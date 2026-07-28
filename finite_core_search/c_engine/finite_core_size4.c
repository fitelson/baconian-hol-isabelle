#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum {
  T_VAR = 0, T_CONST = 1, T_APP = 2, T_LAM = 3, T_EQ = 4,
  T_NEG = 5, T_CONJ = 6, T_DISJ = 7, T_IMP = 8,
  T_FORALL = 9, T_EXISTS = 10
};

enum {
  R_NONE = 0, R_AXIOM, R_TRUE, R_REF, R_CONJ_LEFT, R_CONJ_RIGHT,
  R_DOUBLE_NEG, R_FORALL_ELIM, R_MP, R_CONJ_INTRO,
  R_EQUIVALENCE, R_CONTRADICTION
};

typedef struct {
  uint8_t tag;
  uint8_t pad[3];
  uint32_t a, b;
} TypeRec;

typedef struct {
  uint8_t tag;
  uint8_t pad[3];
  uint32_t a, b, c;
} Node;

typedef struct {
  uint32_t x, y;
} Pair;

typedef struct {
  uint8_t rule;
  uint8_t pad[3];
  uint32_t p1, p2, witness, axiom;
} Proof;

typedef struct {
  uint32_t arg, body, cutoff, result;
} SubstEntry;

static Node *nodes;
static Proof *proofs;
static uint8_t *derived;
static uint32_t *imp_head;
static uint32_t *imp_next;
static uint32_t node_count, node_capacity;
static uint32_t max_nodes;

static uint32_t *term_table;
static uint32_t term_table_capacity, term_table_count;

static SubstEntry *subst_table;
static uint8_t *subst_used;
static uint32_t subst_capacity, subst_count;

static uint32_t *queue;
static uint32_t queue_capacity, queue_length, queue_cursor;

static Pair *witnesses;
static uint32_t witness_count;
static uint32_t *witness_head, *witness_next;
static uint32_t type_count;
static uint32_t prop_type;
static uint32_t false_id;
static clock_t search_start;

static _Noreturn void die(const char *message) {
  fprintf(stderr, "finite_core_size4: %s\n", message);
  exit(2);
}

static void *xcalloc(size_t count, size_t size) {
  void *p = calloc(count, size);
  if (!p) die("out of memory");
  return p;
}

static void *xrealloc(void *old, size_t size) {
  void *p = realloc(old, size);
  if (!p) die("out of memory");
  return p;
}

static uint64_t mix64(uint64_t x) {
  x ^= x >> 30;
  x *= UINT64_C(0xbf58476d1ce4e5b9);
  x ^= x >> 27;
  x *= UINT64_C(0x94d049bb133111eb);
  return x ^ (x >> 31);
}

static uint64_t node_hash(uint8_t tag, uint32_t a, uint32_t b, uint32_t c) {
  uint64_t h = mix64((uint64_t)tag + UINT64_C(0x9e3779b97f4a7c15));
  h ^= mix64(((uint64_t)a << 32) | b);
  h ^= mix64((uint64_t)c + UINT64_C(0x517cc1b727220a95));
  return h;
}

static int node_equal(const Node *n, uint8_t tag,
                      uint32_t a, uint32_t b, uint32_t c) {
  return n->tag == tag && n->a == a && n->b == b && n->c == c;
}

static void ensure_node_capacity(uint32_t wanted) {
  if (wanted <= node_capacity) return;
  uint32_t old = node_capacity;
  uint32_t next = old ? old : 1024;
  while (next < wanted) {
    if (next > UINT32_MAX / 2) die("node capacity overflow");
    next *= 2;
  }
  nodes = xrealloc(nodes, (size_t)next * sizeof(*nodes));
  proofs = xrealloc(proofs, (size_t)next * sizeof(*proofs));
  derived = xrealloc(derived, (size_t)next * sizeof(*derived));
  imp_head = xrealloc(imp_head, (size_t)next * sizeof(*imp_head));
  imp_next = xrealloc(imp_next, (size_t)next * sizeof(*imp_next));
  memset(nodes + old, 0, (size_t)(next - old) * sizeof(*nodes));
  memset(proofs + old, 0, (size_t)(next - old) * sizeof(*proofs));
  memset(derived + old, 0, (size_t)(next - old) * sizeof(*derived));
  for (uint32_t i = old; i < next; ++i) {
    imp_head[i] = UINT32_MAX;
    imp_next[i] = UINT32_MAX;
  }
  node_capacity = next;
}

static void rehash_terms(uint32_t new_capacity) {
  uint32_t *fresh = xcalloc(new_capacity, sizeof(*fresh));
  for (uint32_t id = 0; id < node_count; ++id) {
    Node *n = &nodes[id];
    uint32_t slot = (uint32_t)(node_hash(n->tag, n->a, n->b, n->c)
                               & (new_capacity - 1));
    while (fresh[slot]) slot = (slot + 1) & (new_capacity - 1);
    fresh[slot] = id + 1;
  }
  free(term_table);
  term_table = fresh;
  term_table_capacity = new_capacity;
  term_table_count = node_count;
}

static uint32_t intern_node(uint8_t tag, uint32_t a,
                            uint32_t b, uint32_t c) {
  if (!term_table_capacity) rehash_terms(2048);
  if ((uint64_t)(term_table_count + 1) * 10
      >= (uint64_t)term_table_capacity * 7) {
    rehash_terms(term_table_capacity * 2);
  }
  uint32_t slot = (uint32_t)(node_hash(tag, a, b, c)
                             & (term_table_capacity - 1));
  while (term_table[slot]) {
    uint32_t id = term_table[slot] - 1;
    if (node_equal(&nodes[id], tag, a, b, c)) return id;
    slot = (slot + 1) & (term_table_capacity - 1);
  }
  if (node_count >= max_nodes) {
    double seconds = search_start
        ? (double)(clock() - search_start) / CLOCKS_PER_SEC
        : 0.0;
    printf("{\"status\":\"term_node_cap\",\"derived\":%" PRIu32
           ",\"processed\":%" PRIu32 ",\"term_nodes\":%" PRIu32
           ",\"subst_entries\":%" PRIu32 ",\"seconds\":%.3f}\n",
           queue_length, queue_cursor, node_count, subst_count, seconds);
    exit(3);
  }
  ensure_node_capacity(node_count + 1);
  uint32_t id = node_count++;
  nodes[id].tag = tag;
  nodes[id].a = a;
  nodes[id].b = b;
  nodes[id].c = c;
  term_table[slot] = id + 1;
  term_table_count++;
  return id;
}

static uint64_t subst_hash(uint32_t arg, uint32_t body, uint32_t cutoff) {
  return mix64(((uint64_t)arg << 32) | body)
      ^ mix64((uint64_t)cutoff + UINT64_C(0x6eed0e9da4d94a4f));
}

static void rehash_subst(uint32_t new_capacity) {
  SubstEntry *entries = xcalloc(new_capacity, sizeof(*entries));
  uint8_t *used = xcalloc(new_capacity, sizeof(*used));
  for (uint32_t i = 0; i < subst_capacity; ++i) {
    if (!subst_used[i]) continue;
    SubstEntry e = subst_table[i];
    uint32_t slot = (uint32_t)(subst_hash(e.arg, e.body, e.cutoff)
                               & (new_capacity - 1));
    while (used[slot]) slot = (slot + 1) & (new_capacity - 1);
    used[slot] = 1;
    entries[slot] = e;
  }
  free(subst_table);
  free(subst_used);
  subst_table = entries;
  subst_used = used;
  subst_capacity = new_capacity;
}

static uint32_t substitute(uint32_t arg, uint32_t body, uint32_t cutoff) {
  if (!subst_capacity) rehash_subst(4096);
  if ((uint64_t)(subst_count + 1) * 10
      >= (uint64_t)subst_capacity * 7) {
    rehash_subst(subst_capacity * 2);
  }
  uint32_t slot = (uint32_t)(subst_hash(arg, body, cutoff)
                             & (subst_capacity - 1));
  while (subst_used[slot]) {
    SubstEntry *e = &subst_table[slot];
    if (e->arg == arg && e->body == body && e->cutoff == cutoff)
      return e->result;
    slot = (slot + 1) & (subst_capacity - 1);
  }

  Node n = nodes[body];
  uint32_t result;
  switch (n.tag) {
    case T_VAR:
      if (n.a < cutoff) result = body;
      else if (n.a == cutoff) result = arg;
      else result = intern_node(T_VAR, n.a - 1, 0, 0);
      break;
    case T_CONST:
      result = body;
      break;
    case T_APP:
    case T_CONJ:
    case T_DISJ:
    case T_IMP:
      result = intern_node(
          n.tag,
          substitute(arg, n.a, cutoff),
          substitute(arg, n.b, cutoff),
          0);
      break;
    case T_LAM:
    case T_FORALL:
    case T_EXISTS:
      result = intern_node(
          n.tag, n.a, substitute(arg, n.b, cutoff + 1), 0);
      break;
    case T_EQ:
      result = intern_node(
          T_EQ, n.a,
          substitute(arg, n.b, cutoff),
          substitute(arg, n.c, cutoff));
      break;
    case T_NEG:
      result = intern_node(T_NEG, substitute(arg, n.a, cutoff), 0, 0);
      break;
    default:
      die("bad term tag in substitution");
  }
  subst_used[slot] = 1;
  subst_table[slot].arg = arg;
  subst_table[slot].body = body;
  subst_table[slot].cutoff = cutoff;
  subst_table[slot].result = result;
  subst_count++;
  return result;
}

static void queue_push(uint32_t id) {
  if (queue_length == queue_capacity) {
    queue_capacity = queue_capacity ? queue_capacity * 2 : 4096;
    queue = xrealloc(queue, (size_t)queue_capacity * sizeof(*queue));
  }
  queue[queue_length++] = id;
}

static void derive(uint32_t id, uint8_t rule, uint32_t p1, uint32_t p2,
                   uint32_t witness, uint32_t axiom) {
  ensure_node_capacity(id + 1);
  if (derived[id]) return;
  derived[id] = 1;
  proofs[id].rule = rule;
  proofs[id].p1 = p1;
  proofs[id].p2 = p2;
  proofs[id].witness = witness;
  proofs[id].axiom = axiom;
  queue_push(id);
}

static void write_trace(const char *path) {
  if (!path || !derived[false_id]) return;
  FILE *out = fopen(path, "w");
  if (!out) die("cannot open trace output");
  uint8_t *proof_mark = xcalloc(node_count, 1);
  uint8_t *term_mark = xcalloc(node_count, 1);
  uint32_t *stack = xcalloc(node_count, sizeof(*stack));
  uint32_t top = 0;
  stack[top++] = false_id;
  while (top) {
    uint32_t id = stack[--top];
    if (proof_mark[id]) continue;
    proof_mark[id] = 1;
    Proof p = proofs[id];
    if (p.rule == R_CONJ_LEFT || p.rule == R_CONJ_RIGHT
        || p.rule == R_DOUBLE_NEG || p.rule == R_FORALL_ELIM
        || p.rule == R_EQUIVALENCE) {
      stack[top++] = p.p1;
    } else if (p.rule == R_MP || p.rule == R_CONJ_INTRO
               || p.rule == R_CONTRADICTION) {
      stack[top++] = p.p1;
      stack[top++] = p.p2;
    }
  }
  for (uint32_t id = 0; id < node_count; ++id) {
    if (proof_mark[id]) stack[top++] = id;
    if (proof_mark[id] && proofs[id].rule == R_FORALL_ELIM)
      stack[top++] = proofs[id].witness;
  }
  while (top) {
    uint32_t id = stack[--top];
    if (term_mark[id]) continue;
    term_mark[id] = 1;
    Node n = nodes[id];
    if (n.tag == T_APP || n.tag == T_CONJ || n.tag == T_DISJ
        || n.tag == T_IMP) {
      stack[top++] = n.a;
      stack[top++] = n.b;
    } else if (n.tag == T_LAM || n.tag == T_FORALL
               || n.tag == T_EXISTS) {
      stack[top++] = n.b;
    } else if (n.tag == T_EQ) {
      stack[top++] = n.b;
      stack[top++] = n.c;
    } else if (n.tag == T_NEG) {
      stack[top++] = n.a;
    }
  }
  fprintf(out, "FCSEV_TRACE_1\n");
  for (uint32_t id = 0; id < node_count; ++id) {
    if (!term_mark[id]) continue;
    Node n = nodes[id];
    fprintf(out, "TERM %" PRIu32 " %u %" PRIu32 " %" PRIu32
            " %" PRIu32 "\n", id, n.tag, n.a, n.b, n.c);
  }
  for (uint32_t id = 0; id < node_count; ++id) {
    if (!proof_mark[id]) continue;
    Proof p = proofs[id];
    fprintf(out, "DERIV %" PRIu32 " %u %" PRIu32 " %" PRIu32
            " %" PRIu32 " %" PRIu32 "\n",
            id, p.rule, p.p1, p.p2, p.witness, p.axiom);
  }
  fclose(out);
  free(proof_mark);
  free(term_mark);
  free(stack);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s INPUT.bin [MAX_TERM_NODES] [TRACE]\n", argv[0]);
    return 2;
  }
  max_nodes = argc >= 3 ? (uint32_t)strtoul(argv[2], NULL, 10) : 10000000U;
  const char *trace_path = argc >= 4 ? argv[3] : NULL;
  FILE *in = fopen(argv[1], "rb");
  if (!in) {
    fprintf(stderr, "cannot open %s: %s\n", argv[1], strerror(errno));
    return 2;
  }
  char magic[8];
  uint32_t initial_terms, axiom_count, ref_count, true_id;
  if (fread(magic, 1, 8, in) != 8
      || fread(&type_count, 4, 1, in) != 1
      || fread(&initial_terms, 4, 1, in) != 1
      || fread(&axiom_count, 4, 1, in) != 1
      || fread(&witness_count, 4, 1, in) != 1
      || fread(&ref_count, 4, 1, in) != 1
      || fread(&true_id, 4, 1, in) != 1
      || fread(&false_id, 4, 1, in) != 1) {
    die("short input header");
  }
  if (memcmp(magic, "FCSEV1\0\0", 8) != 0) die("bad input magic");
  TypeRec *types = xcalloc(type_count, sizeof(*types));
  if (fread(types, sizeof(*types), type_count, in) != type_count)
    die("short type table");
  prop_type = UINT32_MAX;
  for (uint32_t i = 0; i < type_count; ++i)
    if (types[i].tag == 1) prop_type = i;
  if (prop_type == UINT32_MAX) die("Prop type missing");

  ensure_node_capacity(initial_terms);
  Node *initial = xcalloc(initial_terms, sizeof(*initial));
  if (fread(initial, sizeof(*initial), initial_terms, in) != initial_terms)
    die("short term table");
  for (uint32_t i = 0; i < initial_terms; ++i) {
    uint32_t id = intern_node(
        initial[i].tag, initial[i].a, initial[i].b, initial[i].c);
    if (id != i) die("input term table is not uniquely topological");
  }
  free(initial);
  Pair *axioms = xcalloc(axiom_count, sizeof(*axioms));
  witnesses = xcalloc(witness_count, sizeof(*witnesses));
  if (fread(axioms, sizeof(*axioms), axiom_count, in) != axiom_count)
    die("short axiom table");
  if (fread(witnesses, sizeof(*witnesses), witness_count, in)
      != witness_count) die("short witness table");
  fclose(in);

  witness_head = xcalloc(type_count, sizeof(*witness_head));
  witness_next = xcalloc(witness_count, sizeof(*witness_next));
  for (uint32_t i = 0; i < type_count; ++i) witness_head[i] = UINT32_MAX;
  for (uint32_t i = witness_count; i-- > 0;) {
    uint32_t ty = witnesses[i].y;
    witness_next[i] = witness_head[ty];
    witness_head[ty] = i;
  }

  search_start = clock();
  for (uint32_t i = 0; i < axiom_count; ++i)
    derive(axioms[i].x, R_AXIOM, 0, 0, 0, axioms[i].y);
  derive(true_id, R_TRUE, 0, 0, 0, 0);
  for (uint32_t i = 0; i < ref_count; ++i) {
    uint32_t ref = intern_node(
        T_EQ, witnesses[i].y, witnesses[i].x, witnesses[i].x);
    derive(ref, R_REF, 0, 0, witnesses[i].x, 0);
  }

  while (queue_cursor < queue_length && !derived[false_id]) {
    uint32_t id = queue[queue_cursor++];
    Node n = nodes[id];
    if (n.tag == T_CONJ) {
      derive(n.a, R_CONJ_LEFT, id, 0, 0, 0);
      derive(n.b, R_CONJ_RIGHT, id, 0, 0, 0);
      Node l = nodes[n.a], r = nodes[n.b];
      if (l.tag == T_IMP && r.tag == T_IMP
          && l.a == r.b && l.b == r.a) {
        uint32_t eq = intern_node(T_EQ, prop_type, l.a, l.b);
        derive(eq, R_EQUIVALENCE, id, 0, 0, 0);
      }
    }
    if (n.tag == T_NEG) {
      if (nodes[n.a].tag == T_NEG)
        derive(nodes[n.a].a, R_DOUBLE_NEG, id, 0, 0, 0);
      if (derived[n.a])
        derive(false_id, R_CONTRADICTION, n.a, id, 0, 0);
    }
    if (n.tag == T_FORALL) {
      for (uint32_t wi = witness_head[n.a]; wi != UINT32_MAX;
           wi = witness_next[wi]) {
        uint32_t instance = substitute(witnesses[wi].x, n.b, 0);
        derive(instance, R_FORALL_ELIM, id, 0, witnesses[wi].x, 0);
      }
    }
    if (n.tag == T_IMP) {
      imp_next[id] = imp_head[n.a];
      imp_head[n.a] = id;
      if (derived[n.a]) derive(n.b, R_MP, id, n.a, 0, 0);
      uint32_t converse = intern_node(T_IMP, n.b, n.a, 0);
      if (derived[converse]) {
        uint32_t conjunction = intern_node(T_CONJ, id, converse, 0);
        derive(conjunction, R_CONJ_INTRO, id, converse, 0, 0);
      }
    }
    for (uint32_t imp = imp_head[id]; imp != UINT32_MAX;
         imp = imp_next[imp]) {
      derive(nodes[imp].b, R_MP, imp, id, 0, 0);
    }
    uint32_t negated = intern_node(T_NEG, id, 0, 0);
    if (derived[negated])
      derive(false_id, R_CONTRADICTION, id, negated, 0, 0);
  }

  double seconds = (double)(clock() - search_start) / CLOCKS_PER_SEC;
  printf("{\"status\":\"%s\",\"derived\":%" PRIu32
         ",\"term_nodes\":%" PRIu32 ",\"subst_entries\":%" PRIu32
         ",\"seconds\":%.3f}\n",
         derived[false_id] ? "candidate_refutation" : "fixed_point_no_refutation",
         queue_length, node_count, subst_count, seconds);
  write_trace(trace_path);

  free(types);
  free(axioms);
  free(witnesses);
  free(witness_head);
  free(witness_next);
  free(nodes);
  free(proofs);
  free(derived);
  free(imp_head);
  free(imp_next);
  free(term_table);
  free(subst_table);
  free(subst_used);
  free(queue);
  return 0;
}
