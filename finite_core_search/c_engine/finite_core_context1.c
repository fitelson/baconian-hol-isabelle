#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/*
 * Context-depth-one forward saturator for the FCSEV2 format.
 *
 * The input emitter is responsible for supplying sound seed judgments,
 * typing facts, and targeted existential-generalization edges.  In
 * particular, beta, eta, propositional-calculus, Boolean, and Classicist
 * instances are seeds rather than rules reconstructed here.
 *
 * This executable intentionally does not emit proof traces.  Therefore a
 * candidate_refutation is never, by itself, an inconsistent core: its
 * derivation must be reconstructed and replayed in Isabelle.
 */

enum {
  T_VAR = 0, T_CONST = 1, T_APP = 2, T_LAM = 3, T_EQ = 4,
  T_NEG = 5, T_CONJ = 6, T_DISJ = 7, T_IMP = 8,
  T_FORALL = 9, T_EXISTS = 10
};

enum {
  TY_IND = 0, TY_PROP = 1, TY_ARR = 2
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
  uint32_t ctx, term, kind, axiom;
} SeedRec;

typedef struct {
  uint32_t ctx, term, type;
} TypedRec;

typedef struct {
  uint32_t ctx, premise, conclusion;
} EgEdge;

_Static_assert(sizeof(TypeRec) == 12, "FCSEV2 TypeRec layout mismatch");
_Static_assert(sizeof(Node) == 16, "FCSEV2 Node layout mismatch");
_Static_assert(sizeof(SeedRec) == 16, "FCSEV2 SeedRec layout mismatch");
_Static_assert(sizeof(TypedRec) == 12, "FCSEV2 TypedRec layout mismatch");
_Static_assert(sizeof(EgEdge) == 12, "FCSEV2 EgEdge layout mismatch");

typedef struct {
  uint32_t ctx, term;
} Judgment;

typedef struct {
  uint64_t key;
  uint32_t value;
  uint32_t next;
} IndexEntry;

typedef struct {
  uint32_t *buckets;
  uint32_t bucket_count;
  IndexEntry *entries;
  uint32_t count;
  uint32_t capacity;
} Index;

typedef struct {
  uint64_t *slots;
  uint32_t capacity;
  uint32_t count;
} JudgmentSet;

typedef struct {
  uint32_t arg, body, cutoff, result;
} SubstEntry;

static TypeRec *types;
static Node *nodes;
static uint32_t type_count;
static uint32_t node_count;
static uint32_t node_capacity;
static uint32_t max_nodes;
static uint32_t context_count;
static uint32_t *context_binders;
static uint32_t prop_type;
static uint32_t true_id;
static uint32_t false_id;

static uint32_t *term_table;
static uint64_t term_table_capacity;
static uint32_t term_table_count;

static SubstEntry *subst_table;
static uint8_t *subst_used;
static uint32_t subst_capacity;
static uint32_t subst_count;
static uint64_t subst_insertions;
static uint32_t subst_cache_resets;

/*
 * Substitution memoization is an optimization, not part of the calculus.
 * Letting this open-addressed table double without bound makes the size-5
 * search exhaust the 32-bit table index before it exhausts the term-node
 * bound.  At the maximum capacity, discard the cache and begin again.  This
 * can cause recomputation, but it cannot add or remove any derivable term.
 */
#define SUBST_CACHE_MAX_CAPACITY (UINT32_C(1) << 28)

static JudgmentSet derived;
static Judgment *queue;
static uint32_t queue_capacity;
static uint32_t queue_length;
static uint32_t queue_cursor;

/* All indexes contain only positive, finite input or derived facts. */
static Index typed_by_term;       /* (ctx, term) -> type */
static Index witnesses_by_type;   /* (ctx, type) -> term */
static Index eg_by_premise;       /* (ctx, premise) -> conclusion */
static Index implications_by_lhs; /* (ctx, antecedent) -> implication */
static Index negations_by_body;   /* (ctx, body) -> negation */
static Index equalities_by_lhs;   /* (ctx, lhs) -> equality */
static Index applications_by_arg; /* (ctx, argument) -> application */

static clock_t search_start;
static const char *trace_request;

static _Noreturn void die(const char *message) {
  fprintf(stderr, "finite_core_context1: %s\n", message);
  exit(2);
}

static void *xcalloc(size_t count, size_t size) {
  if (size && count > SIZE_MAX / size) die("allocation size overflow");
  void *p = calloc(count, size);
  if (!p) die("out of memory");
  return p;
}

static void *xrealloc(void *old, size_t count, size_t size) {
  if (size && count > SIZE_MAX / size) die("allocation size overflow");
  void *p = realloc(old, count * size);
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

static uint64_t pair_key(uint32_t x, uint32_t y) {
  return ((uint64_t)x << 32) | y;
}

static uint64_t node_hash(uint8_t tag, uint32_t a,
                          uint32_t b, uint32_t c) {
  uint64_t h = mix64((uint64_t)tag + UINT64_C(0x9e3779b97f4a7c15));
  h ^= mix64(((uint64_t)a << 32) | b);
  h ^= mix64((uint64_t)c + UINT64_C(0x517cc1b727220a95));
  return h;
}

static bool node_equal(const Node *n, uint8_t tag,
                       uint32_t a, uint32_t b, uint32_t c) {
  return n->tag == tag && n->a == a && n->b == b && n->c == c;
}

static void print_cap_status(void) {
  double seconds = search_start
      ? (double)(clock() - search_start) / CLOCKS_PER_SEC
      : 0.0;
  printf("{\"status\":\"term_node_cap\","
         "\"derived_judgments\":%" PRIu32 ","
         "\"processed_judgments\":%" PRIu32 ","
         "\"term_nodes\":%" PRIu32 ","
         "\"subst_entries\":%" PRIu64 ","
         "\"subst_cache_entries\":%" PRIu32 ","
         "\"subst_cache_resets\":%" PRIu32 ","
         "\"seconds\":%.3f,"
         "\"candidate_trace_supported\":false,"
         "\"isabelle_replay_required\":true}\n",
         queue_length, queue_cursor, node_count, subst_insertions,
         subst_count, subst_cache_resets, seconds);
}

static void ensure_node_capacity(uint32_t wanted) {
  if (wanted <= node_capacity) return;
  uint32_t old = node_capacity;
  uint64_t next = old ? old : 1024;
  while (next < wanted) {
    next *= 2;
    if (next > max_nodes) {
      next = max_nodes;
      break;
    }
    if (next > UINT32_MAX) die("node capacity overflow");
  }
  if (next > max_nodes) next = max_nodes;
  if (next < wanted) {
    print_cap_status();
    exit(3);
  }
  nodes = xrealloc(nodes, (size_t)next, sizeof(*nodes));
  memset(nodes + old, 0, (size_t)(next - old) * sizeof(*nodes));
  node_capacity = (uint32_t)next;
}

static void rehash_terms(uint64_t new_capacity) {
  uint32_t *fresh = xcalloc(new_capacity, sizeof(*fresh));
  for (uint32_t id = 0; id < node_count; ++id) {
    Node *n = &nodes[id];
    uint64_t slot = node_hash(n->tag, n->a, n->b, n->c)
        & (new_capacity - 1);
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
      >= term_table_capacity * 7) {
    if (term_table_capacity >= (UINT64_C(1) << 32))
      die("term hash capacity overflow");
    rehash_terms(term_table_capacity * 2);
  }
  uint64_t slot = node_hash(tag, a, b, c) & (term_table_capacity - 1);
  while (term_table[slot]) {
    uint32_t id = term_table[slot] - 1;
    if (node_equal(&nodes[id], tag, a, b, c)) return id;
    slot = (slot + 1) & (term_table_capacity - 1);
  }
  if (node_count >= max_nodes) {
    print_cap_status();
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

static void index_rehash(Index *index, uint32_t new_bucket_count) {
  uint32_t *fresh = xcalloc(new_bucket_count, sizeof(*fresh));
  for (uint32_t i = 0; i < index->count; ++i) {
    uint32_t bucket = (uint32_t)(
        mix64(index->entries[i].key) & (new_bucket_count - 1));
    index->entries[i].next = fresh[bucket];
    fresh[bucket] = i + 1;
  }
  free(index->buckets);
  index->buckets = fresh;
  index->bucket_count = new_bucket_count;
}

static void index_add(Index *index, uint64_t key, uint32_t value) {
  if (!index->bucket_count) index_rehash(index, 1024);
  if (index->count >= index->capacity) {
    uint32_t next = index->capacity ? index->capacity * 2 : 1024;
    if (next < index->capacity) die("index capacity overflow");
    index->entries = xrealloc(index->entries, next, sizeof(*index->entries));
    index->capacity = next;
  }
  if ((uint64_t)(index->count + 1) * 2 > index->bucket_count) {
    if (index->bucket_count > UINT32_MAX / 2)
      die("index bucket overflow");
    index_rehash(index, index->bucket_count * 2);
  }
  uint32_t bucket = (uint32_t)(
      mix64(key) & (index->bucket_count - 1));
  uint32_t entry = index->count++;
  index->entries[entry].key = key;
  index->entries[entry].value = value;
  index->entries[entry].next = index->buckets[bucket];
  index->buckets[bucket] = entry + 1;
}

static uint32_t index_first(const Index *index, uint64_t key) {
  if (!index->bucket_count) return UINT32_MAX;
  uint32_t bucket = (uint32_t)(
      mix64(key) & (index->bucket_count - 1));
  uint32_t link = index->buckets[bucket];
  while (link) {
    uint32_t entry = link - 1;
    if (index->entries[entry].key == key) return entry;
    link = index->entries[entry].next;
  }
  return UINT32_MAX;
}

static uint32_t index_next(const Index *index, uint32_t entry,
                           uint64_t key) {
  uint32_t link = index->entries[entry].next;
  while (link) {
    uint32_t next = link - 1;
    if (index->entries[next].key == key) return next;
    link = index->entries[next].next;
  }
  return UINT32_MAX;
}

static bool typed_has(uint32_t ctx, uint32_t term, uint32_t type) {
  uint64_t key = pair_key(ctx, term);
  for (uint32_t e = index_first(&typed_by_term, key);
       e != UINT32_MAX; e = index_next(&typed_by_term, e, key)) {
    if (typed_by_term.entries[e].value == type) return true;
  }
  return false;
}

static void judgment_set_rehash(JudgmentSet *set, uint32_t new_capacity) {
  uint64_t *fresh = xcalloc(new_capacity, sizeof(*fresh));
  for (uint32_t i = 0; i < set->capacity; ++i) {
    if (!set->slots[i]) continue;
    uint64_t encoded = set->slots[i];
    uint64_t key = encoded - 1;
    uint32_t slot = (uint32_t)(mix64(key) & (new_capacity - 1));
    while (fresh[slot]) slot = (slot + 1) & (new_capacity - 1);
    fresh[slot] = encoded;
  }
  free(set->slots);
  set->slots = fresh;
  set->capacity = new_capacity;
}

static bool judgment_set_contains(const JudgmentSet *set,
                                  uint32_t ctx, uint32_t term) {
  if (!set->capacity) return false;
  uint64_t key = pair_key(ctx, term);
  uint64_t encoded = key + 1;
  uint32_t slot = (uint32_t)(mix64(key) & (set->capacity - 1));
  while (set->slots[slot]) {
    if (set->slots[slot] == encoded) return true;
    slot = (slot + 1) & (set->capacity - 1);
  }
  return false;
}

static bool judgment_set_add(JudgmentSet *set,
                             uint32_t ctx, uint32_t term) {
  if (!set->capacity) judgment_set_rehash(set, 4096);
  if ((uint64_t)(set->count + 1) * 10
      >= (uint64_t)set->capacity * 7) {
    if (set->capacity > UINT32_MAX / 2)
      die("judgment set capacity overflow");
    judgment_set_rehash(set, set->capacity * 2);
  }
  uint64_t key = pair_key(ctx, term);
  uint64_t encoded = key + 1;
  uint32_t slot = (uint32_t)(mix64(key) & (set->capacity - 1));
  while (set->slots[slot]) {
    if (set->slots[slot] == encoded) return false;
    slot = (slot + 1) & (set->capacity - 1);
  }
  set->slots[slot] = encoded;
  set->count++;
  return true;
}

static void queue_push(uint32_t ctx, uint32_t term) {
  if (queue_length == queue_capacity) {
    uint32_t next = queue_capacity ? queue_capacity * 2 : 4096;
    if (next < queue_capacity) die("queue capacity overflow");
    queue = xrealloc(queue, next, sizeof(*queue));
    queue_capacity = next;
  }
  queue[queue_length].ctx = ctx;
  queue[queue_length].term = term;
  queue_length++;
}

static void derive(uint32_t ctx, uint32_t term) {
  if (ctx >= context_count || term >= node_count)
    die("internal invalid judgment");
  if (judgment_set_add(&derived, ctx, term)) queue_push(ctx, term);
}

static bool is_derived(uint32_t ctx, uint32_t term) {
  return judgment_set_contains(&derived, ctx, term);
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

/*
 * Raise every free variable by amount.  The cutoff increases beneath
 * object-language binders, exactly as in Bacon_Substitution.rename.
 */
static uint32_t shift_by(uint32_t term, uint32_t amount, uint32_t cutoff) {
  Node n = nodes[term];
  switch (n.tag) {
    case T_VAR:
      if (n.a < cutoff) return term;
      if (n.a > UINT32_MAX - amount) die("variable index overflow");
      return intern_node(T_VAR, n.a + amount, 0, 0);
    case T_CONST:
      return term;
    case T_APP:
    case T_CONJ:
    case T_DISJ:
    case T_IMP:
      return intern_node(n.tag,
                         shift_by(n.a, amount, cutoff),
                         shift_by(n.b, amount, cutoff), 0);
    case T_LAM:
    case T_FORALL:
    case T_EXISTS:
      if (cutoff == UINT32_MAX) die("binder depth overflow");
      return intern_node(n.tag, n.a,
                         shift_by(n.b, amount, cutoff + 1), 0);
    case T_EQ:
      return intern_node(T_EQ, n.a,
                         shift_by(n.b, amount, cutoff),
                         shift_by(n.c, amount, cutoff));
    case T_NEG:
      return intern_node(T_NEG, shift_by(n.a, amount, cutoff), 0, 0);
    default:
      die("bad term tag in shift");
  }
}

/*
 * subst0(argument, body), with a cutoff form for descent under binders.
 * Unlike the old closed-term engine, this raises an open argument when it
 * crosses a binder.
 */
static uint32_t substitute(uint32_t arg, uint32_t body, uint32_t cutoff) {
  if (!subst_capacity) rehash_subst(4096);
  if ((uint64_t)(subst_count + 1) * 10
      >= (uint64_t)subst_capacity * 7) {
    if (subst_capacity >= SUBST_CACHE_MAX_CAPACITY) {
      memset(subst_used, 0, subst_capacity * sizeof(*subst_used));
      subst_count = 0;
      subst_cache_resets++;
    } else {
      uint32_t next = subst_capacity * 2;
      if (next > SUBST_CACHE_MAX_CAPACITY)
        next = SUBST_CACHE_MAX_CAPACITY;
      rehash_subst(next);
    }
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
      else if (n.a == cutoff) result = shift_by(arg, cutoff, 0);
      else result = intern_node(T_VAR, n.a - 1, 0, 0);
      break;
    case T_CONST:
      result = body;
      break;
    case T_APP:
    case T_CONJ:
    case T_DISJ:
    case T_IMP:
      result = intern_node(n.tag,
                           substitute(arg, n.a, cutoff),
                           substitute(arg, n.b, cutoff), 0);
      break;
    case T_LAM:
    case T_FORALL:
    case T_EXISTS:
      if (cutoff == UINT32_MAX) die("binder depth overflow");
      result = intern_node(n.tag, n.a,
                           substitute(arg, n.b, cutoff + 1), 0);
      break;
    case T_EQ:
      result = intern_node(T_EQ, n.a,
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
  subst_insertions++;
  return result;
}

/*
 * Partial inverse of shift at a binder-sensitive cutoff.  Failure means
 * that the distinguished newly bound variable occurs free.
 */
static bool unshift(uint32_t term, uint32_t cutoff, uint32_t *result) {
  Node n = nodes[term];
  uint32_t left, right;
  switch (n.tag) {
    case T_VAR:
      if (n.a < cutoff) {
        *result = term;
        return true;
      }
      if (n.a == cutoff) return false;
      *result = intern_node(T_VAR, n.a - 1, 0, 0);
      return true;
    case T_CONST:
      *result = term;
      return true;
    case T_APP:
    case T_CONJ:
    case T_DISJ:
    case T_IMP:
      if (!unshift(n.a, cutoff, &left)
          || !unshift(n.b, cutoff, &right)) return false;
      *result = intern_node(n.tag, left, right, 0);
      return true;
    case T_LAM:
    case T_FORALL:
    case T_EXISTS:
      if (cutoff == UINT32_MAX) die("binder depth overflow");
      if (!unshift(n.b, cutoff + 1, &right)) return false;
      *result = intern_node(n.tag, n.a, right, 0);
      return true;
    case T_EQ:
      if (!unshift(n.b, cutoff, &left)
          || !unshift(n.c, cutoff, &right)) return false;
      *result = intern_node(T_EQ, n.a, left, right);
      return true;
    case T_NEG:
      if (!unshift(n.a, cutoff, &left)) return false;
      *result = intern_node(T_NEG, left, 0, 0);
      return true;
    default:
      die("bad term tag in unshift");
  }
}

static uint32_t find_arrow_type(uint32_t domain, uint32_t codomain) {
  for (uint32_t i = 0; i < type_count; ++i) {
    if (types[i].tag == TY_ARR
        && types[i].a == domain && types[i].b == codomain)
      return i;
  }
  return UINT32_MAX;
}

static void apply_leibniz_from_equality(uint32_t ctx, uint32_t eq_id) {
  Node eq = nodes[eq_id];
  if (eq.tag != T_EQ) return;
  if (!typed_has(ctx, eq.b, eq.a) || !typed_has(ctx, eq.c, eq.a))
    return;
  uint32_t predicate_type = find_arrow_type(eq.a, prop_type);
  if (predicate_type == UINT32_MAX) return;
  uint64_t key = pair_key(ctx, eq.b);
  for (uint32_t e = index_first(&applications_by_arg, key);
       e != UINT32_MAX; e = index_next(&applications_by_arg, e, key)) {
    uint32_t app_id = applications_by_arg.entries[e].value;
    Node app = nodes[app_id];
    if (app.tag != T_APP || !typed_has(ctx, app.a, predicate_type))
      continue;
    derive(ctx, intern_node(T_APP, app.a, eq.c, 0));
  }
}

static void apply_leibniz_from_application(uint32_t ctx, uint32_t app_id) {
  Node app = nodes[app_id];
  if (app.tag != T_APP) return;
  uint64_t key = pair_key(ctx, app.b);
  for (uint32_t e = index_first(&equalities_by_lhs, key);
       e != UINT32_MAX; e = index_next(&equalities_by_lhs, e, key)) {
    uint32_t eq_id = equalities_by_lhs.entries[e].value;
    Node eq = nodes[eq_id];
    if (eq.tag != T_EQ
        || !typed_has(ctx, eq.b, eq.a)
        || !typed_has(ctx, eq.c, eq.a)) continue;
    uint32_t predicate_type = find_arrow_type(eq.a, prop_type);
    if (predicate_type == UINT32_MAX
        || !typed_has(ctx, app.a, predicate_type)) continue;
    derive(ctx, intern_node(T_APP, app.a, eq.c, 0));
  }
}

static void apply_context_rules(uint32_t ctx, uint32_t id) {
  if (ctx == 0 || context_binders[ctx] == UINT32_MAX) return;
  uint32_t binder = context_binders[ctx];
  Node n = nodes[id];

  if (n.tag == T_IMP) {
    uint32_t unshifted;

    /* CEV+ Generalization. */
    if (unshift(n.a, 0, &unshifted)
        && typed_has(0, unshifted, prop_type)
        && typed_has(ctx, n.b, prop_type)) {
      uint32_t quantified = intern_node(T_FORALL, binder, n.b, 0);
      derive(0, intern_node(T_IMP, unshifted, quantified, 0));
    }

    /* CEV+ Instantiation. */
    if (unshift(n.b, 0, &unshifted)
        && typed_has(ctx, n.a, prop_type)
        && typed_has(0, unshifted, prop_type)) {
      uint32_t existential = intern_node(T_EXISTS, binder, n.a, 0);
      derive(0, intern_node(T_IMP, existential, unshifted, 0));
    }
  }

  /*
   * Unary VectorEquivalence:
   *   (shift F $ 0 <-> shift G $ 0)  in [binder]
   * yields Eq (binder -> Prop) F G in [].
   */
  if (n.tag == T_CONJ) {
    Node forward = nodes[n.a];
    Node backward = nodes[n.b];
    if (forward.tag == T_IMP && backward.tag == T_IMP
        && forward.a == backward.b && forward.b == backward.a) {
      Node fa = nodes[forward.a];
      Node ga = nodes[forward.b];
      if (fa.tag == T_APP && ga.tag == T_APP
          && nodes[fa.b].tag == T_VAR && nodes[fa.b].a == 0
          && nodes[ga.b].tag == T_VAR && nodes[ga.b].a == 0) {
        uint32_t f, g;
        uint32_t predicate_type = find_arrow_type(binder, prop_type);
        if (predicate_type != UINT32_MAX
            && unshift(fa.a, 0, &f) && unshift(ga.a, 0, &g)
            && typed_has(0, f, predicate_type)
            && typed_has(0, g, predicate_type)) {
          derive(0, intern_node(T_EQ, predicate_type, f, g));
        }
      }
    }
  }
}

static void process_judgment(uint32_t ctx, uint32_t id) {
  Node n = nodes[id];

  /* Precomputed, targeted existential-generalization instances. */
  uint64_t judgment_key = pair_key(ctx, id);
  for (uint32_t e = index_first(&eg_by_premise, judgment_key);
       e != UINT32_MAX; e = index_next(&eg_by_premise, e, judgment_key)) {
    derive(ctx, eg_by_premise.entries[e].value);
  }

  apply_context_rules(ctx, id);

  if (n.tag == T_CONJ) {
    derive(ctx, n.a);
    derive(ctx, n.b);

    Node left = nodes[n.a];
    Node right = nodes[n.b];
    if (left.tag == T_IMP && right.tag == T_IMP
        && left.a == right.b && left.b == right.a) {
      derive(ctx, intern_node(T_EQ, prop_type, left.a, left.b));
    }
  }

  if (n.tag == T_NEG) {
    index_add(&negations_by_body, pair_key(ctx, n.a), id);
    if (is_derived(ctx, n.a)) derive(ctx, false_id);
  }
  for (uint32_t e = index_first(&negations_by_body, judgment_key);
       e != UINT32_MAX; e = index_next(&negations_by_body, e, judgment_key)) {
    derive(ctx, false_id);
  }

  if (n.tag == T_NEG && nodes[n.a].tag == T_NEG)
    derive(ctx, nodes[n.a].a);

  if (n.tag == T_FORALL) {
    uint64_t witness_key = pair_key(ctx, n.a);
    for (uint32_t e = index_first(&witnesses_by_type, witness_key);
         e != UINT32_MAX;
         e = index_next(&witnesses_by_type, e, witness_key)) {
      derive(ctx, substitute(witnesses_by_type.entries[e].value, n.b, 0));
    }
  }

  if (n.tag == T_IMP) {
    uint64_t antecedent_key = pair_key(ctx, n.a);
    index_add(&implications_by_lhs, antecedent_key, id);
    if (is_derived(ctx, n.a)) derive(ctx, n.b);

    /*
     * Conjunction introduction is the exact zeroary-equivalence premise
     * constructor: from A->B and B->A, derive their conjunction.
     */
    uint64_t converse_key = pair_key(ctx, n.b);
    for (uint32_t e = index_first(&implications_by_lhs, converse_key);
         e != UINT32_MAX;
         e = index_next(&implications_by_lhs, e, converse_key)) {
      uint32_t converse = implications_by_lhs.entries[e].value;
      if (nodes[converse].tag == T_IMP && nodes[converse].b == n.a)
        derive(ctx, intern_node(T_CONJ, id, converse, 0));
    }
  }
  for (uint32_t e = index_first(&implications_by_lhs, judgment_key);
       e != UINT32_MAX;
       e = index_next(&implications_by_lhs, e, judgment_key)) {
    uint32_t implication = implications_by_lhs.entries[e].value;
    derive(ctx, nodes[implication].b);
  }

  if (n.tag == T_EQ) {
    index_add(&equalities_by_lhs, pair_key(ctx, n.b), id);
    apply_leibniz_from_equality(ctx, id);
  }

  if (n.tag == T_APP) {
    index_add(&applications_by_arg, pair_key(ctx, n.b), id);
    apply_leibniz_from_application(ctx, id);
  }
}

static void validate_type_table(void) {
  if (prop_type >= type_count || types[prop_type].tag != TY_PROP)
    die("invalid Prop type id");
  for (uint32_t i = 0; i < type_count; ++i) {
    if (types[i].tag > TY_ARR) die("bad type tag");
    if (types[i].tag == TY_ARR
        && (types[i].a >= type_count || types[i].b >= type_count))
      die("bad arrow type reference");
  }
}

static void validate_node(uint32_t id, const Node *n) {
  switch (n->tag) {
    case T_VAR:
      return;
    case T_CONST:
      if (n->b >= type_count) die("bad constant type reference");
      return;
    case T_APP:
    case T_CONJ:
    case T_DISJ:
    case T_IMP:
      if (n->a >= id || n->b >= id) die("non-topological term table");
      return;
    case T_LAM:
    case T_FORALL:
    case T_EXISTS:
      if (n->a >= type_count || n->b >= id)
        die("bad binder term record");
      return;
    case T_EQ:
      if (n->a >= type_count || n->b >= id || n->c >= id)
        die("bad equality term record");
      return;
    case T_NEG:
      if (n->a >= id) die("non-topological negation term record");
      return;
    default:
      die("bad term tag");
  }
}

static void free_index(Index *index) {
  free(index->buckets);
  free(index->entries);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr,
            "usage: %s INPUT.bin [MAX_TERM_NODES] [TRACE_UNSUPPORTED]\n",
            argv[0]);
    return 2;
  }
  max_nodes = argc >= 3
      ? (uint32_t)strtoul(argv[2], NULL, 10) : 10000000U;
  if (!max_nodes) die("MAX_TERM_NODES must be positive");
  trace_request = argc >= 4 ? argv[3] : NULL;

  FILE *in = fopen(argv[1], "rb");
  if (!in) {
    fprintf(stderr, "cannot open %s: %s\n", argv[1], strerror(errno));
    return 2;
  }

  char magic[8];
  uint32_t initial_terms, seed_count, typed_count, eg_edge_count;
  if (fread(magic, 1, 8, in) != 8
      || fread(&type_count, 4, 1, in) != 1
      || fread(&initial_terms, 4, 1, in) != 1
      || fread(&context_count, 4, 1, in) != 1
      || fread(&seed_count, 4, 1, in) != 1
      || fread(&typed_count, 4, 1, in) != 1
      || fread(&eg_edge_count, 4, 1, in) != 1
      || fread(&true_id, 4, 1, in) != 1
      || fread(&false_id, 4, 1, in) != 1
      || fread(&prop_type, 4, 1, in) != 1) {
    die("short input header");
  }
  if (memcmp(magic, "FCSEV2\0\0", 8) != 0) die("bad input magic");
  if (!type_count || !initial_terms || !context_count)
    die("empty required input table");
  if (initial_terms > max_nodes) die("initial term table exceeds node cap");

  types = xcalloc(type_count, sizeof(*types));
  if (fread(types, sizeof(*types), type_count, in) != type_count)
    die("short type table");
  validate_type_table();

  ensure_node_capacity(initial_terms);
  Node *initial = xcalloc(initial_terms, sizeof(*initial));
  if (fread(initial, sizeof(*initial), initial_terms, in) != initial_terms)
    die("short term table");
  for (uint32_t i = 0; i < initial_terms; ++i) {
    validate_node(i, &initial[i]);
    uint32_t id = intern_node(initial[i].tag, initial[i].a,
                              initial[i].b, initial[i].c);
    if (id != i) die("input term table is not uniquely topological");
  }
  free(initial);
  if (true_id >= node_count || false_id >= node_count)
    die("bad truth or falsity term id");

  context_binders = xcalloc(context_count, sizeof(*context_binders));
  if (fread(context_binders, sizeof(*context_binders), context_count, in)
      != context_count) die("short context table");
  if (context_binders[0] != UINT32_MAX)
    die("context zero must be empty");
  for (uint32_t ctx = 1; ctx < context_count; ++ctx) {
    if (context_binders[ctx] >= type_count)
      die("singleton context has invalid binder type");
  }

  SeedRec *seeds = xcalloc(seed_count, sizeof(*seeds));
  TypedRec *typed = xcalloc(typed_count, sizeof(*typed));
  EgEdge *edges = xcalloc(eg_edge_count, sizeof(*edges));
  if (fread(seeds, sizeof(*seeds), seed_count, in) != seed_count)
    die("short seed table");
  if (fread(typed, sizeof(*typed), typed_count, in) != typed_count)
    die("short typing table");
  if (fread(edges, sizeof(*edges), eg_edge_count, in) != eg_edge_count)
    die("short EG edge table");
  if (fgetc(in) != EOF) die("trailing bytes after FCSEV2 tables");
  fclose(in);

  for (uint32_t i = 0; i < seed_count; ++i) {
    if (seeds[i].ctx >= context_count || seeds[i].term >= initial_terms)
      die("invalid seed record");
  }
  for (uint32_t i = 0; i < typed_count; ++i) {
    TypedRec r = typed[i];
    if (r.ctx >= context_count || r.term >= node_count
        || r.type >= type_count) die("invalid typing record");
    index_add(&typed_by_term, pair_key(r.ctx, r.term), r.type);
    index_add(&witnesses_by_type, pair_key(r.ctx, r.type), r.term);
  }
  for (uint32_t i = 0; i < eg_edge_count; ++i) {
    EgEdge r = edges[i];
    if (r.ctx >= context_count || r.premise >= node_count
        || r.conclusion >= node_count) die("invalid EG edge");
    index_add(&eg_by_premise, pair_key(r.ctx, r.premise), r.conclusion);
  }

  search_start = clock();

  /* ObjTrue and typed reflexivity are CEV base derivations in every context. */
  for (uint32_t ctx = 0; ctx < context_count; ++ctx) derive(ctx, true_id);
  for (uint32_t i = 0; i < typed_count; ++i) {
    TypedRec r = typed[i];
    derive(r.ctx, intern_node(T_EQ, r.type, r.term, r.term));
  }
  for (uint32_t i = 0; i < seed_count; ++i) {
    SeedRec r = seeds[i];
    /*
     * kind and axiom are emitter/replay metadata.  Every record is a positive
     * seed judgment for this trace-free fixed-point engine.
     */
    (void)r.kind;
    (void)r.axiom;
    derive(r.ctx, r.term);
  }

  while (queue_cursor < queue_length
         && !is_derived(0, false_id)) {
    Judgment judgment = queue[queue_cursor++];
    process_judgment(judgment.ctx, judgment.term);
  }

  bool candidate = is_derived(0, false_id);
  double seconds = (double)(clock() - search_start) / CLOCKS_PER_SEC;
  if (candidate) {
    fprintf(stderr,
            "finite_core_context1: candidate only; proof trace unsupported, "
            "so Isabelle replay is still required\n");
  }
  printf("{\"status\":\"%s\","
         "\"derived_judgments\":%" PRIu32 ","
         "\"processed_judgments\":%" PRIu32 ","
         "\"term_nodes\":%" PRIu32 ","
         "\"subst_entries\":%" PRIu64 ","
         "\"subst_cache_entries\":%" PRIu32 ","
         "\"subst_cache_resets\":%" PRIu32 ","
         "\"contexts\":%" PRIu32 ","
         "\"seconds\":%.3f,"
         "\"candidate_trace_supported\":false,"
         "\"trace_request\":\"%s\","
         "\"isabelle_replay_required\":true,"
         "\"candidate_is_inconsistent_core\":false}\n",
         candidate ? "candidate_refutation" : "fixed_point_no_refutation",
         queue_length, queue_cursor, node_count, subst_insertions,
         subst_count, subst_cache_resets,
         context_count, seconds,
         trace_request ? "ignored_unsupported" : "not_requested");

  free(types);
  free(nodes);
  free(context_binders);
  free(seeds);
  free(typed);
  free(edges);
  free(term_table);
  free(subst_table);
  free(subst_used);
  free(derived.slots);
  free(queue);
  free_index(&typed_by_term);
  free_index(&witnesses_by_type);
  free_index(&eg_by_premise);
  free_index(&implications_by_lhs);
  free_index(&negations_by_body);
  free_index(&equalities_by_lhs);
  free_index(&applications_by_arg);
  return 0;
}
