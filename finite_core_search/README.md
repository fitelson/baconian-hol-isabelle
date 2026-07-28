# Finite-core search for Goodman's question

This directory implements a bounded, certificate-first search for a finite
inconsistent core of the theory containing Purity of Pure.

The mathematical license is the Isabelle theorem
`fresh_goodman_negative_answer_iff_finite_inconsistent_core`: if the selected
CEV+ axiom stock is inconsistent, some finite subset derives `ObjFalse`.
Consequently a fair enumeration of finite derivations is a semidecision
procedure for a negative answer. Failure at a finite bound is not evidence of
consistency.

## Certification boundary

The tool uses four statuses.

1. `bounded_no_refutation`: no derivation was found at the displayed bounds.
2. `search_hit`: the external bounded saturator reached `ObjFalse`.
3. `candidate_core`: the support was extracted and deletion-minimized.
4. `certified_inconsistent_core`: a generated Isabelle theory proved both
   `core <= selected stock` and `core |-CEV+ ObjFalse`, built successfully,
   and audited the final theorem object for oracles, hypotheses, and flex-flex
   pairs.

Only status 4 is called an inconsistent core.

## Search profiles

- `central_recombination`: PP, logical purity, application closure, unique
  proposition-level fundamentality, no fundamentals at other types, and
  zeroary/unary Recombination.
- `repaired_zeroary_exhaustion`: the central stock plus zeroary Exhaustion.
- `full_qln`: the central stock plus zeroary and unary Exhaustion.
- `fresh_full_qln_mf`: full QLN plus all displayed instances of Modalized
  Functionality.

The profiles are deliberately separate. A core using unary Exhaustion does
not refute the central question. Purity of Fun and Persistence are not in any
default profile.

## Bounds and priorities

The campaign begins at structural type depth 1, where there are exactly six
types, and then moves to depth 2 (38 types) and depth 3 (1,446 types).  A
`--type-budget` of zero means every type at the displayed depth. Terms are generated
intrinsically by context, result type, and exact constructor count. The
generic generator never emits `Const`, matching Bacon and Goodman's logical
vocabulary condition exactly.

Strict exhaustive tranches contain every closed logical term whose type and
constructor count satisfy the displayed bounds; they contain no out-of-bound
priority seed.  A separate `--priority-extensions` tranche adds exactly these
four constant-free builders:

- Goodman's T4 diagonal builder;
- Goodman's T6 purity builder;
- the existential RS diagonal builder;
- Bacon's footnote-59 diagonal builder.

Raw syntax is deduplicated structurally. No unproved beta-eta or propositional
quotient is used.

## Running

From the project root:

```bash
python3 -m unittest finite_core_search.test_finite_core_search

python3 finite_core_search/run_search.py \
  --profile central_recombination \
  --type-depth 1 \
  --type-budget 0 \
  --max-term-size 4 \
  --term-cell-cap 0 \
  --priority-extensions
```

The command dovetails through term sizes 1 to 4. To run all four
profiles:

```bash
python3 finite_core_search/run_search.py \
  --all-profiles \
  --type-depth 1 \
  --type-budget 0 \
  --max-term-size 4 \
  --term-cell-cap 0
```

Vampire 5.0.1 is the default engine for the finite ground Horn graph, invoked
in SAT-oriented CASC mode. `Theorem` triggers reconstruction and Isabelle
replay. `CounterSatisfiable` establishes only non-derivability in the displayed
finite rule graph, not consistency of Goodman's object theory.

For the exhaustive size-4 depth-1 tranche, use the compact C worklist engine:

```bash
python3 finite_core_search/run_c_search.py \
  --profile central_recombination \
  --type-depth 1 \
  --term-size 4 \
  --priority-extensions \
  --max-term-nodes 20000000 \
  --output finite_core_search/runs/c_size4
```

The C engine hash-conses the object syntax and implements the same displayed
proof rules as the Python reference saturator. A C refutation remains only a
candidate until its emitted trace replays in Isabelle.

For sizes 5 and above, use the schematic engine:

```bash
python3 finite_core_search/schematic_vampire.py \
  --profile central_recombination \
  --type-depth 1 \
  --term-size 6 \
  --priority-extensions \
  --time-limit 5m \
  --cores 4 \
  --output finite_core_search/runs/schematic_size6
```

It retains the exact finite stock of closed terms and witnesses, but replaces
eagerly generated universal instances with 82 guarded instantiation schemata.
The initial central-Recombination runs returned `CounterSatisfiable` at both
sizes:

| term size | pool axioms | witnesses | result |
|---:|---:|---:|:---|
| 5 | 24,316 | 48,652 | bounded fixed point, no refutation |
| 6 | 408,789 | 817,613 | bounded fixed point, no refutation |

At size 6, the generated TFF input has about 1.23 million declarations and is
about 240 MB. Vampire's decisive strategy took 11.1 seconds (27.5 seconds for
the SAT-oriented portfolio). These are exact results only for the proof rules
listed below.

## Increased CEV+ coverage at size 4

The context-indexed trigger engine holds structural type depth at 1 and term
size at 4 while enlarging the proof calculus:

```bash
python3 finite_core_search/run_context_c_search.py \
  --profile central_recombination \
  --type-depth 1 \
  --term-size 4 \
  --priority-extensions \
  --max-term-nodes 50000000 \
  --output finite_core_search/runs/context_c_size4
```

It searches the empty context and all six singleton contexts. In addition to
the original rules, it includes bounded propositional tautologies, targeted
existential generalization, beta and eta conversion, lazy Leibniz
substitution, Generalization, Instantiation, unary Vector Equivalence, and
the Boolean and Classicist identities. Each new rule has a corresponding
Isabelle replay lemma in
`theories/goodman/cevplus/Bacon_PP_Fresh_Finite_Core_Search.thy`.

The completed central-Recombination run reached a fixed point after deriving
13,094,962 context-indexed judgments and constructing 19,993,531 term nodes.
It took 12.4 seconds and did not derive `ObjFalse`. This is a materially
stronger bounded non-derivability result than the original size-4 run, not a
consistency proof.

The remaining proof-search bounds are explicit: contexts longer than one,
Vector Equivalence of arity greater than one, existential templates absent
from the selected root vocabulary, and propositional tautologies larger than
the displayed term bound. The context engine does not yet emit a proof trace;
if it finds falsity, that result remains a candidate until trace support is
added and Isabelle replay succeeds.

Each tranche writes:

- `manifest.json`, mapping stable axiom names to exact Isabelle syntax;
- `result.json`, including the precise bounds and search status;
- after a search hit, a minimized core and generated replay session.

Generated runs go under `finite_core_search/runs/` and are intentionally
untracked.

## Present proof-search coverage

The initial exact forward saturator includes:

- added-axiom introduction;
- truth and typed reflexivity from the CEV base;
- universal instantiation;
- modus ponens;
- conjunction introduction and elimination;
- double-negation elimination;
- contradiction;
- zeroary Equivalence.

Every positive step has a direct Isar replay macro in
`theories/goodman/cevplus/Bacon_PP_Fresh_Finite_Core_Search.thy`.

The original Python/Vampire engine remains sound but incomplete for the whole
CEV+ calculus at a fixed term bound. The context-indexed engine now covers the
first nonzero context and vector arity, together with the other rules listed
above. The next layer must extend the context/vector bound beyond one,
complete existential-generalization templates, and raise the independent
propositional-formula bound. Every no-refutation status still describes only
the displayed bounded sound fragment.
