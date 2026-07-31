# Higher-Order Metaphysics in Isabelle/HOL

This repository formalizes three successive layers of the Bacon--Dorr--Goodman
project:

1. Bacon's base higher-order theory \(H\);
2. Classicism, including CE and CEV;
3. Goodman's CEV+ theory for the Purity-of-Pure consistency question.

The theory names and theorem identifiers remain stable.  The directory and
session structure now makes the three mathematical layers explicit.

## Repository structure

| Layer | Isabelle session | Source directory | Terminal theory |
|---|---|---|---|
| Base theory \(H\) | `Bacon_Base` | `theories/base/` | `Bacon_Deduction` |
| Classicism, CE, and CEV | `Bacon_Classicism` | `theories/classicism/` | `Bacon_Finite_CEV_Model` |
| Goodman's CEV+ | `Goodman_CEVplus` | `theories/goodman/` | `Bacon_CEV_Axiom_Extension` |

Everything specific to Goodman's question is below `theories/goodman/`:

- `core/`: reusable formal machinery for purity, fundamentality, and Bacon's
  substitution structures;
- `notes/`: the object-language and model-theoretic claims T1--T9 and M1--M7;
- `cevplus/`: finite-fragment, Henkin, and canonical metatheory for CEV+;
- `models/finite/`: Isabelle certificates for bounded external models;
- `models/hol_zf/canonical/`: the official, source-faithful HOL-ZF
  formalization of Bacon's appendix model;
- `models/hol_zf/extensions/`: Goodman's vocabulary interpreted over Bacon's
  exact carriers;
- `models/hol_zf/secondary/`: older comparison models, fragment experiments,
  and the quarantined closure-code/PER program;
- `models/fragments/`: separately localized model extensions;
- `bridges/`: translations between the CEV+ formulation and the model
  sessions, together with the finite-fragment model interface and verified
  cyclic-component constructions.

The detailed directory and session map is in
[`docs/REPOSITORY_STRUCTURE.md`](docs/REPOSITORY_STRUCTURE.md).

Two certificate-first search tools sit beside the Isabelle sources:

- [`finite_core_search/`](finite_core_search/README.md) enumerates bounded
  finite stocks and accepts a contradiction only after Isabelle replay;
- [`pure_diagonal_search/`](pure_diagonal_search/README.md) enumerates closed
  logical builders \(B\), forms \(B(\mathrm{Pure})\), checks their purity in
  Isabelle, and screens them for replayable contradictions.

## Goodman's question

The central question is whether Bacon's background theory, together with
exactly one fundamental proposition, no fundamental entities at other types,
and Purity of Pure, is consistent without assuming Purity of Fun.

The question remains open.  The determinate claims in Goodman's July 2026
notes have been proved, refuted and repaired, or given their exact
qualifications.  The reader-facing account is:

- [Goodman verification and progress report
  (PDF)](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf);
- [LaTeX source](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex);
- [complete verification matrix](reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md).

Among the principal results:

- T3 has a modal gap and is repaired by zeroary Exhaustion or a restricted
  pure-identity rigidity principle.
- M5's countability argument is false and is replaced by a uniform
  orbit-avoidance construction.
- M5's rebuilding step is complete: the rebuilt application-closed pure
  stock contains Goodman's displayed self-inverse exotic operator and has a
  new fundamental proposition satisfying Recombination and `fun-prime`
  separation at every world.
- Recombination plus zeroary Exhaustion and unique proposition-level
  fundamentality derives the existence of a `fun-prime` proposition.
- All four T6 contradiction routes are machine-checked.
- T9's cardinal dichotomy is verified from its explicit counting assumptions.
- Bacon's footnote-59/M1 diagonal is verified in arbitrary compositional CEV+
  Henkin models: full QLN, PP, and Purity of Fun have no such model.  This
  stronger inconsistency theorem does not answer Goodman's question because
  the central axiom sets omit Purity of Fun.
- Bacon's omitted QLN verification is reconstructed for the
  unique-fundamental-proposition specialization relevant to Goodman.  The
  complete closed-logical stock satisfies both zeroary and unary QLN; the
  broader multiple-fundamental extension is not claimed.
- Goodman's QLN granularity condition is encoded in the complete object
  language.  Full QLN and application closure prove that the modal agreement
  disjunction is equivalent to pointwise truth uniformity.  Thus the proposed
  condition is exactly TU in this setting, not a weaker intermediate lemma;
  no derivation of TU from PP is claimed.
- Goodman's L2 is false in Bacon's exact appendix model.  The closed logical
  operator \(Z\), true exactly when its argument varies among the immediate
  successors of the current world, is surjective, noninjective,
  right-cancellative on the exact closed-logical stock, and nonreversible; it
  therefore supplies an explicit L2 counterexample.

The last item settles Goodman's proposed semantic calibration of L2.  It does
not settle the consistency question, because Bacon's appendix model independently
fails Purity of Pure at the unary-operator type.

The official Bacon model is now the exact recursive HOL-ZF construction in
`theories/goodman/models/hol_zf/canonical/`.  It proves the all-type action and
surjectivity facts used in Proposition 8, Bacon's arbitrary-signature
Theorem 10.1 throughout the `t`-fragment, with only signatures involving
`e`-containing types excluded,
H/Classicist/CE/CEV soundness including the individual Existence instance and
vector Equivalence, and the
enumeration/gluing completeness theorem for Bacon's proposition-generated
fragment.  The older tree and PER developments have no import path into this
chain and are built only in the separate
`Higher_Order_Metaphysics_PP_ZF_Secondary` session.

## Building

Isabelle builds must be run serially:

```sh
./check_isabelle.sh
```

This single serial build plan includes every root session and the maintained
Goodman theorem-object audit.  Before Isabelle starts, it also checks that the
canonical Bacon model and its Goodman extensions do not import any theory in
the secondary directory and that the PER declarations remain quarantined.

Focused builds use the central session graph:

```sh
isabelle build -j 1 -d . Bacon_Base
isabelle build -j 1 -d . Bacon_Classicism
isabelle build -j 1 -d . Goodman_CEVplus
isabelle build -j 1 -d . Higher_Order_Metaphysics_PP_Frontier
isabelle build -j 1 -d . Higher_Order_Metaphysics_PP_ZF_Model
isabelle build -j 1 -d . Higher_Order_Metaphysics_PP_ZF_Secondary
```

The audit alone can still be run as a focused check:

```sh
isabelle build -j 1 -d . \
  -D reports/audit_goodman_complete \
  Goodman_Complete_Audit_2026_07_27
```

The project contains no admitted Isabelle proofs.  The audit session checks
the principal theorem objects for oracle dependencies, residual hypotheses,
and flex-flex pairs.

## Documentation

- [`docs/REPOSITORY_STRUCTURE.md`](docs/REPOSITORY_STRUCTURE.md): authoritative
  layer, directory, and session map;
- [`docs/ISABELLE_TERMINOLOGY.md`](docs/ISABELLE_TERMINOLOGY.md): Bacon--Dorr--
  Goodman vocabulary for reader-facing documentation;
- [`STATUS.md`](STATUS.md): detailed chronological theorem status;
- [`CODEX_HANDOFF.md`](CODEX_HANDOFF.md): implementation-level handoff;
- [`GOODMAN_HANDOFF.md`](GOODMAN_HANDOFF.md): earlier Goodman-specific handoff.

## Isabelle knowledge graph

The hand-written Isabelle graph extractor uses Isabelle's elaborated session
database rather than parsing source text heuristically:

```sh
tools/isabelle_kg/build_graph.sh
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search L2
tools/isabelle_kg/query_graph.py deps pp_e_child_variation_refutes_exact_L2 --depth 2
```

The generated graph is stored in `isabelle-kg/` and is the default source for
theory, theorem, import, and dependency questions.
