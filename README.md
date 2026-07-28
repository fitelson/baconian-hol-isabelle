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
- `models/hol_zf/`: Bacon-style models formalized over HOL-ZF;
- `models/fragments/`: separately localized model extensions;
- `bridges/`: translations between the CEV+ formulation and the model
  sessions.

The detailed directory and session map is in
[`docs/REPOSITORY_STRUCTURE.md`](docs/REPOSITORY_STRUCTURE.md).

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
- Goodman's L2 is false in Bacon's appendix model.  The closed logical
  operator \(Z\), defined by comparing the truth values at the two immediate
  successor worlds, is surjective, noninjective, right-cancellative among the
  operators denoted by closed terms containing only logical vocabulary, and
  nonreversible; it therefore supplies an explicit L2 counterexample.

The last item settles Goodman's proposed semantic calibration of L2.  It does
not settle the consistency question, because Bacon's appendix model independently
fails Purity of Pure at the unary-operator type.

## Building

Isabelle builds must be run serially:

```sh
isabelle build -j 1 -D .
```

Focused builds use the central session graph:

```sh
isabelle build -j 1 -d . Bacon_Base
isabelle build -j 1 -d . Bacon_Classicism
isabelle build -j 1 -d . Goodman_CEVplus
isabelle build -j 1 -d . Higher_Order_Metaphysics_PP_Frontier
isabelle build -j 1 -d . Higher_Order_Metaphysics_PP_ZF_Model
```

The complete Goodman audit is:

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
tools/isabelle_kg/query_graph.py deps pp_b_child_xor_refutes_exact_L2 --depth 2
```

The generated graph is stored in `isabelle-kg/` and is the default source for
theory, theorem, import, and dependency questions.
