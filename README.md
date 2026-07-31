# Bacon--Dorr Higher-Order Logic in Isabelle/HOL

This repository formalizes the higher-order logical background developed by
Bacon and Dorr.  Its two principal layers are Bacon's base theory \(H\) and
Classicism, including CE and CEV.

## Base theory \(H\)

The `Bacon_Base` session in [`theories/base/`](theories/base/) contains:

- the simple types and typed object language;
- de Bruijn syntax, renaming, and capture-avoiding substitution;
- typing and beta contraction; and
- the Hilbert-style derivability relation for \(H\), including individual
  Existence.

Its terminal theory is
[`Bacon_Deduction.thy`](theories/base/Bacon_Deduction.thy).

## Classicism, CE, and CEV

The `Bacon_Classicism` session in
[`theories/classicism/`](theories/classicism/) extends \(H\) with:

- Classicism and the CE and CEV derivability systems;
- Bacon's logical abbreviations and Boolean and quantificational principles;
- necessity defined by propositional identity with truth, together with the
  corresponding modal and S4 derivations;
- beta--eta conversion and vector Equivalence;
- abstract applicative semantics and soundness; and
- canonical-model, Henkin-completeness, quotient, and finite-model results.

Its terminal theory is
[`Bacon_Finite_CEV_Model.thy`](theories/classicism/Bacon_Finite_CEV_Model.thy).

| Layer | Isabelle session | Source directory |
|---|---|---|
| Base theory \(H\) | `Bacon_Base` | [`theories/base/`](theories/base/) |
| Classicism, CE, and CEV | `Bacon_Classicism` | [`theories/classicism/`](theories/classicism/) |

## Goodman project

The application of these background theories to Jeremy Goodman's
Purity-of-Pure consistency question is kept in
[`theories/goodman/`](theories/goodman/).  Its current mathematical status is
given in the [Goodman verification and progress report
(PDF)](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf).

## Building

All Isabelle builds must be run serially.  To check the complete repository:

```sh
./check_isabelle.sh
```

The two background sessions can be built separately:

```sh
isabelle build -j 1 -d . Bacon_Base
isabelle build -j 1 -d . Bacon_Classicism
```

The project contains no admitted Isabelle proofs.

## Documentation

- [`docs/REPOSITORY_STRUCTURE.md`](docs/REPOSITORY_STRUCTURE.md): complete
  directory and session map;
- [`docs/ISABELLE_TERMINOLOGY.md`](docs/ISABELLE_TERMINOLOGY.md):
  Bacon--Dorr--Goodman terminology;
- [`STATUS.md`](STATUS.md): detailed theorem status; and
- [`CODEX_HANDOFF.md`](CODEX_HANDOFF.md): implementation-level handoff.

For theory, theorem, import, and dependency queries, the repository includes
an Isabelle-native knowledge graph in [`isabelle-kg/`](isabelle-kg/), generated
from Isabelle's elaborated session database by
[`tools/isabelle_kg/build_graph.sh`](tools/isabelle_kg/build_graph.sh).
