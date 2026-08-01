# Higher-Order Metaphysics in Isabelle

This repository contains Isabelle/HOL formalizations of higher-order logic and
contemporary higher-order metaphysics. It currently has two independent theory
families: the base theory \(H\) and its Classicist extensions, and Zalta's
Abstract Object Theory. The Goodman project applies the first family to a
separate consistency question.

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
| Abstract Object Theory | `AOT` | [`theories/zalta/`](theories/zalta/) |

## Abstract Object Theory

The independent `AOT` session in [`theories/zalta/`](theories/zalta/)
formalizes Edward Zalta's Abstract Object Theory as presented in *Principia
Logico-Metaphysica*. Daniel Kirchner developed the Isabelle/HOL formalization
and its custom theorem-proving environment. It formalizes Zalta's theory and
PLM developments to which Kirchner and Uri Nodelman made critical theoretical
contributions. The development supplies its own shallow semantic embedding,
syntax, axioms, proof commands, and results concerning logical objects,
possible worlds, natural numbers, possibilities, and truthmaker semantics. It
does not import the base theory \(H\), Classicism, CEV, or the Goodman project.

## Goodman project

The application of these background theories to Jeremy Goodman's
Purity-of-Pure consistency question has its own
[project page](theories/goodman/README.md).

## Building

All Isabelle builds must be run serially.  To check the complete repository:

```sh
./check_isabelle.sh
```

The principal sessions can be built separately:

```sh
isabelle build -j 1 -d . Bacon_Base
isabelle build -j 1 -d . Bacon_Classicism
isabelle build -j 1 -D theories/zalta AOT
```

The project contains no admitted Isabelle proofs.

## Documentation

- [`docs/REPOSITORY_STRUCTURE.md`](docs/REPOSITORY_STRUCTURE.md): complete
  directory and session map;
- [`docs/ISABELLE_TERMINOLOGY.md`](docs/ISABELLE_TERMINOLOGY.md):
  Bacon--Dorr--Goodman terminology;
- [`STATUS.md`](STATUS.md): concise current theorem status; and
- [`sources/README.md`](sources/README.md): primary Bacon, Dorr, Goodman,
  Kirchner, and Zalta source PDFs used in the fidelity audits.

For theory, theorem, import, and dependency queries, the repository includes
tools for generating and querying two separate Isabelle-native knowledge
graphs: one for the Bacon--Dorr--Goodman family and one for Zalta's AOT. They
are never merged. The generated `isabelle-kg/` directory is local and
intentionally excluded from Git because it is large. See the [knowledge-graph
guide](tools/isabelle_kg/README.md) for prerequisites, construction, and query
examples.

## License

The original Isabelle formalization and repository software are licensed
under the [BSD 2-Clause License](LICENSE). The imported AOT material in
[`theories/zalta/`](theories/zalta/) retains its upstream copyright and
licensing status; the repository license does not relicense it. The source
PDFs in [`sources/pdfs/`](sources/pdfs/) likewise remain under the copyright
of their respective authors and publishers.
