# Project Status

Current as of 2026-08-01.

## Bacon--Dorr background theories

The maintained background consists of two Isabelle sessions:

- `Bacon_Base` formalizes the typed object language and Bacon's proof system
  \(H\), including individual Existence.
- `Bacon_Classicism` extends \(H\) with Classicism, CE, CEV, modal and S4
  derivations, vector Equivalence, semantics, soundness, and canonical and
  Henkin completeness results.

These form the repository's first theory family. Their source directories are
[`theories/base/`](theories/base/) and
[`theories/classicism/`](theories/classicism/).

## Zalta's Abstract Object Theory

The independent `AOT` session in [`theories/zalta/`](theories/zalta/)
formalizes Edward Zalta's Abstract Object Theory as presented in *Principia
Logico-Metaphysica*. Daniel Kirchner developed this Isabelle/HOL
formalization and its custom theorem-proving environment. It formalizes
Zalta's theory and PLM developments to which Kirchner and Uri Nodelman made
critical theoretical contributions. It is a standalone shallow semantic
embedding over `HOL-Cardinals`, with its own syntax, axioms, proof commands,
and mathematical developments. It has no import path to or from the
Bacon--Dorr--Goodman sessions.

The imported source is based on `ekpyron/AOT` `develop` commit
`9a165b4d2e1dd9da7276248ebdcaf671dcdf2bdd`, together with separately
identified local extensions and repairs. The maintained `AOT` session builds
under Isabelle2025-2.

## Goodman project

Jeremy Goodman's question asks whether Purity of Pure is consistent with the
Bacon--Dorr background plus a unique fundamental proposition, without Purity
of Fun. The question remains open.

The formalization has nevertheless completed the following source-verification
and model-theoretic work:

- Goodman's determinate T- and M-claims have been proved, refuted and repaired,
  or given their exact qualifications.
- Bacon's exact appendix construction is canonical in the repository. The
  development proves the recursive carriers and action, Proposition 8,
  Theorem 10.1 throughout the \(t\)-fragment, H/Classicist/CE/CEV soundness,
  enumeration and gluing, and the resulting semantic frame-theory
  representation theorem.
- Theorem 10.1 covers arbitrary signatures throughout the \(t\)-fragment;
  signatures involving \(e\)-containing types remain outside its verified
  scope.
- Goodman's L2 fails when the pure unary operators are precisely the
  denotations of closed logical terms in Bacon's exact appendix model.
- For that exact-carrier closed-logical interpretation, PP is equivalent to
  membership of the unary-stock classifier in the next closed-logical stock.
  That membership is not presently proved false or true without additional
  assumptions.
- The maintained Goodman audit checks 167 principal theorem objects for
  oracles, residual hypotheses, and flex-flex constraints.

None of these results settles the central question. In particular, fragment
models and results about the operators denoted by closed logical terms do not
supply an interpretation of Pure satisfying the unrestricted logical-purity
schema and Purity of Pure.

The concise Goodman project index is
[`theories/goodman/README.md`](theories/goodman/README.md). The authoritative
reader-facing records are:

- [verification and progress report
  (PDF)](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf);
- [report source](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex);
- [complete verification
  matrix](reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md); and
- [final post-repair source-fidelity
  audit](reports/CONSENSUS_POSTFIX_FIDELITY_AUDIT_2026-07-31.md).

## Verification

All Isabelle builds must be serial. The maintained repository check is:

```sh
./check_isabelle.sh
```

It checks the session graph, the exact-Bacon-model boundary, reader-facing
terminology, every maintained Isabelle session, and the dedicated Goodman
audit. The repository contains no admitted Isabelle proofs.

The official Bacon appendix model is in
[`theories/goodman/models/hol_zf/canonical/`](theories/goodman/models/hol_zf/canonical/).
Goodman's interpretations over those carriers are in
[`theories/goodman/models/hol_zf/extensions/`](theories/goodman/models/hol_zf/extensions/).
Older comparison and experimental models are isolated in
[`theories/goodman/models/hol_zf/secondary/`](theories/goodman/models/hol_zf/secondary/)
and have no import path into the canonical chain.
