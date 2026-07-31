# Goodman Purity-of-Pure Project

This directory applies the Bacon--Dorr background theories to Jeremy
Goodman's consistency question:

> Is Purity of Pure consistent with the remaining theory and the existence of
> a unique fundamental proposition, when Purity of Fun is not assumed?

The question remains open.

## Formal organization

- [`Bacon_CEV_Axiom_Extension.thy`](Bacon_CEV_Axiom_Extension.thy) gives the
  CEV+ axiom-extension interface.
- [`Bacon_PP_Question.thy`](Bacon_PP_Question.thy) states the central
  Purity-of-Pure question.
- [`core/`](core/) contains reusable purity and fundamentality machinery.
- [`notes/`](notes/) formalizes Goodman's displayed T- and M-claims.
- [`cevplus/`](cevplus/) contains CEV+ metatheory and finite-fragment work.
- [`models/`](models/) contains the exact Bacon appendix construction,
  Goodman extensions over it, and explicitly secondary comparison models.
- [`bridges/`](bridges/) contains translations and finite-fragment model
  interfaces.

The official source-faithful reconstruction of Bacon's appendix model is in
[`models/hol_zf/canonical/`](models/hol_zf/canonical/). Goodman-specific
interpretations over its exact carriers are in
[`models/hol_zf/extensions/`](models/hol_zf/extensions/). Older comparison
and experimental constructions are confined to
[`models/hol_zf/secondary/`](models/hol_zf/secondary/) and are not used as
evidence about Bacon's exact model.

## Verified status

The formalization verifies, corrects, or precisely qualifies every determinate
claim in Goodman's notes. It also supplies Bacon's omitted proof of Theorem
10.1 throughout the \(t\)-fragment, the exact H/Classicist/CE/CEV soundness
chain, and the enumeration and gluing argument for Bacon's semantic
frame-theory representation theorem.

The central consistency question is not among the settled results. The exact
appendix model does not validate Purity of Pure at the unary-operator type,
and no model of the complete CEV+ stock with Purity of Pure is currently
known.

For precise statements and qualifications, see:

- [Goodman verification and progress report
  (PDF)](../../reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf);
- [LaTeX source](../../reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex);
- [complete verification
  matrix](../../reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md);
  and
- [final post-repair source-fidelity
  audit](../../reports/CONSENSUS_POSTFIX_FIDELITY_AUDIT_2026-07-31.md).

Run the complete maintained verification serially from the repository root:

```sh
./check_isabelle.sh
```
