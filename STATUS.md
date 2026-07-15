# Formalization Status

This file separates verified Isabelle results from conditional interfaces and
remaining paper-level obligations. The status below is for release `v0.1.0`
under Isabelle2025-2.

## Verified foundations

- A deep embedding of the Bacon-style typed object language, including de
  Bruijn syntax, typing, renaming, substitution, and beta-eta conversion.
- Hilbert systems `H`, `C`, `CE`, and `CEV`, with formula preservation.
- Restricted necessitation for the weaker systems and unrestricted
  necessitation for `CEV` through theorem-to-truth equivalence.
- The `CEV` modal `K`, `T`, and `4` schemata, packaged as `CEV_S4_package`.
- Full `H` soundness for `valid_in_context`, with relative soundness results
  for `C`, `CE`, and `CEV` in the corresponding semantic locales.

## Completeness

- `H` and `C` have verified Henkin and substitutional term-model completeness
  results, including `H_Henkin_valid_in_context_iff_proves`,
  `C_Henkin_valid_in_context_iff_proves`,
  `H_term_model_valid_iff_proves`, `C_term_model_valid_iff_proves`, and the
  corresponding strong-completeness theorems.
- Completeness for the earlier general `valid_in_context` interface remains
  conditional on its stated countermodel properties.
- The `CE` and `CEV` canonical infrastructure is substantial but not yet a
  fully unconditional completeness proof. The principal named `CEV`
  construction obligation is
  `CEV_context_equiv_abstract_const_admissible`.

## Caie application

- Caie's Appendix C formulas 32--40 are represented in the deep embedding.
- None of the nine theorem statements follows by definition and beta-eta
  conversion alone. The four definitional bridges are verified separately.
- Every Appendix C target is locally derivable from the explicit
  `caie_appendix_C_axiom_package`. The closure is recorded by
  `caie_appendix_C_axiom_package_closes_targets_from_verified` and the
  source-to-target bridge-pair layer.
- This establishes derivability from the stated package; it does not yet
  reduce every package member to a smallest philosophically natural basis.

## Finite M-star model

- `Bacon_Caie_Mstar.thy` verifies the finite Name, emptiness, rigidity,
  coverage, and plenitude claims collected in
  `Mstar_proposition29_finite_bullets`.
- Proposition 29's theorem-truth bullet is currently conditional. The theorem
  `Mstar_proposition29_from_NDS_soundness` requires both
  `nds_background_soundness` and `mstar_nds_model_obligation`.

## Remaining milestones

1. Prove `CEV_context_equiv_abstract_const_admissible` and close the general
   `CEV` completeness construction.
2. Formalize and prove the NDS-model soundness result corresponding to Caie's
   Proposition 27.
3. Connect the finite M-star structure to the deep NDS semantics by proving
   `mstar_nds_model_obligation`.
4. Further decompose the Caie counterfactual and name principles where a
   smaller philosophically natural basis is available.

