# Canonical Bacon appendix model

This directory is the source-faithful HOL-ZF formalization of Bacon's appendix
model.  Its dependency spine is:

```text
Bacon_PP_ZF_Word_Propositions
  -> Bacon_PP_ZF_Full_MSet
  -> Bacon_PP_ZF_Exact_Frame
  -> Bacon_PP_ZF_Exact_Substitution
  -> Bacon_PP_ZF_Exact_10_1
  -> Bacon_PP_ZF_Exact_CEV_Soundness
  -> Bacon_PP_ZF_Exact_Enumeration
  -> Bacon_PP_ZF_Exact_Completeness
```

The carriers at every arrow type are Bacon's recursively restricted
function spaces.  `Bacon_PP_ZF_Full_MSet` proves the all-type action,
closure, surjectivity, and substitution/application laws needed for
Proposition 8.  `Bacon_PP_ZF_Exact_10_1` proves Bacon's arbitrary-signature
theorem throughout the `t`-fragment and supplies the omitted branch-gluing
argument.
`Bacon_PP_ZF_Exact_CEV_Soundness` proves soundness of the structural, H,
Classicist, CE, and CEV rules, including the individual Existence instance and vector
Equivalence.  The last two theories formalize Bacon's enumeration and gluing
argument and its completeness consequence for the proposition-generated
fragment and a fixed signature.  Signatures involving `e`-containing types
remain outside scope, as Bacon explicitly defers that extension.

Alternative carriers and evaluators are not imported by this chain.  They are
retained only in `../secondary/` for comparison and historical audit.
