# Goodman extensions of Bacon's exact model

These seventeen theories interpret Goodman's vocabulary over the exact Bacon
carriers from `../canonical/`.

The basic Goodman interpretation is developed in:

- [`Bacon_PP_ZF_Exact_Logical_Stock.thy`](Bacon_PP_ZF_Exact_Logical_Stock.thy),
  for the denotations of closed logical terms;
- [`Bacon_PP_ZF_Exact_Logical_Stock_Action.thy`](Bacon_PP_ZF_Exact_Logical_Stock_Action.thy),
  for their behavior under Bacon's action;
- [`Bacon_PP_ZF_Exact_Generic_Seed.thy`](Bacon_PP_ZF_Exact_Generic_Seed.thy),
  for the generic fundamental proposition and the interpretation of
  fundamentality; and
- [`Bacon_PP_ZF_Exact_Recombination.thy`](Bacon_PP_ZF_Exact_Recombination.thy),
  for Recombination, Exhaustion, QLN, and Goodman's background principles.

The exact-carrier treatment of M1 and Purity of Pure is in:

- [`Bacon_PP_ZF_Exact_M1.thy`](Bacon_PP_ZF_Exact_M1.thy), which transfers the
  footnote-59 calculation to Bacon's recursively restricted carriers and
  identifies the footnote-60 classifier there; and
- [`Bacon_PP_ZF_Exact_Self_Classifying_Stock.thy`](Bacon_PP_ZF_Exact_Self_Classifying_Stock.thy),
  which proves that Purity of Pure is equivalent to the appropriate
  higher-type membership condition and records sufficient conditions on an
  interpretation of `Pure`. It neither constructs such an interpretation nor
  proves the membership condition false.

Goodman's L2 is analyzed over the complete stock of closed logical denotations
in the following sequence:

- [`Bacon_PP_ZF_Exact_L2_Model.thy`](Bacon_PP_ZF_Exact_L2_Model.thy),
  [`Bacon_PP_ZF_Exact_L2_Generic_Prelim.thy`](Bacon_PP_ZF_Exact_L2_Generic_Prelim.thy),
  and [`Bacon_PP_ZF_Exact_L2_Generic.thy`](Bacon_PP_ZF_Exact_L2_Generic.thy)
  set up the exact semantic formulation and the required generic proposition;
- [`Bacon_PP_ZF_Exact_L2_Reduction.thy`](Bacon_PP_ZF_Exact_L2_Reduction.thy),
  [`Bacon_PP_ZF_Exact_L2_Cancellation.thy`](Bacon_PP_ZF_Exact_L2_Cancellation.thy),
  and [`Bacon_PP_ZF_Exact_L2_Obstruction.thy`](Bacon_PP_ZF_Exact_L2_Obstruction.thy)
  reduce L2 to the relevant reversibility and cancellation properties;
- [`Bacon_PP_ZF_Exact_L2_Refutation.thy`](Bacon_PP_ZF_Exact_L2_Refutation.thy),
  [`Bacon_PP_ZF_Exact_L2_Child_Atom.thy`](Bacon_PP_ZF_Exact_L2_Child_Atom.thy),
  and [`Bacon_PP_ZF_Exact_L2_Immediate_Successor.thy`](Bacon_PP_ZF_Exact_L2_Immediate_Successor.thy)
  isolate the exact counterexample conditions; and
- [`Bacon_PP_ZF_Exact_L2_Child_Variation_Semantics.thy`](Bacon_PP_ZF_Exact_L2_Child_Variation_Semantics.thy)
  and [`Bacon_PP_ZF_Exact_L2_Child_Variation.thy`](Bacon_PP_ZF_Exact_L2_Child_Variation.thy)
  prove that a closed logical child-variation operator falsifies L2 and its
  strong form in this interpretation.

This directory introduces no alternative carrier, application operation, or
equivalence relation, and it does not import the secondary development.
