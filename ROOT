session Higher_Order_Metaphysics = HOL +
  description "
    A deep embedding of a Bacon-style higher-order object language in Isabelle/HOL.
  "
  sessions
    "HOL-Library"
  theories
    Bacon_CEV_Axiom_Extension

session Higher_Order_Metaphysics_PP in "pp" = Higher_Order_Metaphysics +
  description "
    Settled results on the Goodman Purity-of-Pure consistency question.

    This session is the stable base.  Work in progress belongs in the
    Frontier session below, so that editing it does not force a rebuild
    of everything here.
  "
theories
  Bacon_PP_Diagonal
  Bacon_PP_Generic_Witness
  Bacon_PP_MSet
  Bacon_PP_Parity
  Bacon_PP_LevelClasses
  Bacon_PP_Uniform_Index
  Bacon_PP_TreeAut
  Bacon_PP_Orbit_Stability
  Bacon_PP_TreeAut_Functions
  Bacon_PP_TypeCoherence
  Bacon_PP_Purity_Operator
  Bacon_PP_Symmetric_Witness

session Higher_Order_Metaphysics_PP_Frontier in "frontier" =
    Higher_Order_Metaphysics_PP +
  description "
    Work in progress on the self-classifying stock.

    A leaf session over the stored heap of Higher_Order_Metaphysics_PP, so a
    single theory here rebuilds in seconds rather than forcing the whole PP
    chain to be rechecked.  The timeout makes a runaway proof fail fast
    instead of hanging a build.  Move theories down into the PP session once
    they are settled.
  "
  options [timeout = 60]
theories
  Bacon_PP_Stock_Requirements
  Bacon_PP_Diagonal_Reduction
  Bacon_PP_Seed_Nontriviality
  Bacon_PP_Seed_Aware_Requirements
  Bacon_PP_Domain_Persistence
  Bacon_PP_Attainment
  Bacon_PP_Attainment_Failure
  Bacon_PP_Decided_Realization
  Bacon_PP_Decision_Basis
  Bacon_PP_Pure_Decision_Basis
  Bacon_PP_Cone_Determined
  Bacon_PP_Oterm_Bridge
  Bacon_PP_Higher_Bridge
