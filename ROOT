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
  Bacon_PP_Heredity_Semantics
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
  Bacon_PP_Axiom_Soundness
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
  Bacon_PP_Positive_Diagonal
  Bacon_PP_Modal_Five
  Bacon_PP_Five_Countermodel
  Bacon_PP_Minimal_Axioms
  Bacon_PP_Modalized_Functionality
  Bacon_PP_Definable_Purity
  Bacon_PP_Intensionality
  Bacon_PP_Modalized_Functionality_Derived
  Bacon_PP_T6_Encoding
  Bacon_PP_Goodman_Composition
  Bacon_PP_Goodman_Fun_Prime_Closure
  Bacon_PP_Goodman_Fun_Prime_Nontriviality
  Bacon_PP_Goodman_Fun_Prime_Attainment
  Bacon_PP_Goodman_Fun_Prime_Possibly_Pure
  Bacon_PP_Goodman_Fun_Prime_Noncontingency
  Bacon_PP_Goodman_Fun_Prime_Six_Distinct
  Bacon_PP_Goodman_T2f_Verified
  Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse
  Bacon_PP_Goodman_Heredity
  Bacon_PP_Goodman_Heredity_Obstruction
  Bacon_PP_Goodman_Pure_Proposition_Triviality
  Bacon_PP_Goodman_Biconditional_Classification
  Bacon_PP_Goodman_WI_Collapse
  Bacon_PP_Goodman_Heredity_Modal
  Bacon_PP_Goodman_Heredity_Rigidity
  Bacon_PP_Goodman_Heredity_Core
  Bacon_PP_Goodman_Heredity_Exhaustion
  Bacon_PP_Goodman_Heredity_Sharp
  Bacon_PP_Goodman_Heredity_Advertised
  Bacon_PP_Goodman_Higher_Type_Diagonal
  Bacon_PP_Goodman_Proliferation
  Bacon_PP_Goodman_T6_Inv
  Bacon_PP_Goodman_T6_TU
  Bacon_PP_Goodman_T6_WI
  Bacon_PP_Goodman_T6_WI_Master
  Bacon_PP_Goodman_T6_RS_Encoding
  Bacon_PP_Goodman_T6_RS
  Bacon_PP_Goodman_T7_Absorption
  Bacon_PP_Goodman_T8_Encoding
  Bacon_PP_Goodman_T8_Kind_Uniqueness
  Bacon_PP_Goodman_T8_Base_Kinds
  Bacon_PP_Goodman_T8_Growth
  Bacon_PP_QSS_Recombination_Bridge
  Bacon_PP_Central_Model_Obligations

session Higher_Order_Metaphysics_PP_Models in "models" =
    Higher_Order_Metaphysics_PP +
  description "
    Explicit Isabelle certificates for finite candidate models produced by
    external model finders.  Each theory proves every axiom in its documented
    bounded benchmark; no such certificate is a model of the full PP schemas
    unless a separate translation theorem says so.
  "
  options [timeout = 60]
theories
  Bacon_PP_Vampire_Depth1_Model

session Higher_Order_Metaphysics_PP_ZF_Model in "zf_model" =
    Higher_Order_Metaphysics_PP_Frontier +
  description "
    A direct preconstructed-domain model program for Goodman's central PP stock.

    The universal carrier is the axiomatized ZFC universe supplied by HOL-ZF.
    Results in this session are therefore relative to HOL-ZF's additional
    set-theoretic assumptions.
  "
  options [timeout = 60]
  sessions
    "HOL-ZF"
theories
  Bacon_PP_ZF_Full_Frame
  Bacon_PP_ZF_Hyper_Frame
  Bacon_PP_ZF_Tree_Frame
  Bacon_PP_ZF_Tree_Logical_Stock
  Bacon_PP_ZF_Tree_Generic_Seed
  Bacon_PP_ZF_Tree_Basis_Stock
  Bacon_PP_ZF_Tree_Seeded_Stock
  Bacon_PP_ZF_Tree_Range_Classifier
  Bacon_PP_ZF_Tree_Range_Diagonal
  Bacon_PP_ZF_Tree_Range_Term_Basis
