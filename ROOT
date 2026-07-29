session Bacon_Base in "theories/base" = HOL +
  description "
    Bacon's base higher-order language and proof theory H.
  "
  sessions
    "HOL-Library"
  theories
    Bacon_Deduction

session Bacon_Classicism in "theories/classicism" = Bacon_Base +
  description "
    Classicism, including CE, CEV, modal derivations, semantics, and
    canonical-model infrastructure.
  "
  theories
    Bacon_Finite_CEV_Model

session Goodman_CEVplus in "theories/goodman" = Bacon_Classicism +
  description "
    Goodman's CEV+ vocabulary and axiom-extension interface for Purity of Pure.
  "
  theories
    Bacon_CEV_Axiom_Extension

session Higher_Order_Metaphysics_PP in "theories/goodman/core" =
    Goodman_CEVplus +
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

session Higher_Order_Metaphysics_PP_Frontier in "theories/goodman/notes" =
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
  Bacon_PP_Goodman_M2
  Bacon_PP_Goodman_M1
  Bacon_PP_Goodman_M3
  Bacon_PP_Goodman_M4
  Bacon_PP_Goodman_M5
  Bacon_PP_Goodman_M5_Collision
  Bacon_PP_Goodman_M5_Orbit_Avoidance
  Bacon_PP_Goodman_M6
  Bacon_PP_Goodman_M7_Invariant_Reachability
  Bacon_PP_Goodman_M3_Complete
  Bacon_PP_Goodman_M1_Complete
  Bacon_PP_Goodman_M1_Fn60
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
  Bacon_PP_Goodman_M5_Existential_Invertibles
  Bacon_PP_Goodman_T6_WI
  Bacon_PP_Goodman_T6_WI_Master
  Bacon_PP_Goodman_T6_RS_Encoding
  Bacon_PP_Goodman_T6_RS
  Bacon_PP_Goodman_T7_Absorption
  Bacon_PP_Goodman_T8_Encoding
  Bacon_PP_Goodman_T8_Kind_Uniqueness
  Bacon_PP_Goodman_T8_Base_Kinds
  Bacon_PP_Goodman_T8_Growth
  Bacon_PP_Goodman_T9
  Bacon_PP_QSS_Recombination_Bridge
  Bacon_PP_Central_Model_Obligations

session Higher_Order_Metaphysics_PP_Models in "theories/goodman/models/finite" =
    Higher_Order_Metaphysics_PP +
  description "
    Explicit Isabelle certificates for finite candidate models produced by
    external model finders.  Each theory proves every axiom in its documented
    bounded benchmark; no such certificate is a model of the full PP schemas
    unless a separate translation theorem says so.
  "
  options [timeout = 600]
theories
  Bacon_PP_Vampire_Depth1_Model
  Bacon_PP_Vampire_Fresh_Finite_Model
  Bacon_PP_Vampire_Unworlded_Finite_Model

session Higher_Order_Metaphysics_PP_ZF_Model
    in "theories/goodman/models/hol_zf" =
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
  Bacon_PP_ZF_Goodman_M1_Fn60
  Bacon_PP_ZF_Bacon_10_1
  Bacon_PP_ZF_Goodman_M5_Rebuild
  Bacon_PP_ZF_Goodman_M7
  Bacon_PP_ZF_Tree_Basis_Stock
  Bacon_PP_ZF_Tree_Seeded_Stock
  Bacon_PP_ZF_Tree_Range_Classifier
  Bacon_PP_ZF_Tree_Range_Diagonal
  Bacon_PP_ZF_Tree_Range_Term_Basis
  Bacon_PP_ZF_Repaired_Central_Stock
  Bacon_PP_ZF_Tree_CEV_Soundness
  Bacon_PP_ZF_Tree_One_Step_Classifier_Stock
  Bacon_PP_ZF_Tree_One_Classifier_Contexts
  Bacon_PP_ZF_Tree_Ambient_Inverse
  Bacon_PP_ZF_Tree_Quotient_Diagonal
  Bacon_PP_ZF_Tree_Quotient_Diagonal_Builder
  Bacon_PP_ZF_Tree_Stabilizer_Orbit
  Bacon_PP_ZF_Goodman_L2_Model
  Bacon_PP_ZF_Goodman_L2_Global_Reduction
  Bacon_PP_ZF_Goodman_L2_Composition_Fragment
  Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers
  Bacon_PP_ZF_Goodman_L2_Child_Xor
  Bacon_PP_ZF_Goodman_L2_Stock_Expansion
  Bacon_PP_ZF_Fresh_Sparse_Fragment_Model
  Bacon_PP_ZF_Fresh_Identity_Fragment_Model
  Bacon_PP_ZF_Fresh_Identity_Negation_Fragment_Model
  Bacon_PP_ZF_Fresh_Logical_Constants_Fragment_Model
  Bacon_PP_ZF_Fresh_Constant_Builder_Fragment_Model
  Bacon_PP_ZF_Fresh_Conjunction_Fragment_Model
  Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model

session Higher_Order_Metaphysics_PP_ZF_Truth_Functions
    in "theories/goodman/models/fragments/truth_functions" =
    Higher_Order_Metaphysics_PP_ZF_Model +
  description "
    Uniform HOL-ZF fragment model for all sixteen curried binary
    truth-functions.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_Binary_Truth_Functions_Fragment_Model

session Higher_Order_Metaphysics_PP_ZF_Necessity
    in "theories/goodman/models/fragments/necessity" =
    Higher_Order_Metaphysics_PP_ZF_Truth_Functions +
  description "
    HOL-ZF moving-seed fragment model with the pure necessity operator.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_Necessity_Fragment_Model

session Higher_Order_Metaphysics_PP_ZF_Possibility
    in "theories/goodman/models/fragments/possibility" =
    Higher_Order_Metaphysics_PP_ZF_Necessity +
  description "
    HOL-ZF moving-seed fragment model with pure necessity and possibility.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_Possibility_Fragment_Model

session Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified
    in "theories/goodman/models/fragments/higher_order_quantified" =
    Higher_Order_Metaphysics_PP_ZF_Possibility +
  description "
    HOL-ZF moving-seed fragment model absorbing six higher-order quantified
    logical operators.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model

session Higher_Order_Metaphysics_PP_ZF_Fun_Prime
    in "theories/goodman/models/fragments/fun_prime" =
    Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified +
  description "
    HOL-ZF moving-seed fragment model enlarged by the object-language
    fun-prime operator.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_Fun_Prime_Fragment_Model

session Higher_Order_Metaphysics_PP_ZF_T6_Diagonal
    in "theories/goodman/models/fragments/t6_diagonal" =
    Higher_Order_Metaphysics_PP_ZF_Fun_Prime +
  description "
    HOL-ZF moving-seed investigation of the fun-prime and T6 diagonal
    operators.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Fresh_T6_Diagonal_Fragment_Model
  Bacon_PP_ZF_Fresh_T6_Collisions

session Higher_Order_Metaphysics_PP_ZF_Modal_Depth_Two
    in "theories/goodman/models/fragments/modal_depth_two" =
    Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified +
  description "
    HOL-ZF moving-seed fragment for modal-depth-two alternations, based on a
    reusable modal-word normalization language.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Modal_Word_Normalization
  Bacon_PP_ZF_Fresh_Modal_Depth_Two_Fragment_Model

session Goodman_CEVplus_Canonical in "theories/goodman/cevplus" =
    Goodman_CEVplus +
  description "
    Canonical and Henkin metatheory for Goodman's CEV+ formulation.
  "
  options [timeout = 120]
theories
  Bacon_PP_Fresh_Finite_Fragment
  Bacon_PP_Fresh_Finite_Core_Search
  Bacon_PP_Fresh_Local_Henkin_Extension
  Bacon_PP_Fresh_CEVplus_Closure
  Bacon_PP_Fresh_Relative_Lindenbaum
  Bacon_CEV_Axiom_Relative_Henkin
  Bacon_PP_Fresh_Relative_Henkin_Completion
  Bacon_PP_Fresh_CEVplus_Canonical_Semantics
  Bacon_PP_Fresh_Canonical_Quotient_Frontier

session Goodman_CEVplus_ZF_Bridge
    in "theories/goodman/bridges/cevplus_zf" =
    Higher_Order_Metaphysics_PP_ZF_Truth_Functions +
  description "
    Bridge between Goodman's CEV+ formulation and the explicit HOL-ZF fragment
    models.
  "
  options [timeout = 60]
  sessions
    Goodman_CEVplus_Canonical
theories
  Bacon_PP_Fresh_ZF_Fragment_Bridge

session Goodman_CEVplus_Modal_Quantified_Bridge
    in "theories/goodman/bridges/modal_quantified" =
    Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified +
  description "
    Bridge from the modal and higher-order quantified fragment models to
    Goodman's CEV+ principles.
  "
  options [timeout = 60]
  sessions
    Goodman_CEVplus_ZF_Bridge
theories
  Bacon_PP_Fresh_ZF_Modal_Quantified_Bridge
