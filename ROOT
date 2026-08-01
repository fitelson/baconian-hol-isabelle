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
  Bacon_PP_Appendix_Model
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
  Bacon_PP_Goodman_T9_Infinitude
  Bacon_PP_Goodman_Granularity
  Bacon_PP_Goodman_Granularity_QLN
  Bacon_PP_QSS_Recombination_Bridge
  Bacon_PP_Complement_Pair_Recombination
  Bacon_PP_Goodman_M1_Henkin

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
    Canonical HOL-ZF formalization of Bacon's appendix model and the Goodman
    interpretations proved directly over its exact carriers.

    The canonical theories use Bacon's recursively restricted function spaces
    and division action.  The universal carrier is the axiomatized ZFC universe
    supplied by HOL-ZF, so these results are relative to HOL-ZF's additional
    set-theoretic assumptions.  Alternative model constructions are isolated
    in a separate child session.
  "
  options [timeout = 60]
  sessions
    "HOL-ZF"
  directories
    "canonical"
    "extensions"
theories
  Bacon_PP_ZF_Word_Propositions
  Bacon_PP_ZF_Full_MSet
  Bacon_PP_ZF_Exact_Frame
  Bacon_PP_ZF_Exact_Logical_Stock
  Bacon_PP_ZF_Exact_Substitution
    Bacon_PP_ZF_Exact_Logical_Stock_Action
    Bacon_PP_ZF_Exact_Generic_Seed
    Bacon_PP_ZF_Exact_L2_Model
    Bacon_PP_ZF_Exact_L2_Generic_Prelim
    Bacon_PP_ZF_Exact_L2_Generic
    Bacon_PP_ZF_Exact_L2_Reduction
    Bacon_PP_ZF_Exact_L2_Cancellation
    Bacon_PP_ZF_Exact_L2_Obstruction
    Bacon_PP_ZF_Exact_L2_Refutation
    Bacon_PP_ZF_Exact_L2_Child_Atom
    Bacon_PP_ZF_Exact_L2_Immediate_Successor
    Bacon_PP_ZF_Exact_L2_Child_Variation_Semantics
    Bacon_PP_ZF_Exact_L2_Child_Variation
    Bacon_PP_ZF_Exact_Recombination
    Bacon_PP_ZF_Exact_M1
    Bacon_PP_ZF_Exact_Self_Classifying_Stock
  Bacon_PP_ZF_Exact_10_1
  Bacon_PP_ZF_Exact_CEV_Soundness
  Bacon_PP_ZF_Exact_Enumeration
  Bacon_PP_ZF_Exact_Completeness

session Higher_Order_Metaphysics_PP_ZF_Secondary
    in "theories/goodman/models/hol_zf/secondary" =
    Higher_Order_Metaphysics_PP_ZF_Model +
  description "
    Secondary comparison models, finite-fragment experiments, and the
    abandoned closure-code construction.  None of these theories belongs to
    the source-faithful Bacon completeness chain.
  "
  options [timeout = 60]
theories
  Bacon_PP_Central_Model_Obligations
  Bacon_PP_ZF_Full_Frame
  Bacon_PP_ZF_Hyper_Frame
  Bacon_PP_ZF_Tree_Frame
  Bacon_PP_ZF_Bacon_Frame
  Bacon_PP_ZF_Bacon_Action
  Bacon_PP_ZF_Tree_Logical_Stock
  Bacon_PP_ZF_Tree_Automorphism_Equivariance
  Bacon_PP_ZF_Tree_Generic_Seed
  Bacon_PP_ZF_Goodman_M1_Fn60
  Bacon_PP_ZF_Bacon_10_1
  Bacon_PP_ZF_Bacon_QLN
  Bacon_PP_ZF_Goodman_M5_Rebuild
  Bacon_PP_ZF_Goodman_M7
  Bacon_PP_ZF_Tree_Basis_Stock
  Bacon_PP_ZF_Tree_Seeded_Stock
  Bacon_PP_ZF_Tree_Range_Classifier
  Bacon_PP_ZF_Tree_Range_Diagonal
  Bacon_PP_ZF_Tree_Range_Term_Basis
  Bacon_PP_ZF_Repaired_Central_Stock
  Bacon_PP_ZF_Tree_CEV_Soundness
  Bacon_PP_ZF_Goodman_M1_Fn59
      Bacon_PP_ZF_Tree_One_Step_Classifier_Stock
      Bacon_PP_ZF_Tree_One_Classifier_Contexts
      Bacon_PP_ZF_Tree_Family_Probe_Absorption
      Bacon_PP_ZF_Tree_Inverse_Cone_Naturality
      Bacon_PP_ZF_Tree_Family_View_Definability
      Bacon_PP_ZF_Tree_Symmetrized_Singleton
      Bacon_PP_ZF_Tree_Complemented_Symmetrized_Singleton
      Bacon_PP_ZF_Tree_Indexed_Family_Probe
      Bacon_PP_ZF_Tree_Singleton_Family_Elimination
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

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Core
    in "theories/goodman/models/hol_zf_boolean_probe/core" =
    Higher_Order_Metaphysics_PP_ZF_Secondary +
  description "
    Boolean closure of the first classifier-generated unary probe and its
    Recombination seed.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Closure

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Classification
    in "theories/goodman/models/hol_zf_boolean_probe/classification" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Core +
  description "
    Exact finite classification of stable parameters for the symmetrized
    singleton family.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Classification

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Collision
    in "theories/goodman/models/hol_zf_boolean_probe/collision" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Classification +
  description "
    Collision classification and the remaining stabilization condition for
    the Boolean family probe.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Collision

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Canonical_Cases
    in "theories/goodman/models/hol_zf_boolean_probe/canonical_cases" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Collision +
  description "
    Automorphism analysis and absorption of the finite canonical collision
    cases left by the Boolean family-probe classification.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Canonical_Cases

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Successor
    in "theories/goodman/models/hol_zf_boolean_probe/successor" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Canonical_Cases +
  description "
    Boolean closure after adjoining the stabilized classifier-generated
    probe, as the next fixed-point stage of the cyclic model construction.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Successor

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Higher_Types
    in "theories/goodman/models/hol_zf_boolean_probe/higher_types" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Successor +
  description "
    Higher-type pure stocks forced by negation, conjunction, and the
    stabilized classifier-bearing Boolean cycle.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Higher_Types

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Model_Core
    in "theories/goodman/models/hol_zf_boolean_probe/model_core" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Higher_Types +
  description "
    Seeded Henkin semantics for the stabilized Boolean classifier cycle.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Model_Core

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Background
    in "theories/goodman/models/hol_zf_boolean_probe/background" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Model_Core +
  description "
    PP, unique fundamentality, and zeroary and unary Recombination in the
    stabilized Boolean classifier-cycle model.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Background

session Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Finite_Model
    in "theories/goodman/models/hol_zf_boolean_probe/finite_model" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Background +
  description "
    Verification of the finite Boolean classifier-cycle package, including
    PP, Recombination, logical purity instances, and application closure.
  "
  options [timeout = 60]
  sessions
    Goodman_CEVplus_Finite_Fragment_Model_Program
theories
  Bacon_PP_ZF_Tree_Boolean_Probe_Finite_Model

session Higher_Order_Metaphysics_PP_ZF_Classifier_Stabilization
    in "theories/goodman/models/hol_zf_boolean_probe/stabilization" =
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Finite_Model +
  description "
    A reusable absorption criterion for classifier-generated unary values,
    instantiated by the verified Boolean classifier-cycle model.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Classifier_Stabilization

session Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Probe
    in "theories/goodman/models/hol_zf_boolean_probe/modal_boolean" =
    Higher_Order_Metaphysics_PP_ZF_Classifier_Stabilization +
  description "
    Modal-Boolean closure of the stabilized classifier stock and a test of
    the invariant-stock classifier absorption theorem.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Modal_Boolean_Probe

session Higher_Order_Metaphysics_PP_ZF_Multi_Family_Absorption
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family" =
    Higher_Order_Metaphysics_PP_ZF_Classifier_Stabilization +
  description "
    Simultaneous absorption of finitely many classifier-generated family
    probes, characterized by the complete matrix of cross-family collisions.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Family_Absorption

session Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Necessity
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family_necessity" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Absorption +
  description "
    Necessity half of the cross-collision criterion: a stabilized family
    probe forces every newly admitted cross-collision to belong to the old
    unary stock.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Family_Collision_Necessity

session Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Sufficiency
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family_sufficiency" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Necessity +
  description "
    Sufficiency half of the cross-collision criterion: if every newly admitted
    cross-collision was already in the unary stock, reevaluation leaves the
    selected family probe unchanged.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Family_Collision_Sufficiency

session Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Characterization
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family_characterization" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Sufficiency +
  description "
    Exact individual and simultaneous characterizations of classifier-probe
    stabilization by absorption of the complete cross-collision matrix.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Family_Collision_Characterization

session Higher_Order_Metaphysics_PP_ZF_Multi_Family_Off_Diagonal
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family_off_diagonal" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Characterization +
  description "
    For diagonally reflexive families, simultaneous classifier-probe
    stabilization is reduced exactly to absorption of the off-diagonal
    cross-family collisions.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Family_Off_Diagonal

session Higher_Order_Metaphysics_PP_ZF_Symmetrized_Pair_Simultaneous_Absorption
    in "theories/goodman/models/hol_zf_boolean_probe/multi_family_symmetrized_pair" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Off_Diagonal +
  description "
    Concrete simultaneous stabilization of the symmetrized-singleton family
    and its complemented family over Bacon's exact closed-logical unary stock.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Symmetrized_Pair_Simultaneous_Absorption

session Higher_Order_Metaphysics_PP_ZF_Symmetrized_Singleton_Cross_Collision
    in "theories/goodman/models/hol_zf_boolean_probe/symmetrized_singleton_cross" =
    Higher_Order_Metaphysics_PP_ZF_Symmetrized_Pair_Simultaneous_Absorption +
  description "
    The classifier probe generated by the symmetrized-singleton family is
    complement-invariant and therefore cannot collide with a value of the
    injective singleton family.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Symmetrized_Singleton_Cross_Collision

session Higher_Order_Metaphysics_PP_ZF_Singleton_Symmetrized_Pair
    in "theories/goodman/models/hol_zf_boolean_probe/singleton_symmetrized_pair" =
    Higher_Order_Metaphysics_PP_ZF_Symmetrized_Singleton_Cross_Collision +
  description "
    Simultaneous stabilization of the genuinely distinct singleton-family and
    symmetrized-singleton classifier probes.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Singleton_Symmetrized_Pair

session Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Stock_Probe
    in "theories/goodman/models/hol_zf_boolean_probe/indexed_family_stock" =
    Higher_Order_Metaphysics_PP_ZF_Singleton_Symmetrized_Pair +
  description "
    Stock-parametric probes for higher-order indexed families and the
    admissible unary stock obtained by adjoining all semantic probe sections.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Indexed_Family_Stock_Probe

session Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Collision
    in "theories/goodman/models/hol_zf_boolean_probe/indexed_family_collision" =
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Stock_Probe +
  description "
    Exact stabilization criterion for a uniformly indexed higher-order family:
    all semantic probe sections stabilize exactly when their collision matrix
    is absorbed; diagonal reflexivity reduces this to quotient-off-diagonal
    collisions.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Indexed_Family_Collision

session Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Anchor
    in "theories/goodman/models/hol_zf_boolean_probe/indexed_family_anchor" =
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Collision +
  description "
    Reusable true- and false-anchor criteria: one proposition with a uniform
    probe truth value absorbs the complete indexed collision matrix whenever
    that value reflects family values into the old unary stock.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Indexed_Family_Anchor

session Higher_Order_Metaphysics_PP_ZF_Indexed_Conjunctive_Singleton
    in "theories/goodman/models/hol_zf_boolean_probe/indexed_conjunctive_singleton" =
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Anchor +
  description "
    A genuinely proposition-indexed singleton family whose complete semantic
    section enlargement stabilizes: testing a collision at falsity forces the
    colliding family parameter to be necessarily false and hence already in
    Bacon's closed-logical unary stock.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Indexed_Conjunctive_Singleton

session Higher_Order_Metaphysics_PP_ZF_Indexed_Equivalence_Singleton
    in "theories/goodman/models/hol_zf_boolean_probe/indexed_equivalence_singleton" =
    Higher_Order_Metaphysics_PP_ZF_Indexed_Conjunctive_Singleton +
  description "
    A proposition-indexed family without a uniform anchor.  Each probe section
    is a symmetrized-singleton value, whose complement invariance excludes
    collision with every generated singleton value, so the complete indexed
    section enlargement stabilizes.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Indexed_Equivalence_Singleton

session Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/multi_indexed_family_stock" =
    Higher_Order_Metaphysics_PP_ZF_Indexed_Equivalence_Singleton +
  description "
    The admissible unary-stock enlargement generated simultaneously by all
    semantic sections of several indexed family builders, allowing a distinct
    object-language index type for each finite application-component tag.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Indexed_Family_Stock

session Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Collision
    in "theories/goodman/models/hol_zf_boolean_probe/multi_indexed_family_collision" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Stock +
  description "
    Exact individual and simultaneous stabilization theorems for heterogeneous
    indexed families: the complete cross-family, cross-index collision matrix
    is the sole obstruction.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Indexed_Family_Collision

session Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Off_Diagonal
    in "theories/goodman/models/hol_zf_boolean_probe/multi_indexed_family_off_diagonal" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Collision +
  description "
    For diagonally reflexive heterogeneous indexed families, the simultaneous
    criterion reduces exactly to collisions between different family tags or
    inequivalent semantic indices within one tag.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Indexed_Family_Off_Diagonal

session Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Conjunctive_Equivalence
    in "theories/goodman/models/hol_zf_boolean_probe/multi_indexed_conj_equiv" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Off_Diagonal +
  description "
    Simultaneous stabilization of two infinite proposition-indexed section
    families.  The complete 2x2 collision matrix is discharged jointly by the
    falsity-anchor and complement-symmetry mechanisms.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Multi_Indexed_Conjunctive_Equivalence

session Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Singleton
    in "theories/goodman/models/hol_zf_boolean_probe/operator_indexed_singleton" =
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Conjunctive_Equivalence +
  description "
    The first unary-operator-indexed family.  Its classifier probe is
    eliminated exactly as the closed logical operator mapping F and p to the
    settledness of F(p), exposing the next higher-type collision problem.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Operator_Indexed_Singleton

session Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Collision
    in "theories/goodman/models/hol_zf_boolean_probe/operator_indexed_collision" =
    Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Singleton +
  description "
    Semantic realization of every persistent proposition as an exact
    settledness profile, used to construct the first operator-indexed
    nonabsorbed classifier collision.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Operator_Indexed_Collision

session Higher_Order_Metaphysics_PP_ZF_Iterated_Stabilization
    in "theories/goodman/models/hol_zf_boolean_probe/iterated_stabilization" =
    Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Collision +
  description "
    Generic single- and multi-family two-stage stabilization theorems.  If the
    old indexed probe ranges cover every generated family value, the first
    enlargement absorbs all values and the second enlargement is a fixed
    point.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Iterated_Stabilization

session Higher_Order_Metaphysics_PP_ZF_Guarded_Indexed_Family
    in "theories/goodman/models/hol_zf_boolean_probe/guarded_indexed_family" =
    Higher_Order_Metaphysics_PP_ZF_Iterated_Stabilization +
  description "
    Purity-guarded indexed probe-section enlargement, matching the antecedent
    of CEV+ application closure.  For the operator-indexed singleton family,
    the next genuine obstruction is exactly a collision indexed by a pure
    operator; unary Recombination excludes the canonical semantic realizer.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Guarded_Indexed_Family

session Higher_Order_Metaphysics_PP_ZF_Guarded_Collision_Invariant
    in "theories/goodman/models/hol_zf_boolean_probe/guarded_collision_invariant" =
    Higher_Order_Metaphysics_PP_ZF_Guarded_Indexed_Family +
  description "
    Necessary behavior of a purity-guarded operator index whose settledness
    probe collides with a singleton family: its value at the parameter is
    settled, while its value at a one-world perturbation is unsettled.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Guarded_Collision_Invariant

session Higher_Order_Metaphysics_PP_ZF_Boundary_Singleton_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/boundary_singleton_stock" =
    Higher_Order_Metaphysics_PP_ZF_Guarded_Collision_Invariant +
  description "
    An admissible moving stock of singleton families and their pointwise
    negations indexed by propositions that are not currently equivalent to the
    fundamental proposition but become equivalent on a future cone.  The
    entire stock satisfies unary Recombination.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boundary_Singleton_Stock

session Higher_Order_Metaphysics_PP_ZF_Modal_Boundary_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/modal_boundary_stock" =
    Higher_Order_Metaphysics_PP_ZF_Boundary_Singleton_Stock +
  description "
    The modal-Boolean unary stock enlarged by the moving boundary singleton
    families and their pointwise negations.  With the modal-Boolean moving
    seed, the combined stock remains admissible, negation-closed, and satisfies
    unary Recombination at every world.
  "
  options [timeout = 60]
  sessions
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Probe
theories
  Bacon_PP_ZF_Tree_Modal_Boundary_Stock

session Higher_Order_Metaphysics_PP_ZF_Boundary_Operator_Probe
    in "theories/goodman/models/hol_zf_boolean_probe/boundary_operator_probe" =
    Higher_Order_Metaphysics_PP_ZF_Modal_Boundary_Stock +
  description "
    Exact calculation of the operator-indexed singleton-family classifier
    probe over the moving boundary stock and over its union with the
    modal-Boolean stock.  The remaining cyclic value is isolated as the
    disjunction of modal-Boolean singleton membership and the condition that
    the operator output lies on the moving fundamental boundary.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boundary_Operator_Probe

session Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Nonabsorption
    in "theories/goodman/models/hol_zf_boolean_probe/boundary_probe_nonabsorption" =
    Higher_Order_Metaphysics_PP_ZF_Boundary_Operator_Probe +
  description "
    The first classifier probe generated by the moving boundary stock, at the
    identity operator, is neither a boundary singleton family nor the
    pointwise negation of one.  Thus the boundary stock preserves
    Recombination but does not itself stabilize the next classifier cycle.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boundary_Probe_Nonabsorption

session Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Recombination
    in "theories/goodman/models/hol_zf_boolean_probe/boundary_probe_recombination" =
    Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Nonabsorption +
  description "
    Exact Recombination criterion for the first genuinely new boundary probe.
    The probe itself is harmless; its pointwise negation is safe exactly when
    every current moving seed later lies on the boundary of a future seed.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Boundary_Probe_Recombination

session Higher_Order_Metaphysics_PP_ZF_Recurrent_Generic_Seed
    in "theories/goodman/models/hol_zf_boolean_probe/recurrent_generic_seed" =
    Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Recombination +
  description "
    A strengthened countable generic-seed construction.  All diagonal coding
    cones are placed below the left branch, while the root is true and the
    right cone is empty.  The witness still satisfies Recombination for every
    operator in the countable equivariant stock and its cone transports satisfy
    the boundary-recurrence condition needed by the next cyclic enlargement.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Recurrent_Generic_Seed

session Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/recurrent_probe_stock" =
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Generic_Seed +
  description "
    The modal-Boolean stock, the recurrent moving-boundary singleton stock,
    and the first generated boundary probe together with its pointwise
    negation form an admissible, negation-closed unary stock satisfying
    Recombination at every world.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Recurrent_Probe_Stock

session Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stabilization
    in "theories/goodman/models/hol_zf_boolean_probe/recurrent_probe_stabilization" =
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stock +
  description "
    The first generated boundary probe and its pointwise negation do not alter
    the classifier on singleton-family queries at any world.  This gives the
    exact one-step stabilization theorem for the first classifier-bearing
    cyclic enlargement.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Recurrent_Probe_Stabilization

session Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Antipatching
    in "theories/goodman/models/hol_zf_boolean_probe/recurrent_probe_antipatching" =
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stabilization +
  description "
    Exact seed obligations for the full operator-indexed classifier range.
    Boundary recurrence makes the negation of each generated section
    Recombination-safe; an anti-patching witness makes the section itself
    Recombination-safe.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Recurrent_Probe_Antipatching

session Higher_Order_Metaphysics_PP_ZF_Recurrent_Identity_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/recurrent_identity_stock" =
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Antipatching +
  description "
    The current unary stock enlarged by the complete identity-indexed
    classifier output, not merely its boundary disjunct.  The enlargement and
    its pointwise negation are admissible, negation-closed, and satisfy
    Recombination at every world.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Recurrent_Identity_Stock

session Higher_Order_Metaphysics_PP_ZF_Dual_Recurrent_Generic_Seed
    in "theories/goodman/models/hol_zf_boolean_probe/dual_recurrent_generic_seed" =
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Antipatching +
  description "
    A strengthened countable generic-seed construction with two guarded
    self-similar cones.  It preserves all diagonal Recombination witnesses and
    simultaneously supplies boundary recurrence for identity and negation.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Recurrent_Generic_Seed

session Higher_Order_Metaphysics_PP_ZF_Dual_Identity_Negation_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/dual_identity_negation_stock" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Recurrent_Generic_Seed +
  description "
    The dual-recurrent modal-boundary stock enlarged by the complete
    classifier sections for identity and negation, together with their
    pointwise negations.  The full package is admissible, negation-closed, and
    satisfies Recombination at every world.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Identity_Negation_Stock

session Higher_Order_Metaphysics_PP_ZF_Dual_Constant_Absorption
    in "theories/goodman/models/hol_zf_boolean_probe/dual_constant_absorption" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Identity_Negation_Stock +
  description "
    The full classifier sections indexed by the constant-truth and
    constant-falsity operators collapse to constant truth.  Their pointwise
    negations collapse to constant falsity, so all four values are already
    absorbed by the modal-Boolean base stock.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Constant_Absorption

session Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Frontier
    in "theories/goodman/models/hol_zf_boolean_probe/dual_modal_frontier" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Constant_Absorption +
  description "
    The next classifier-bearing cyclic package, indexed by necessity and
    possibility.  Guarded identity and negation cones discharge the exact
    boundary-recurrence and anti-patching obligations, proving that all four
    generated sections preserve Recombination.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Modal_Frontier

session Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/dual_modal_stock" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Frontier +
  description "
    The application-closed enlargement by the full necessity and possibility
    classifier sections and their pointwise negations.  The resulting stock
    is admissible, negation-closed, and satisfies Recombination.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Modal_Stock

session Higher_Order_Metaphysics_PP_ZF_Dual_Negated_Modal_Frontier
    in "theories/goodman/models/hol_zf_boolean_probe/dual_negated_modal_frontier" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Stock +
  description "
    The remaining modal variants indexed by necessary falsity and possible
    falsity.  The guarded identity cone discharges their recurrence and
    anti-patching obligations, so both generated sections and both pointwise
    complements preserve Recombination.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Negated_Modal_Frontier

session Higher_Order_Metaphysics_PP_ZF_Dual_Full_Modal_Stock
    in "theories/goodman/models/hol_zf_boolean_probe/dual_full_modal_stock" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Negated_Modal_Frontier +
  description "
    The complete four-index modal enlargement by necessity, possibility,
    necessary falsity, possible falsity, and all pointwise complements.
    The stock is admissible, negation-closed, and satisfies Recombination.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Full_Modal_Stock

session Higher_Order_Metaphysics_PP_ZF_Dual_Quantified_Absorption
    in "theories/goodman/models/hol_zf_boolean_probe/dual_quantified_absorption" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Full_Modal_Stock +
  description "
    The six higher-order quantified unary operators are identified exactly
    with necessity, necessary falsity, possible falsity, possibility,
    constant falsity, and constant truth in the recurrent tree semantics.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Quantified_Absorption

session Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Depth_Two
    in "theories/goodman/models/hol_zf_boolean_probe/dual_modal_depth_two" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Quantified_Absorption +
  description "
    The genuine modal-depth-two alternations, box-diamond and diamond-box.
    Their complement fixed-point obstructions provide the base case for
    extending the recurrent classifier stock beyond modal depth one.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Modal_Depth_Two

session Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Normalization
    in "theories/goodman/models/hol_zf_boolean_probe/dual_modal_normalization" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Depth_Two +
  description "
    The finite S4 modal-composition monoid.  The two remaining depth-three
    forms, box-diamond-box and diamond-box-diamond, are stabilized before
    proving normalization of all positive modal words.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Modal_Normalization

session Higher_Order_Metaphysics_PP_ZF_Dual_Boolean_Closure
    in "theories/goodman/models/hol_zf_boolean_probe/dual_boolean_closure" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Normalization +
  description "
    The exact Boolean-closure frontier for the recurrent pure stock.
    Conjunction preserves Recombination safety outright; disjunction is
    equivalent to a joint anti-patching condition on the fundamental seed.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Boolean_Closure

session Higher_Order_Metaphysics_PP_ZF_Dual_Pair_Grafting
    in "theories/goodman/models/hol_zf_boolean_probe/dual_pair_grafting" =
    Higher_Order_Metaphysics_PP_ZF_Dual_Boolean_Closure +
  description "
    Local boundary grafts for the remaining mixed-sign pairs.  A left cone
    supplies a prescribed fundamental boundary while a reserved right cone
    preserves all previously met Recombination obligations.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Dual_Pair_Grafting

session Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Higher_Types
    in "theories/goodman/models/hol_zf_boolean_probe/modal_higher_types" =
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Probe +
  description "
    Higher-type pure stocks forced by the modal-Boolean classifier cycle.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Modal_Boolean_Higher_Types

session Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Model
    in "theories/goodman/models/hol_zf_boolean_probe/modal_model" =
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Higher_Types +
  description "
    Seeded Henkin semantics for the stabilized modal-Boolean classifier cycle.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Modal_Boolean_Model

session Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Background
    in "theories/goodman/models/hol_zf_boolean_probe/modal_background" =
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Model +
  description "
    PP, unique fundamentality, and zeroary and unary Recombination in the
    stabilized modal-Boolean classifier-cycle model.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Modal_Boolean_Background

session Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Finite_Model
    in "theories/goodman/models/hol_zf_boolean_probe/modal_finite_model" =
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Background +
  description "
    A verified finite package extending the first classifier cycle by the
    pure pointwise-necessitation transformer.
  "
  options [timeout = 60]
theories
  Bacon_PP_ZF_Tree_Modal_Boolean_Finite_Model

session Higher_Order_Metaphysics_PP_ZF_Truth_Functions
    in "theories/goodman/models/fragments/truth_functions" =
    Higher_Order_Metaphysics_PP_ZF_Secondary +
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
  Bacon_PP_ZF_Modal_Word_Normalization

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
  Bacon_PP_ZF_T6_Builder_Enlargement

session Goodman_CEVplus_Canonical in "theories/goodman/cevplus" =
    Goodman_CEVplus +
  description "
    Canonical and Henkin metatheory for Goodman's CEV+ formulation.
  "
  options [timeout = 120]
theories
  Bacon_PP_Fresh_Finite_Fragment
  Bacon_PP_Finite_Application_Graph
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

session Goodman_CEVplus_Finite_Fragment_Model_Program
    in "theories/goodman/bridges/finite_fragments" =
    Higher_Order_Metaphysics_PP_Frontier +
  description "
    Semantic interface for the compactness attack on Goodman's
    Recombination-only Purity-of-Pure question.
  "
  options [timeout = 60]
  sessions
    Goodman_CEVplus_Canonical
theories
  Bacon_PP_Finite_Fragment_Model_Program

session Goodman_CEVplus_Finite_First_Cyclic_Model
    in "theories/goodman/bridges/finite_cyclic_model" =
    Higher_Order_Metaphysics_PP_ZF_Secondary +
  description "
    A tailored HOL-ZF model for the first classifier-bearing cyclic
    finite package in the compactness attack on Goodman's question.
  "
  options [timeout = 60]
  sessions
    Goodman_CEVplus_Finite_Fragment_Model_Program
    Higher_Order_Metaphysics_PP_ZF_T6_Diagonal
theories
  Bacon_PP_ZF_Finite_First_Cyclic_Package
  Bacon_PP_ZF_Two_Component_Assembly
  Bacon_PP_ZF_T6_Collision_Carrier
