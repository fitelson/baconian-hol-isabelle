theory Audit_Goodman_Complete
  imports
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_T6_WI_Master
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_T8_Growth
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_T9
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_Heredity_Advertised
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_QSS_Recombination_Bridge
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_Granularity_QLN
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1_Complete
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1_Henkin
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1_Fn60
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M2
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M3_Complete
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M4
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M5
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M5_Collision
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M5_Existential_Invertibles
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M5_Orbit_Avoidance
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M6
    Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M7_Invariant_Reachability
    Higher_Order_Metaphysics_PP.Bacon_PP_Heredity_Semantics
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Bacon_10_1
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Bacon_QLN
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_M1_Fn59
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_M1_Fn60
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_M5_Rebuild
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_M7
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Repaired_Central_Stock
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_CEV_Soundness
    Higher_Order_Metaphysics_PP_ZF_Model.Bacon_PP_ZF_Exact_Completeness
    Higher_Order_Metaphysics_PP_ZF_Model.Bacon_PP_ZF_Exact_L2_Child_Variation
    Goodman_CEVplus_Canonical.Bacon_PP_Fresh_Finite_Fragment
    Goodman_CEVplus_ZF_Bridge.Bacon_PP_Fresh_ZF_Fragment_Bridge
begin

section \<open>Kernel theorem-object audit\<close>

ML \<open>
fun require_clean (name, thm) =
  let
    val oracles = Thm_Deps.all_oracles [thm]
    val oracle_names = map (fn ((n, _), _) => n) oracles
    val hyps = Thm.hyps_of thm
    val tpairs = Thm.tpairs_of thm
    val shyps = Thm.shyps_of thm
    val line = name
      ^ ": oracles=" ^ string_of_int (length oracles)
      ^ (if null oracle_names then ""
         else " [" ^ commas oracle_names ^ "]")
      ^ " hyps=" ^ string_of_int (length hyps)
      ^ " tpairs=" ^ string_of_int (length tpairs)
      ^ " shyps=" ^ string_of_int (length shyps)
    (* Sort hypotheses are ordinary kernel-checked polymorphism, not
       undischarged logical assumptions.  T9's cardinal theorems carry the
       expected single type-sort hypothesis. *)
    val clean =
      null oracles andalso null hyps andalso null tpairs
  in
    if clean then
      (true, line ^
        (if null shyps then " [CLEAN]"
         else " [CLEAN; SORT-POLYMORPHIC]"))
    else (false, line ^ " [PROBLEM]")
  end

val targets = [
  (* Scope and semantic-bridge maintenance. *)
  ("higher bridge unary equality",
    @{thm pp_v_equal_unary_root_iff}),
  ("higher bridge classifier equality",
    @{thm pp_v_equal_classifier_root_iff}),
  ("zeroary-unary QLN package exact scope",
    @{thm pp_full_QLN_background_axioms_exact_scope}),
  ("object-language unary Exhaustion instance",
    @{thm CEV_axiom_unary_exhaustion_instance}),
  ("object-language unary QLN equivalence instance",
    @{thm CEV_axiom_unary_QLN_instance}),
  ("full-QLN granularity iff truth uniformity",
    @{thm CEV_full_QLN_PP_granularity_iff_truth_uniform}),
  ("proposition-valued Modalized Functionality schema",
    @{thm CEV_proves_proposition_valued_modalized_functionality_schema}),
  ("Goodman consistency iff every finite fragment is consistent",
    @{thm pp_recombination_axiom_consistency_iff_finite_fragments}),
  ("negative answer iff a finite inconsistent core exists",
    @{thm pp_recombination_axiom_negative_answer_iff_finite_inconsistent_core}),

  (* Object-language suite. *)
  ("T1 pure propositions", @{thm CEV_Goodman_T1_pure_propositions_extreme}),
  ("T1 biconditional classification",
    @{thm CEV_Goodman_T1_biconditional_operator_classification}),
  ("T1 WI collapse", @{thm CEV_Goodman_T1_WI_collapses_to_Inv}),
  ("T2a group closure", @{thm CEV_fun_prime_under_group_member}),
  ("T2a negation closure", @{thm CEV_fun_prime_under_negation}),
  ("T2b nontriviality", @{thm CEV_Goodman_T2b}),
  ("T2c attainment", @{thm CEV_Goodman_T2c}),
  ("T2d possible purity", @{thm CEV_Goodman_T2d}),
  ("T2e noncontingency", @{thm CEV_Goodman_T2e}),
  ("T2f six-way distinctness", @{thm CEV_Goodman_T2f}),
  ("T3 modal core", @{thm CEV_T3_modal_core}),
  ("T3 advertised plus Exhaustion",
    @{thm CEV_Goodman_T3_advertised_with_exhaustion}),
  ("T3 rigidity repair", @{thm CEV_Goodman_T3_heredity_rigid}),
  ("T3 unrestricted rigidity refutation",
    @{thm CEV_unrestricted_rigidity_refuted}),
  ("T3 modal abstraction countermodel",
    @{thm Goodman_T3_advertised_modal_abstraction_countermodel}),
  ("T4 higher-type diagonal", @{thm CEV_Goodman_T4}),
  ("T5 proliferation", @{thm CEV_Goodman_T5}),
  ("T6 Inv", @{thm CEV_Goodman_T6_Inv}),
  ("T6 TU", @{thm CEV_Goodman_T6_TU}),
  ("T6 WI", @{thm CEV_Goodman_T6_WI}),
  ("T6 WI direct master family",
    @{thm CEV_Goodman_T6_WI_advertised_master_claim_direct}),
  ("T6 RS", @{thm CEV_Goodman_T6_RS}),
  ("T7a parameter", @{thm CEV_Goodman_T7a_parameter}),
  ("T7a closed", @{thm CEV_Goodman_T7a}),
  ("T8a base kinds", @{thm CEV_Goodman_T8a}),
  ("T8b kind uniqueness", @{thm CEV_Goodman_T8_kind_uniqueness}),
  ("T8c witness-parametric growth", @{thm CEV_Goodman_T8c}),
  ("T8c closed growth", @{thm CEV_Goodman_T8c_closed}),
  ("T9 infinite product absorption", @{thm pp_T9_Times_ordLeq_infinite}),
  ("T9 PC specification injection",
    @{thm pp_T9_PC_specification_injective}),
  ("T9 orbit-fibre code injective",
    @{thm pp_T9_orbit_fibre_code(1)}),
  ("T9 orbit-fibre code range",
    @{thm pp_T9_orbit_fibre_code(2)}),
  ("T9 global orbit code injective",
    @{thm pp_T9_global_orbit_code(1)}),
  ("T9 global orbit code typed",
    @{thm pp_T9_global_orbit_code(2)}),
  ("T9 counting bound", @{thm pp_T9_counting_bound}),
  ("T9 cardinal dichotomy", @{thm pp_T9_cardinal_dichotomy}),
  ("T9 PC cardinal dichotomy", @{thm pp_T9_PC_cardinal_dichotomy}),
  ("T9 advertised PC-orbit dichotomy",
    @{thm pp_T9_advertised_PC_orbit_dichotomy}),

  (* Recombination, QSS, and repaired central-stock translations. *)
  ("Recombination-only QSS core",
    @{thm CEV_QSS_modal_core_from_recombination}),
  ("QSS with zeroary Exhaustion",
    @{thm CEV_QSS_from_recombination_with_zeroary_exhaustion}),
  ("fun-prime existence from QSS and unique fundamentality",
    @{thm CEV_exists_fun_prime_from_QSS_and_unique_fundamentality}),
  ("repaired central T6 Inv",
    @{thm CEV_Goodman_T6_Inv_repaired_central_stock}),
  ("repaired central T6 TU",
    @{thm CEV_Goodman_T6_TU_repaired_central_stock}),
  ("repaired central T6 WI",
    @{thm CEV_Goodman_T6_WI_repaired_central_stock}),
  ("repaired central T6 RS",
    @{thm CEV_Goodman_T6_RS_repaired_central_stock}),
  ("repaired central stock forces L2 or TU failure",
    @{thm henkin_action_model.repaired_central_stock_forces_L2_or_TU_failure}),
  ("repaired central stock has explicit L2 or TU failure",
    @{thm henkin_action_model.repaired_central_stock_has_explicit_L2_or_TU_failure}),

  (* Model-theoretic M1--M7 suite. *)
  ("M1 bottom purity", @{thm pp_M1_bottom_purity_is_noncontingency}),
  ("M1 footnote-59 liar purity", @{thm pp_M1_fn59_liar_pure}),
  ("M1 footnote-59 contradiction",
    @{thm pp_M1_fn59_unique_fun_diagonal_contradiction_sem}),
  ("M1 arbitrary-Henkin exact denotation",
    @{thm goodman_M1_henkin_model.M1_fn59_liar_denotation}),
  ("M1 arbitrary-Henkin QSS denotation",
    @{thm goodman_M1_henkin_model.M1_fn59_QSS_denotation}),
  ("M1 arbitrary-Henkin unique-fundamentality denotation",
    @{thm goodman_M1_henkin_model.M1_unique_fundamental_denotation}),
  ("M1 arbitrary-Henkin diagonal contradiction",
    @{thm goodman_M1_henkin_model.M1_fn59_diagonal_contradiction}),
  ("M1 arbitrary-Henkin PP failure",
    @{thm goodman_M1_henkin_model.M1_fn59_PP_failure}),
  ("M1 arbitrary-Henkin full-QLN plus Purity-of-Fun exclusion",
    @{thm goodman_M1_henkin_model.no_full_QLN_model_with_purity_of_fun}),
  ("M1 footnote-59 exact denotation",
    @{thm pp_t_moving_internal_parameters.pp_t_M1_fn59_liar_denotation}),
  ("M1 QSS exact denotation",
    @{thm pp_t_moving_internal_parameters.pp_t_M1_fn59_QSS_denotation}),
  ("M1 footnote-59 secondary tree-model contradiction",
    @{thm pp_t_moving_internal_parameters.pp_t_M1_fn59_diagonal_contradiction}),
  ("M1 footnote-59 PP failure bridge",
    @{thm pp_t_moving_internal_parameters.pp_t_M1_fn59_PP_failure}),
  ("M1 footnote-60 identity join",
    @{thm pp_M1_fn60_identity_join_exact_extension}),
  ("M1 footnote-60 exact diagnosis",
    @{thm pp_M1_fn60_exact_diagnosis}),
  ("M1 footnote-60 full-domain classifier",
    @{thm pp_t_M1_fn60_classifier_in_full_domain}),
  ("M1 footnote-60 exact extension in appendix model",
    @{thm pp_t_M1_fn60_classifier_exact_extension}),
  ("M1 footnote-60 Pure interpretation",
    @{thm pp_t_M1_fn60_is_Pure_interpretation}),
  ("M1 footnote-60 PP equivalence",
    @{thm pp_t_M1_fn60_global_PP_iff_classifier_pure_at_root}),
  ("M2 classifier bijection", @{thm pp_M2_classifier_bijection}),
  ("M2 cardinal obstruction",
    @{thm pp_M2_invariant_operators_outnumber_propositions}),
  ("M2 QSS failure", @{thm pp_M2_invariance_QSS_fails}),
  ("M3 free generator",
    @{thm pp_M3_countable_invariant_stock_has_free_generator}),
  ("M3 fun-prime iff free", @{thm pp_M3_fun_prime_iff_free}),
  ("M3 logical fun-prime iff free",
    @{thm pp_M3_logical_fun_prime_iff_free}),
  ("M3 fun-prime has extreme views",
    @{thm pp_M3_fun_prime_has_extreme_views}),
  ("M3 fun-prime generator",
    @{thm pp_M3_countable_boolean_stock_has_fun_prime}),
  ("M3 product meagerness",
    @{thm pp_M3_fun_prime_class_is_product_meager}),
  ("M4 conditional-stock hereditary preimage",
    @{thm pp_M4_fun_prime_preimage}),
  ("M4 conditional-stock outside fundamental orbit",
    @{thm pp_M4_explicit_fun_prime_outside_fundamental_orbit}),
  ("M4 conditional-stock semantic heredity",
    @{thm pp_stock_fun_prime_hereditary}),
  ("M5 exotic involution", @{thm pp_M5_exotic_involution}),
  ("M5 not truth-uniform", @{thm pp_M5_exotic_not_truth_uniform}),
  ("M5 not biconditional", @{thm pp_M5_exotic_not_biconditional}),
  ("M5 diagonal pair avoids orbit",
    @{thm pp_M5_diagonal_pair_avoids_orbit}),
  ("M5 diagonal pair has no proper echo",
    @{thm pp_M5_diagonal_no_echo}),
  ("M5 diagonal transposition first member",
    @{thm pp_M5_diagonal_exotic_s}),
  ("M5 diagonal transposition second member",
    @{thm pp_M5_diagonal_exotic_s'}),
  ("M5 diagonal transposition fixes candidate",
    @{thm pp_M5_diagonal_exotic_fixes_R}),
  ("M5 diagonal transposition nonidentity",
    @{thm pp_M5_diagonal_exotic_not_identity}),
  ("M5 diagonal transposition invariant",
    @{thm pp_M5_diagonal_exotic_is_function_space_invariant}),
  ("M5 pre-rebuild QSS obstruction",
    @{thm pp_M5_pre_rebuild_QSS_obstruction}),
  ("M5 collision method",
    @{thm CEV_Goodman_M5_collision}),
  ("M5 reversible operators are injective",
    @{thm CEV_M5_reversible_injective}),
  ("M5 displayed collision operator is not reversible",
    @{thm CEV_Goodman_M5_collision_operator_not_reversible}),
  ("Bacon Theorem 10.1 at the appendix-developed scope",
    @{thm pp_e_Bacon_10_1}),
  ("Bacon zeroary QLN verification",
    @{thm pp_t_generic_zeroary_QLN_gvalid}),
  ("Bacon unary QLN verification",
    @{thm pp_t_generic_unary_QLN_gvalid}),
  ("Bacon QLN verification for unique fundamental proposition",
    @{thm pp_t_Bacon_QLN_unique_fundamental_proposition}),
  ("M5 rebuilt model with fixed operator",
    @{thm pp_t_M5_rebuild_with_fixed_unary_operator}),
  ("M5 rebuilt exotic involution",
    @{thm pp_t_M5_exotic_involution}),
  ("M5 rebuilt exotic violates TU",
    @{thm pp_t_M5_exotic_not_truth_uniform}),
  ("M5 rebuilt exotic violates WI",
    @{thm pp_t_M5_exotic_not_biconditional}),
  ("M5 rebuilt exotic denotation typed",
    @{thm pp_t_M5_exotic_den_typed}),
  ("M5 rebuilt exotic denotation cone-natural",
    @{thm pp_t_M5_exotic_den_cone_natural}),
  ("M5 rebuilt exotic denotation self-inverse",
    @{thm pp_t_M5_exotic_den_involution}),
  ("M5 exotic pure in rebuilt stock",
    @{thm pp_t_M5_exotic_pure_in_rebuilt_definable_stock}),
  ("M5 rebuilt fundamental supplies Recombination",
    @{thm pp_t_M5_root_fundamental_recombines}),
  ("M5 rebuilt fundamental is fun-prime",
    @{thm pp_t_M5_root_fundamental_is_fun_prime}),
  ("M5 rebuilt fun-prime at every world",
    @{thm pp_t_M5_fundamental_at_is_fun_prime}),
  ("M5 full rebuilt background validity",
    @{thm pp_t_M5_full_rebuilt_background_gvalid}),
  ("M5 full rebuilt exotic certificate",
    @{thm pp_t_M5_full_rebuilt_exotic_certificate}),
  ("M5 full rebuilt model",
    @{thm pp_t_M5_full_rebuilt_model}),
  ("M6 conditional-stock substitution separation",
    @{thm pp_M6_fun_prime_separates_distinct_substitutions}),
  ("M6 conditional-stock single-coordinate failure",
    @{thm pp_M6_single_proposition_independence_fails}),
  ("M6 conditional-stock strict fun-prime pair",
    @{thm pp_M6_fun_prime_strict_pair}),
  ("M6 conditional-stock joint assignment obstruction",
    @{thm pp_M6_joint_assignment_blocked_by_inclusion}),
  ("M7 diagonal outside range", @{thm pp_t_M7_diagonal_outside_range}),
  ("M7 fundamental completeness failure",
    @{thm pp_t_M7_fundamental_completeness_fails}),
  ("M7 invariant reachability classifier",
    @{thm pp_M7_invariant_reachable_iff_classifier}),
  ("M7 universal invariant reachability iff orbit-map injection",
    @{thm pp_M7_all_invariant_reachable_iff_orbit_map_injective}),

  (* Exact-model L2 calibration on Bacon's natural-word action. *)
  ("exact-stock fun-prime existence", @{thm pp_e_exact_fun_prime_exists}),
  ("exact child-variation term belongs to the closed logical stock",
    @{thm pp_e_child_variation_in_exact_stock}),
  ("exact child-variation operator is surjective",
    @{thm pp_e_child_variation_surjective}),
  ("exact child-variation operator is noninjective",
    @{thm pp_e_child_variation_not_injective}),
  ("exact child-variation operator is right-cancellative",
    @{thm pp_e_exact_child_variation_right_cancellative}),
  ("exact child-variation operator is nonreversible",
    @{thm pp_e_child_variation_not_exact_reversible}),
  ("closed logical operator refutes exact L2",
    @{thm pp_e_child_variation_refutes_exact_L2}),
  ("closed logical operator refutes exact strong L2",
    @{thm pp_e_child_variation_refutes_exact_strong_L2}),
  ("exact individual Existence validity",
    @{thm pp_e_constants.pp_e_H_IndividualExistence_valid}),
  ("exact H soundness", @{thm pp_e_constants.pp_e_H_sound}),
  ("exact CEV soundness", @{thm pp_e_constants.pp_e_CEV_valid}),
  ("exact CEV base global soundness",
    @{thm pp_e_constants.pp_e_base_sound}),
  ("exact CEV vector-Equivalence soundness",
    @{thm pp_e_constants.pp_e_zeta_sound}),
  ("exact Bacon consistency representation",
    @{thm pp_e_Bacon_consistency_representation}),
  ("exact Bacon semantic frame-theory representation",
    @{thm pp_e_Bacon_exact_completeness}),
  ("fixed point answers Goodman",
    @{thm pp_t_cone_natural_enumerator.pp_t_term_basis_fixed_point_answers_Goodman}),

  (* Verified K-fragment model and fresh-stock bridge. *)
  ("K-fragment global validity",
    @{thm pp_t_constant_builder_fragment_PP_gvalid}),
  ("K-fragment consistency",
    @{thm pp_constant_builder_fragment_PP_axioms_consistent}),
  ("K-fragment inclusion in Goodman stock",
    @{thm pp_constant_builder_fragment_PP_axioms_subset_fresh_goodman}),
  ("Goodman five-purity-instance consistency",
    @{thm fresh_goodman_constant_builder_only_consistent}),
  ("K-fragment exact Goodman consistency",
    @{thm pp_constant_builder_fragment_is_goodman_consistent}),

  (* Verified conjunction-fragment model and fresh-stock bridge. *)
  ("conjunction-fragment global validity",
    @{thm pp_t_conjunction_fragment_PP_gvalid}),
  ("conjunction-fragment consistency",
    @{thm pp_conjunction_fragment_PP_axioms_consistent}),
  ("conjunction-fragment inclusion in Goodman stock",
    @{thm pp_conjunction_fragment_PP_axioms_subset_fresh_goodman}),
  ("Goodman six-purity-instance consistency",
    @{thm fresh_goodman_conjunction_only_consistent}),
  ("conjunction-fragment exact Goodman consistency",
    @{thm pp_conjunction_fragment_is_goodman_consistent}),

  (* Uniform binary truth-function model and fresh-stock bridge. *)
  ("binary truth-function fragment global validity",
    @{thm pp_t_binary_truth_fragment_PP_gvalid}),
  ("binary truth-function fragment consistency",
    @{thm pp_binary_truth_fragment_PP_axioms_consistent}),
  ("binary truth-function fragment inclusion in Goodman stock",
    @{thm pp_binary_truth_fragment_PP_axioms_subset_fresh_goodman}),
  ("Goodman binary-truth-purity consistency",
    @{thm fresh_goodman_binary_truth_only_consistent}),
  ("binary truth-function exact Goodman consistency",
    @{thm pp_binary_truth_fragment_is_goodman_consistent})
]

val results = map require_clean targets
val report = cat_lines (map #2 results)
val _ =
  if forall #1 results
  then writeln
    ("GOODMAN-COMPLETE-AUDIT-ALL-PRINCIPAL-THEOREMS-KERNEL-CLEAN\n"
      ^ report)
  else error ("GOODMAN-COMPLETE-AUDIT-PROBLEM\n" ^ report)
\<close>

end
