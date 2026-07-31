theory Bacon_PP_ZF_Tree_Boolean_Probe_Finite_Model
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Background.Bacon_PP_ZF_Tree_Boolean_Probe_Background
    Goodman_CEVplus_Finite_Fragment_Model_Program.Bacon_PP_Finite_Fragment_Model_Program
begin

section \<open>Logical purity instances\<close>

theorem pp_t_probe_successor_model_logical_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and closed_pure:
      "\<And>w. pp_t_probe_successor_model_pure \<sigma> w
        (pp_t_closed_den M)"
  shows "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule ProbeSuccessorModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  let ?\<rho> = "pp_t_list_env env"
  have empty_env: "pp_t_env_typed [] ?\<rho>"
    by (rule pp_t_empty_env_typed)
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_probe_successor_model_constants ?\<rho>
          (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
      pp_t_probe_successor_model_pure \<sigma> w
        (pp_t_eval pp_t_probe_successor_model_constants ?\<rho> M)"
    by (rule pp_t_probe_successor_model_eval_pure_holds[
      OF typed empty_env])
  have closed_domain:
      "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have eval_domain:
      "Elem
        (pp_t_eval pp_t_probe_successor_model_constants ?\<rho> M)
        (pp_t_domain \<sigma>)"
    using ProbeSuccessorModelConstants.pp_t_eval_type[
      OF typed empty_env]
    by (simp add: pp_t_dom_def)
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_closed_den M)
        (pp_t_eval pp_t_probe_successor_model_constants ?\<rho> M)"
    by (rule pp_t_probe_successor_model_closed_logical_eval_eqv[
      OF typed logical])
  have pure_eval:
      "pp_t_probe_successor_model_pure \<sigma> w
        (pp_t_eval pp_t_probe_successor_model_constants ?\<rho> M)"
    using pp_t_probe_successor_model_pure_admissible
      closed_domain eval_domain related closed_pure[of w]
    unfolding pp_t_predicate_admissible_def
    by (metis prefix_order.refl)
  show "pp_t_holds
      (ProbeSuccessorModelConstants.pp_t_den
        (pp_pure \<sigma> M) env) w"
    unfolding ProbeSuccessorModelConstants.pp_t_den_def
    using evaluation pure_eval by blast
qed

lemma pp_t_probe_successor_family_builder_closed_pure:
  "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_family_builder_type w
    (pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder))"
  unfolding pp_t_probe_successor_family_builder_den_def[symmetric]
  by (simp add: pp_t_probe_successor_family_builder_in_stock)

theorem pp_t_probe_successor_family_builder_purity_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_family_builder_type
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder))"
  by (rule pp_t_probe_successor_model_logical_purity_gvalid[
    OF pp_t_family_probe_builder_typed[
        OF pp_t_symmetrized_singleton_family_builder_typed]
      pp_t_family_probe_builder_logical[
        OF pp_t_symmetrized_singleton_family_builder_logical]
      pp_t_probe_successor_family_builder_closed_pure])

lemma pp_t_probe_successor_negator_closed_pure:
  "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_transformer_type w
    (pp_t_closed_den pp_t_unary_output_negator)"
  by (simp add: pp_t_probe_successor_transformer_stock_negator)

theorem pp_t_probe_successor_negator_purity_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_transformer_type
      pp_t_unary_output_negator)"
  by (rule pp_t_probe_successor_model_logical_purity_gvalid[
    OF pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical
      pp_t_probe_successor_negator_closed_pure])

lemma pp_t_probe_successor_conjunction_builder_closed_pure:
  "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_builder_type w
    pp_t_unary_output_conjunction_den"
  by (simp add:
      pp_t_probe_successor_conjunction_builder_in_stock)

theorem pp_t_probe_successor_conjunction_builder_purity_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_builder_type
      pp_t_unary_output_conjunction)"
  by (rule pp_t_probe_successor_model_logical_purity_gvalid[
    OF pp_t_unary_output_conjunction_typed
      pp_t_unary_output_conjunction_logical
      pp_t_probe_successor_conjunction_builder_closed_pure])

section \<open>Application closure\<close>

lemma pp_t_probe_successor_model_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_probe_successor_model_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_probe_successor_model_pure
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
          \<and> pp_t_probe_successor_model_pure \<sigma> w x
        \<longrightarrow>
        pp_t_probe_successor_model_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_probe_successor_model_family_application_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_classifier_type
      pp_t_boolean_probe_unary_type)"
proof (rule ProbeSuccessorModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeSuccessorModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_classifier_type
          pp_t_boolean_probe_unary_type) env) w"
    unfolding ProbeSuccessorModelConstants.pp_t_den_def
      pp_t_probe_successor_model_application_closure_holds_iff
    using pp_t_probe_successor_model_family_application
    by blast
qed

theorem pp_t_probe_successor_model_transformer_application_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_unary_type
      pp_t_boolean_probe_unary_type)"
proof (rule ProbeSuccessorModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeSuccessorModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_unary_type) env) w"
    unfolding ProbeSuccessorModelConstants.pp_t_den_def
      pp_t_probe_successor_model_application_closure_holds_iff
    using pp_t_probe_successor_model_transformer_application
    by blast
qed

theorem pp_t_probe_successor_model_builder_application_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_unary_type
      pp_t_boolean_probe_transformer_type)"
proof (rule ProbeSuccessorModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeSuccessorModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_transformer_type) env) w"
    unfolding ProbeSuccessorModelConstants.pp_t_den_def
      pp_t_probe_successor_model_application_closure_holds_iff
    using pp_t_probe_successor_model_builder_application
    by blast
qed

section \<open>The finite Boolean classifier-cycle package\<close>

definition pp_finite_boolean_classifier_cycle_package ::
    "oterm set"
where
  "pp_finite_boolean_classifier_cycle_package =
    pp_recombination_fixed_axioms
    \<union> {
      pp_pure pp_t_boolean_probe_family_builder_type
        (pp_t_family_probe_builder
          pp_t_symmetrized_singleton_family_builder),
      pp_pure pp_t_boolean_probe_transformer_type
        pp_t_unary_output_negator,
      pp_pure pp_t_boolean_probe_builder_type
        pp_t_unary_output_conjunction,
      pp_application_closure
        pp_t_boolean_probe_classifier_type
        pp_t_boolean_probe_unary_type,
      pp_application_closure
        pp_t_boolean_probe_unary_type
        pp_t_boolean_probe_unary_type,
      pp_application_closure
        pp_t_boolean_probe_unary_type
        pp_t_boolean_probe_transformer_type}"

lemma pp_finite_boolean_classifier_cycle_package_finite:
  "finite pp_finite_boolean_classifier_cycle_package"
  unfolding pp_finite_boolean_classifier_cycle_package_def
    pp_recombination_fixed_axioms_def
  by simp

lemma pp_finite_boolean_classifier_cycle_package_subset:
  "pp_finite_boolean_classifier_cycle_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have family_purity:
      "pp_pure pp_t_boolean_probe_family_builder_type
          (pp_t_family_probe_builder
            pp_t_symmetrized_singleton_family_builder)
        \<in> pp_purity_schema"
    using pp_t_family_probe_builder_typed[
        OF pp_t_symmetrized_singleton_family_builder_typed]
      pp_t_family_probe_builder_logical[
        OF pp_t_symmetrized_singleton_family_builder_logical]
    unfolding pp_purity_schema_def by blast
  have negator_purity:
      "pp_pure pp_t_boolean_probe_transformer_type
          pp_t_unary_output_negator
        \<in> pp_purity_schema"
    using pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical
    unfolding pp_purity_schema_def by blast
  have conjunction_purity:
      "pp_pure pp_t_boolean_probe_builder_type
          pp_t_unary_output_conjunction
        \<in> pp_purity_schema"
    using pp_t_unary_output_conjunction_typed
      pp_t_unary_output_conjunction_logical
    unfolding pp_purity_schema_def by blast
  have applications:
      "pp_application_closure
          pp_t_boolean_probe_classifier_type
          pp_t_boolean_probe_unary_type
        \<in> pp_application_closure_schema
      \<and>
      pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_unary_type
        \<in> pp_application_closure_schema
      \<and>
      pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_transformer_type
        \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  show ?thesis
    using family_purity negator_purity conjunction_purity
      applications
    unfolding pp_finite_boolean_classifier_cycle_package_def
      pp_recombination_fixed_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

lemma pp_application_pair_of_explicit[simp]:
  "pp_application_pair_of
      (pp_application_closure \<sigma> \<tau>)
    =
    (\<sigma>, \<tau>)"
proof -
  have member:
      "pp_application_closure \<sigma> \<tau>
        \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  have equation:
      "pp_application_closure \<sigma> \<tau>
        =
        pp_application_closure
          (fst (pp_application_pair_of
            (pp_application_closure \<sigma> \<tau>)))
          (snd (pp_application_pair_of
            (pp_application_closure \<sigma> \<tau>)))"
    by (rule pp_application_pair_of_correct[OF member])
  have components:
      "\<sigma> =
          fst (pp_application_pair_of
            (pp_application_closure \<sigma> \<tau>))
        \<and>
        \<tau> =
          snd (pp_application_pair_of
            (pp_application_closure \<sigma> \<tau>))"
    by (rule pp_application_closure_pair_injective[OF equation])
  show ?thesis
    using components
    by (cases "pp_application_pair_of
        (pp_application_closure \<sigma> \<tau>)")
      simp
qed

lemma pp_finite_boolean_classifier_cycle_application_part:
  "pp_finite_boolean_classifier_cycle_package
      \<inter> pp_application_closure_schema
    =
    {
      pp_application_closure
        pp_t_boolean_probe_classifier_type
        pp_t_boolean_probe_unary_type,
      pp_application_closure
        pp_t_boolean_probe_unary_type
        pp_t_boolean_probe_unary_type,
      pp_application_closure
        pp_t_boolean_probe_unary_type
        pp_t_boolean_probe_transformer_type}"
  unfolding pp_finite_boolean_classifier_cycle_package_def
    pp_recombination_fixed_axioms_def
    pp_application_closure_schema_def
    pp_target_PP_def pp_purity_of_pure_def
    pp_unique_fundamental_def
    pp_zeroary_recombination_def
    pp_unary_recombination_def
    pp_application_closure_def
    pp_pure_def pp_fun_def pp_Pure_def pp_Fun_def
  by auto

theorem pp_finite_boolean_classifier_cycle_application_pairs:
  "pp_fragment_application_pairs
      pp_finite_boolean_classifier_cycle_package
    =
    pp_finite_boolean_closure_pairs"
  unfolding pp_fragment_application_pairs_def
    pp_finite_boolean_classifier_cycle_application_part
    pp_finite_boolean_closure_pairs_def
    pp_finite_negation_closure_pairs_def
    pp_finite_first_classifier_cycle_def
  by auto

theorem pp_finite_boolean_classifier_cycle_component:
  "pp_finite_component
      (pp_fragment_application_pairs
        pp_finite_boolean_classifier_cycle_package)
      pp_finite_unary_type
    =
    {pp_finite_unary_type, pp_finite_classifier_type,
      pp_finite_unary_transformer_type}"
  unfolding
    pp_finite_boolean_classifier_cycle_application_pairs
  by (rule pp_finite_boolean_classifier_component)

theorem pp_t_probe_successor_model_finite_package_gvalid:
  "ProbeSuccessorModelConstants.TreeHenkin.gvalid_set
    pp_finite_boolean_classifier_cycle_package"
  unfolding
    ProbeSuccessorModelConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_finite_boolean_classifier_cycle_package"
  from A consider
      (target) "A = pp_target_PP"
    | (unique) "A = pp_unique_fundamental Prop"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
    | (family_purity)
        "A = pp_pure pp_t_boolean_probe_family_builder_type
          (pp_t_family_probe_builder
            pp_t_symmetrized_singleton_family_builder)"
    | (negator_purity)
        "A = pp_pure pp_t_boolean_probe_transformer_type
          pp_t_unary_output_negator"
    | (conjunction_purity)
        "A = pp_pure pp_t_boolean_probe_builder_type
          pp_t_unary_output_conjunction"
    | (family_application)
        "A = pp_application_closure
          pp_t_boolean_probe_classifier_type
          pp_t_boolean_probe_unary_type"
    | (transformer_application)
        "A = pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_unary_type"
    | (builder_application)
        "A = pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_transformer_type"
    unfolding pp_finite_boolean_classifier_cycle_package_def
      pp_recombination_fixed_axioms_def
    by blast
  then show
      "ProbeSuccessorModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case target
    then show ?thesis
      using pp_t_probe_successor_model_target_PP_gvalid by simp
  next
    case unique
    then show ?thesis
      using pp_t_probe_successor_model_unique_fundamental_gvalid
      by simp
  next
    case zeroary
    then show ?thesis
      using
        pp_t_probe_successor_model_zeroary_recombination_gvalid
      by simp
  next
    case unary
    then show ?thesis
      using
        pp_t_probe_successor_model_unary_recombination_gvalid
      by simp
  next
    case family_purity
    then show ?thesis
      using pp_t_probe_successor_family_builder_purity_gvalid
      by simp
  next
    case negator_purity
    then show ?thesis
      using pp_t_probe_successor_negator_purity_gvalid by simp
  next
    case conjunction_purity
    then show ?thesis
      using
        pp_t_probe_successor_conjunction_builder_purity_gvalid
      by simp
  next
    case family_application
    then show ?thesis
      using
        pp_t_probe_successor_model_family_application_gvalid
      by simp
  next
    case transformer_application
    then show ?thesis
      using
        pp_t_probe_successor_model_transformer_application_gvalid
      by simp
  next
    case builder_application
    then show ?thesis
      using
        pp_t_probe_successor_model_builder_application_gvalid
      by simp
  qed
qed

theorem pp_finite_boolean_classifier_cycle_package_consistent:
  "CEV_axiom_consistent []
    pp_finite_boolean_classifier_cycle_package"
  using ProbeSuccessorModelConstants.pp_t_base_sound
    ProbeSuccessorModelConstants.pp_t_zeta_sound
    pp_t_probe_successor_model_finite_package_gvalid
  by (rule
    ProbeSuccessorModelConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

end
