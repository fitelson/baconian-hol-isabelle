theory Bacon_PP_ZF_Tree_Modal_Boolean_Finite_Model
  imports
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Background.Bacon_PP_ZF_Tree_Modal_Boolean_Background
begin

section \<open>Logical purity in the modal-Boolean model\<close>

theorem pp_t_probe_modal_boolean_model_logical_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and closed_pure:
      "\<And>w. pp_t_probe_modal_boolean_model_pure \<sigma> w
        (pp_t_closed_den M)"
  shows "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule ProbeModalBooleanModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  let ?\<rho> = "pp_t_list_env env"
  have empty_env: "pp_t_env_typed [] ?\<rho>"
    by (rule pp_t_empty_env_typed)
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_probe_modal_boolean_model_constants ?\<rho>
          (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
      pp_t_probe_modal_boolean_model_pure \<sigma> w
        (pp_t_eval pp_t_probe_modal_boolean_model_constants ?\<rho> M)"
    by (rule pp_t_probe_modal_boolean_model_eval_pure_holds[
      OF typed empty_env])
  have closed_domain:
      "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have eval_domain:
      "Elem
        (pp_t_eval pp_t_probe_modal_boolean_model_constants ?\<rho> M)
        (pp_t_domain \<sigma>)"
    using ProbeModalBooleanModelConstants.pp_t_eval_type[
      OF typed empty_env]
    by (simp add: pp_t_dom_def)
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_closed_den M)
        (pp_t_eval pp_t_probe_modal_boolean_model_constants ?\<rho> M)"
    by (rule pp_t_probe_modal_boolean_model_closed_logical_eval_eqv[
      OF typed logical])
  have pure_eval:
      "pp_t_probe_modal_boolean_model_pure \<sigma> w
        (pp_t_eval pp_t_probe_modal_boolean_model_constants ?\<rho> M)"
    using pp_t_probe_modal_boolean_model_pure_admissible
      closed_domain eval_domain related closed_pure[of w]
    unfolding pp_t_predicate_admissible_def
    by (metis prefix_order.refl)
  show "pp_t_holds
      (ProbeModalBooleanModelConstants.pp_t_den
        (pp_pure \<sigma> M) env) w"
    unfolding ProbeModalBooleanModelConstants.pp_t_den_def
    using evaluation pure_eval by blast
qed

lemma pp_t_probe_modal_boolean_family_builder_closed_pure:
  "pp_t_probe_modal_boolean_model_pure
    pp_t_boolean_probe_family_builder_type w
    (pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder))"
  unfolding pp_t_probe_successor_family_builder_den_def[symmetric]
  by (simp add: pp_t_probe_successor_family_builder_in_stock)

lemma pp_t_probe_modal_boolean_negator_closed_pure:
  "pp_t_probe_modal_boolean_model_pure
    pp_t_boolean_probe_transformer_type w
    (pp_t_closed_den pp_t_unary_output_negator)"
  by (simp add:
      pp_t_probe_modal_boolean_transformer_stock_negator)

lemma pp_t_probe_modal_boolean_necessitation_closed_pure:
  "pp_t_probe_modal_boolean_model_pure
    pp_t_boolean_probe_transformer_type w
    pp_t_unary_output_necessitation_den"
  by (simp add:
      pp_t_probe_modal_boolean_transformer_stock_necessitation)

lemma pp_t_probe_modal_boolean_conjunction_builder_closed_pure:
  "pp_t_probe_modal_boolean_model_pure
    pp_t_boolean_probe_builder_type w
    pp_t_unary_output_conjunction_den"
  by (simp add:
      pp_t_probe_successor_conjunction_builder_in_stock)

theorem pp_t_probe_modal_boolean_family_builder_purity_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_family_builder_type
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder))"
  by (rule pp_t_probe_modal_boolean_model_logical_purity_gvalid[
    OF pp_t_family_probe_builder_typed[
        OF pp_t_symmetrized_singleton_family_builder_typed]
      pp_t_family_probe_builder_logical[
        OF pp_t_symmetrized_singleton_family_builder_logical]
      pp_t_probe_modal_boolean_family_builder_closed_pure])

theorem pp_t_probe_modal_boolean_negator_purity_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_transformer_type
      pp_t_unary_output_negator)"
  by (rule pp_t_probe_modal_boolean_model_logical_purity_gvalid[
    OF pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical
      pp_t_probe_modal_boolean_negator_closed_pure])

theorem pp_t_probe_modal_boolean_necessitation_purity_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_transformer_type
      pp_t_unary_output_necessitation)"
  by (rule pp_t_probe_modal_boolean_model_logical_purity_gvalid[
    OF pp_t_unary_output_necessitation_typed
      pp_t_unary_output_necessitation_logical
      pp_t_probe_modal_boolean_necessitation_closed_pure])

theorem pp_t_probe_modal_boolean_conjunction_builder_purity_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_boolean_probe_builder_type
      pp_t_unary_output_conjunction)"
  by (rule pp_t_probe_modal_boolean_model_logical_purity_gvalid[
    OF pp_t_unary_output_conjunction_typed
      pp_t_unary_output_conjunction_logical
      pp_t_probe_modal_boolean_conjunction_builder_closed_pure])

section \<open>Application closure\<close>

lemma pp_t_probe_modal_boolean_model_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_probe_modal_boolean_model_pure
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
          \<and> pp_t_probe_modal_boolean_model_pure \<sigma> w x
        \<longrightarrow>
        pp_t_probe_modal_boolean_model_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_probe_modal_boolean_model_family_application_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_classifier_type
      pp_t_boolean_probe_unary_type)"
proof (rule ProbeModalBooleanModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeModalBooleanModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_classifier_type
          pp_t_boolean_probe_unary_type) env) w"
    unfolding ProbeModalBooleanModelConstants.pp_t_den_def
      pp_t_probe_modal_boolean_model_application_closure_holds_iff
    using pp_t_probe_modal_boolean_model_family_application
    by blast
qed

theorem pp_t_probe_modal_boolean_model_transformer_application_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_unary_type
      pp_t_boolean_probe_unary_type)"
proof (rule ProbeModalBooleanModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeModalBooleanModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_unary_type) env) w"
    unfolding ProbeModalBooleanModelConstants.pp_t_den_def
      pp_t_probe_modal_boolean_model_application_closure_holds_iff
    using pp_t_probe_modal_boolean_model_transformer_application
    by blast
qed

theorem pp_t_probe_modal_boolean_model_builder_application_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_boolean_probe_unary_type
      pp_t_boolean_probe_transformer_type)"
proof (rule ProbeModalBooleanModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ProbeModalBooleanModelConstants.pp_t_den
        (pp_application_closure
          pp_t_boolean_probe_unary_type
          pp_t_boolean_probe_transformer_type) env) w"
    unfolding ProbeModalBooleanModelConstants.pp_t_den_def
      pp_t_probe_modal_boolean_model_application_closure_holds_iff
    using pp_t_probe_modal_boolean_model_builder_application
    by blast
qed

section \<open>The finite modal-Boolean classifier-cycle package\<close>

definition pp_finite_modal_boolean_classifier_cycle_package ::
    "oterm set"
where
  "pp_finite_modal_boolean_classifier_cycle_package =
    pp_finite_boolean_classifier_cycle_package
    \<union> {
      pp_pure pp_t_boolean_probe_transformer_type
        pp_t_unary_output_necessitation}"

lemma pp_finite_modal_boolean_classifier_cycle_package_finite:
  "finite pp_finite_modal_boolean_classifier_cycle_package"
  unfolding pp_finite_modal_boolean_classifier_cycle_package_def
  using pp_finite_boolean_classifier_cycle_package_finite
  by simp

lemma pp_finite_modal_boolean_classifier_cycle_package_subset:
  "pp_finite_modal_boolean_classifier_cycle_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have necessity_purity:
      "pp_pure pp_t_boolean_probe_transformer_type
          pp_t_unary_output_necessitation
        \<in> pp_purity_schema"
    using pp_t_unary_output_necessitation_typed
      pp_t_unary_output_necessitation_logical
    unfolding pp_purity_schema_def by blast
  show ?thesis
    using pp_finite_boolean_classifier_cycle_package_subset
      necessity_purity
    unfolding pp_finite_modal_boolean_classifier_cycle_package_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

lemma pp_t_probe_modal_boolean_model_base_package_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid_set
    pp_finite_boolean_classifier_cycle_package"
  unfolding
    ProbeModalBooleanModelConstants.TreeHenkin.gvalid_set_def
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
      "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case target
    then show ?thesis
      using pp_t_probe_modal_boolean_model_target_PP_gvalid by simp
  next
    case unique
    then show ?thesis
      using pp_t_probe_modal_boolean_model_unique_fundamental_gvalid
      by simp
  next
    case zeroary
    then show ?thesis
      using
        pp_t_probe_modal_boolean_model_zeroary_recombination_gvalid
      by simp
  next
    case unary
    then show ?thesis
      using
        pp_t_probe_modal_boolean_model_unary_recombination_gvalid
      by simp
  next
    case family_purity
    then show ?thesis
      using pp_t_probe_modal_boolean_family_builder_purity_gvalid
      by simp
  next
    case negator_purity
    then show ?thesis
      using pp_t_probe_modal_boolean_negator_purity_gvalid by simp
  next
    case conjunction_purity
    then show ?thesis
      using
        pp_t_probe_modal_boolean_conjunction_builder_purity_gvalid
      by simp
  next
    case family_application
    then show ?thesis
      using
        pp_t_probe_modal_boolean_model_family_application_gvalid
      by simp
  next
    case transformer_application
    then show ?thesis
      using
        pp_t_probe_modal_boolean_model_transformer_application_gvalid
      by simp
  next
    case builder_application
    then show ?thesis
      using
        pp_t_probe_modal_boolean_model_builder_application_gvalid
      by simp
  qed
qed

theorem pp_t_probe_modal_boolean_model_finite_package_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid_set
    pp_finite_modal_boolean_classifier_cycle_package"
  unfolding
    ProbeModalBooleanModelConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A:
      "A \<in> pp_finite_modal_boolean_classifier_cycle_package"
  then consider
      (old) "A \<in> pp_finite_boolean_classifier_cycle_package"
    | (necessitation)
        "A = pp_pure pp_t_boolean_probe_transformer_type
          pp_t_unary_output_necessitation"
    unfolding pp_finite_modal_boolean_classifier_cycle_package_def
    by blast
  then show
      "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case old
    show ?thesis
      using pp_t_probe_modal_boolean_model_base_package_gvalid
      unfolding
        ProbeModalBooleanModelConstants.TreeHenkin.gvalid_set_def
      using old by blast
  next
    case necessitation
    then show ?thesis
      using pp_t_probe_modal_boolean_necessitation_purity_gvalid
      by simp
  qed
qed

theorem pp_finite_modal_boolean_classifier_cycle_package_consistent:
  "CEV_axiom_consistent []
    pp_finite_modal_boolean_classifier_cycle_package"
  using ProbeModalBooleanModelConstants.pp_t_base_sound
    ProbeModalBooleanModelConstants.pp_t_zeta_sound
    pp_t_probe_modal_boolean_model_finite_package_gvalid
  by (rule
    ProbeModalBooleanModelConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

end
