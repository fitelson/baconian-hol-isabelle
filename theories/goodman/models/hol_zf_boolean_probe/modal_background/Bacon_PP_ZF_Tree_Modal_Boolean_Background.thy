theory Bacon_PP_ZF_Tree_Modal_Boolean_Background
  imports
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Model.Bacon_PP_ZF_Tree_Modal_Boolean_Model
begin

section \<open>PP in the modal-Boolean model\<close>

lemma pp_t_probe_modal_boolean_model_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
      pp_target_PP) w"
proof -
  have evaluation:
      "pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
          pp_target_PP
        =
        pp_t_classifier pp_t_boolean_probe_classifier_type
          (pp_t_probe_modal_boolean_model_pure
            pp_t_boolean_probe_classifier_type)
        \<acute> pp_t_probe_modal_boolean_classifier"
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    by (simp add: pp_t_probe_modal_boolean_classifier_def)
  have at_classifier:
      "pp_t_holds
        (pp_t_classifier pp_t_boolean_probe_classifier_type
          (pp_t_probe_modal_boolean_model_pure
            pp_t_boolean_probe_classifier_type)
          \<acute> pp_t_probe_modal_boolean_classifier) w
      \<longleftrightarrow>
      pp_t_probe_modal_boolean_model_pure
        pp_t_boolean_probe_classifier_type w
        pp_t_probe_modal_boolean_classifier"
    by (rule pp_t_classifier_holds[
      OF pp_t_probe_modal_boolean_classifier_in_domain])
  show ?thesis
    unfolding evaluation
    using at_classifier
      pp_t_probe_modal_boolean_model_classifier_is_pure
    by blast
qed

theorem pp_t_probe_modal_boolean_model_target_PP_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding ProbeModalBooleanModelConstants.TreeHenkin.gvalid_def
    ProbeModalBooleanModelConstants.pp_t_den_def
  using pp_t_probe_modal_boolean_model_target_PP_holds by blast

section \<open>Unique fundamentality\<close>

lemma pp_t_probe_modal_boolean_model_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_t_probe_modal_boolean_stock_seed_at w"
  have base: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[
      OF base pp_t_probe_modal_boolean_stock_seed_at_in_domain] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval pp_t_probe_modal_boolean_model_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      by (rule pp_t_eqv_reflexive[
        OF pp_t_probe_modal_boolean_stock_seed_at_in_domain])
    show ?thesis
      using pp_t_probe_modal_boolean_model_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_probe_modal_boolean_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_t_domain Prop)"
    have yr_env:
        "pp_t_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_t_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_probe_modal_boolean_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_probe_modal_boolean_model_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval pp_t_probe_modal_boolean_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_probe_modal_boolean_model_constants
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_t_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_t_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_t_probe_modal_boolean_stock_seed_at_in_domain
      r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

theorem pp_t_probe_modal_boolean_model_unique_fundamental_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding ProbeModalBooleanModelConstants.TreeHenkin.gvalid_def
    ProbeModalBooleanModelConstants.pp_t_den_def
  using pp_t_probe_modal_boolean_model_unique_fundamental_holds
  by blast

section \<open>Recombination\<close>

lemma pp_t_probe_modal_boolean_model_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
      pp_zeroary_recombination) w"
  by (simp add: pp_zeroary_recombination_def pp_pure_def
      pp_t_classifier_holds extend_env.simps
      pp_t_probe_modal_boolean_model_pure_def)

theorem pp_t_probe_modal_boolean_model_zeroary_recombination_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding ProbeModalBooleanModelConstants.TreeHenkin.gvalid_def
    ProbeModalBooleanModelConstants.pp_t_den_def
  using pp_t_probe_modal_boolean_model_zeroary_recombination_holds
  by blast

lemma pp_t_probe_modal_boolean_model_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_probe_modal_boolean_model_pure
            pp_t_boolean_probe_unary_type w X
          \<and> pp_t_seeded_fundamental_at
            pp_t_probe_modal_boolean_stock_seed_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v)
          \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_probe_modal_boolean_model_fundamental_recombines:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and X_pure:
      "pp_t_probe_modal_boolean_model_pure
        pp_t_boolean_probe_unary_type w X"
    and r: "Elem r (pp_t_domain Prop)"
    and r_fundamental:
      "pp_t_seeded_fundamental_at
        pp_t_probe_modal_boolean_stock_seed_at Prop w r"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w"
proof -
  let ?seed = "pp_t_probe_modal_boolean_stock_seed_at w"
  have seed: "Elem ?seed (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_stock_seed_at_in_domain)
  have r_seed: "pp_t_eqv Prop w r ?seed"
    using r_fundamental by simp
  have seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> ?seed) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have related: "pp_t_eqv Prop v r ?seed"
      by (rule pp_t_eqv_persistent[OF r_seed wv])
    have applications:
        "pp_t_eqv Prop v (X \<acute> r) (X \<acute> ?seed)"
      using pp_t_arrow_member_respects[
        OF X r seed related] .
    show "pp_t_holds (X \<acute> ?seed) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        necessary[rule_format, OF wv]
      by simp
  qed
  have X_stock: "pp_t_probe_modal_boolean_stock w X"
    using X_pure by simp
  show ?thesis
    using
      pp_t_probe_modal_boolean_stock_seed_recombines_at_every_world[
        of w]
      X X_stock seed_necessary
    unfolding pp_t_unary_recombines_at_def by blast
qed

lemma pp_t_probe_modal_boolean_model_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_probe_modal_boolean_model_constants \<rho>
      pp_unary_recombination) w"
  unfolding
    pp_t_probe_modal_boolean_model_unary_recombination_holds_iff
  using pp_t_probe_modal_boolean_model_fundamental_recombines
  by blast

theorem pp_t_probe_modal_boolean_model_unary_recombination_gvalid:
  "ProbeModalBooleanModelConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding ProbeModalBooleanModelConstants.TreeHenkin.gvalid_def
    ProbeModalBooleanModelConstants.pp_t_den_def
  using pp_t_probe_modal_boolean_model_unary_recombination_holds
  by blast

end
