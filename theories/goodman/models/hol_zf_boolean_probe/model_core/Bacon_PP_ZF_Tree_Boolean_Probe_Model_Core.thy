theory Bacon_PP_ZF_Tree_Boolean_Probe_Model_Core
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Higher_Types.Bacon_PP_ZF_Tree_Boolean_Probe_Higher_Types
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Seeded_Stock
begin

section \<open>Seeded constants for the stabilized Boolean stock\<close>

definition pp_t_probe_successor_model_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_probe_successor_model_constants =
    pp_t_seeded_internal_constants
      pp_t_probe_successor_model_pure
      pp_t_probe_successor_stock_seed_at"

lemma pp_t_probe_successor_seeded_fundamental_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_seeded_fundamental_at
      pp_t_probe_successor_stock_seed_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain Prop)"
      and y: "Elem y (pp_t_domain Prop)"
      and xy: "pp_t_eqv Prop w x y"
      and wv: "prefix w v"
    have xy_v: "pp_t_eqv Prop v x y"
      using pp_t_eqv_persistent[OF xy wv] .
    have seed:
        "Elem (pp_t_probe_successor_stock_seed_at v)
          (pp_t_domain Prop)"
      by (rule pp_t_probe_successor_stock_seed_at_in_domain)
    have refl:
        "pp_t_eqv Prop v
          (pp_t_probe_successor_stock_seed_at v)
          (pp_t_probe_successor_stock_seed_at v)"
      by (rule pp_t_eqv_reflexive[OF seed])
    show "pp_t_seeded_fundamental_at
          pp_t_probe_successor_stock_seed_at Prop v x
        =
        pp_t_seeded_fundamental_at
          pp_t_probe_successor_stock_seed_at Prop v y"
      using pp_t_eqv_congruence[
        OF x y seed seed xy_v refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
qed

interpretation ProbeSuccessorModelConstants:
  pp_t_constants pp_t_probe_successor_model_constants
proof
  fix c \<sigma>
  show "Elem (pp_t_probe_successor_model_constants c \<sigma>)
      (pp_t_domain \<sigma>)"
  proof (cases \<sigma>)
    case Ind
    then show ?thesis
      unfolding pp_t_probe_successor_model_constants_def
      using pp_t_default_in_domain[of Ind] by simp
  next
    case Prop
    then show ?thesis
      unfolding pp_t_probe_successor_model_constants_def
      using pp_t_default_in_domain[of Prop] by simp
  next
    case (Arr \<sigma> \<tau>)
    have pure_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_probe_successor_model_pure \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      by (rule pp_t_classifier_in_domain)
        (rule pp_t_probe_successor_model_pure_admissible)
    have fun_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_seeded_fundamental_at
              pp_t_probe_successor_stock_seed_at \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      by (rule pp_t_classifier_in_domain)
        (rule
          pp_t_probe_successor_seeded_fundamental_admissible)
    have default:
        "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      by (rule pp_t_default_in_domain)
    show ?thesis
      using Arr pure_classifier fun_classifier default
      by (auto simp: pp_t_probe_successor_model_constants_def
          pp_t_seeded_fundamental_at.simps)
  qed
qed

lemma pp_t_probe_successor_model_eval_Pure[simp]:
  "pp_t_eval pp_t_probe_successor_model_constants \<rho>
      (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_probe_successor_model_pure \<sigma>)"
  by (simp add: pp_t_probe_successor_model_constants_def
      pp_Pure_def pp_pure_name_def)

lemma pp_t_probe_successor_model_eval_Fun[simp]:
  "pp_t_eval pp_t_probe_successor_model_constants \<rho>
      (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at
        pp_t_probe_successor_stock_seed_at \<sigma>)"
  by (simp add: pp_t_probe_successor_model_constants_def
      pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_probe_successor_model_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_probe_successor_model_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
    pp_t_probe_successor_model_pure \<sigma> w
      (pp_t_eval pp_t_probe_successor_model_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_probe_successor_model_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using ProbeSuccessorModelConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_probe_successor_model_pure \<sigma>" w]
    by simp
qed

lemma pp_t_probe_successor_model_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_probe_successor_model_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
    pp_t_seeded_fundamental_at
      pp_t_probe_successor_stock_seed_at \<sigma> w
      (pp_t_eval pp_t_probe_successor_model_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_probe_successor_model_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using ProbeSuccessorModelConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at
        pp_t_probe_successor_stock_seed_at \<sigma>" w]
    by simp
qed

lemma pp_t_probe_successor_model_closed_logical_eval_eqv:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_eqv \<sigma> w
    (pp_t_closed_den M)
    (pp_t_eval pp_t_probe_successor_model_constants \<rho> M)"
proof -
  have const_free: "consts_of M = {}"
    using logical unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval pp_t_probe_successor_model_constants \<rho> M =
        pp_t_eval pp_t_default_constants \<rho> M"
    using pp_t_eval_const_free[OF const_free] .
  have eval_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF typed pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have closed_domain:
      "Elem
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)
        (pp_t_domain \<sigma>)"
    using pp_t_closed_den_in_domain[OF typed]
    unfolding pp_t_closed_den_def .
  have forward:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF typed pp_t_empty_env_eqv] .
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)
        (pp_t_eval pp_t_default_constants \<rho> M)"
    by (rule pp_t_eqv_symmetric[
      OF eval_domain closed_domain forward])
  show ?thesis
    unfolding pp_t_closed_den_def
    using related change_constants by simp
qed

end
