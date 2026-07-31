theory Bacon_PP_ZF_Tree_Dual_Constant_Absorption
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Identity_Negation_Stock.Bacon_PP_ZF_Tree_Dual_Identity_Negation_Stock
begin

section \<open>Closed constant operators\<close>

definition pp_t_constant_falsity_unary :: oterm where
  "pp_t_constant_falsity_unary = pp_constant_operator ObjFalse"

lemma pp_t_constant_falsity_unary_typed:
  "[] \<turnstile> pp_t_constant_falsity_unary :
    pp_t_one_context_unary_type"
  unfolding pp_t_constant_falsity_unary_def
  using typed_pp_constant_operator[
    OF typed_ObjFalse, where \<Gamma>="[]"]
  unfolding pp_unary_ty_def .

lemma pp_t_constant_falsity_unary_logical:
  "pp_logical_vocabulary pp_t_constant_falsity_unary"
  by (simp add: pp_t_constant_falsity_unary_def
      pp_constant_operator_def pp_constant_builder_def
      pp_logical_vocabulary_def ObjFalse_def ObjTrue_def)

lemma pp_t_closed_constant_truth_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_closed_den pp_t_constant_truth_unary \<acute> p
      =
     pp_zf_truth True"
  unfolding pp_t_closed_den_def
    pp_t_constant_truth_unary_def
    pp_constant_operator_def pp_constant_builder_def
  using p pp_t_truth_in_domain[where b=True]
  by (simp add: Lambda_app pp_t_eval_ObjTrue)

lemma pp_t_closed_constant_falsity_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_closed_den pp_t_constant_falsity_unary \<acute> p
      =
     pp_zf_truth False"
proof -
  have eval_false:
      "pp_t_eval pp_t_default_constants pp_t_closed_env ObjFalse
        = pp_zf_truth False"
    unfolding ObjFalse_def
  proof (simp only: pp_t_eval.simps, rule pp_t_prop_ext)
    show "Elem
        (pp_t_prop
          (\<lambda>w. \<not> pp_t_holds
            (pp_t_eval pp_t_default_constants pp_t_closed_env ObjTrue) w))
        (pp_t_domain Prop)"
      by (rule pp_t_prop_in_domain)
    show "Elem (pp_zf_truth False) (pp_t_domain Prop)"
      by (rule pp_t_truth_in_domain)
    fix w
    show "pp_t_holds
          (pp_t_prop
            (\<lambda>w. \<not> pp_t_holds
              (pp_t_eval pp_t_default_constants pp_t_closed_env ObjTrue) w))
          w
        =
        pp_t_holds (pp_zf_truth False) w"
      by (simp add: pp_t_eval_ObjTrue)
  qed
  show ?thesis
    unfolding pp_t_closed_den_def
      pp_t_constant_falsity_unary_def
      pp_constant_operator_def pp_constant_builder_def
    using p pp_t_truth_in_domain[where b=False]
    by (simp add: Lambda_app eval_false)
qed

lemma pp_t_modal_stock_contains_truth_singleton:
  "pp_t_probe_modal_boolean_stock w
    (pp_t_singleton_family_at (pp_zf_truth b))"
proof -
  have p: "Elem (pp_zf_truth b) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled:
      "pp_t_eqv Prop w (pp_zf_truth b) (pp_zf_truth True)
      \<or>
       pp_t_eqv Prop w (pp_zf_truth b) (pp_zf_truth False)"
    by (cases b)
      (simp_all add: pp_t_eqv_reflexive[OF pp_t_truth_in_domain])
  have closed:
      "pp_t_closed_logical_stock pp_t_one_context_unary_type w
        (pp_t_singleton_family_at (pp_zf_truth b))"
    using pp_t_singleton_family_in_closed_stock_iff_settled[
      OF p, of w]
      settled by blast
  have base:
      "pp_t_probe_boolean_stock w
        (pp_t_singleton_family_at (pp_zf_truth b))"
    by (rule pp_t_closed_logical_stock_subset_probe_boolean_stock[
      OF closed])
  have successor:
      "pp_t_probe_successor_stock w
        (pp_t_singleton_family_at (pp_zf_truth b))"
    by (rule pp_t_probe_boolean_stock_subset_successor_stock[OF base])
  show ?thesis
    by (rule
      pp_t_probe_successor_stock_subset_modal_boolean_stock[OF successor])
qed

section \<open>The constant-indexed classifier sections collapse\<close>

lemma pp_t_dual_constant_truth_full_section:
  "pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_constant_truth_unary)
    =
   pp_t_closed_den pp_t_constant_truth_unary"
proof (rule pp_t_unary_function_ext)
  have F:
      "Elem (pp_t_closed_den pp_t_constant_truth_unary)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_constant_truth_unary_typed)
  show "Elem
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_truth_unary))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[OF F])
  show "Elem (pp_t_closed_den pp_t_constant_truth_unary)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule F)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_truth_unary) \<acute> p
      =
    pp_t_closed_den pp_t_constant_truth_unary \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_truth_unary) \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_dual_recurrent_full_section_in_domain[OF F] p])
    show "Elem
        (pp_t_closed_den pp_t_constant_truth_unary \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[OF F p])
    fix w
    have component:
        "pp_t_holds
          (pp_t_recurrent_modal_component
              (pp_t_closed_den pp_t_constant_truth_unary)
            \<acute> p) w"
    proof -
      have probe:
          "pp_t_holds
              (pp_t_recurrent_modal_component
                  (pp_t_closed_den pp_t_constant_truth_unary)
                \<acute> p) w
            \<longleftrightarrow>
           pp_t_probe_modal_boolean_stock w
            (pp_t_singleton_family_at
              (pp_t_closed_den pp_t_constant_truth_unary \<acute> p))"
        by (rule pp_t_modal_singleton_operator_probe_apply_holds[
          OF F p])
      show ?thesis
        using probe pp_t_modal_stock_contains_truth_singleton[
          where b=True and w=w]
        unfolding pp_t_closed_constant_truth_apply[OF p]
        by blast
    qed
    have boundary:
        "Elem
          (pp_t_moving_boundary_operator_probe
              pp_t_probe_modal_boolean_dual_recurrent_seed_at
            \<acute> pp_t_closed_den pp_t_constant_truth_unary)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_moving_boundary_operator_probe_in_domain F])
    have disjunction:
        "pp_t_holds
          (pp_t_dual_recurrent_full_section
            (pp_t_closed_den pp_t_constant_truth_unary) \<acute> p) w"
      using pp_t_unary_output_disjunction_apply_holds[
        OF pp_t_recurrent_modal_component_in_domain[OF F]
          boundary p, of w]
        component by blast
    show "pp_t_holds
          (pp_t_dual_recurrent_full_section
            (pp_t_closed_den pp_t_constant_truth_unary) \<acute> p) w
        =
        pp_t_holds
          (pp_t_closed_den pp_t_constant_truth_unary \<acute> p) w"
      using disjunction
      unfolding pp_t_closed_constant_truth_apply[OF p]
      by simp
  qed
qed

lemma pp_t_dual_constant_falsity_full_section:
  "pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_constant_falsity_unary)
    =
   pp_t_closed_den pp_t_constant_truth_unary"
proof (rule pp_t_unary_function_ext)
  have F:
      "Elem (pp_t_closed_den pp_t_constant_falsity_unary)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_constant_falsity_unary_typed)
  have T:
      "Elem (pp_t_closed_den pp_t_constant_truth_unary)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_constant_truth_unary_typed)
  show "Elem
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_falsity_unary))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[OF F])
  show "Elem (pp_t_closed_den pp_t_constant_truth_unary)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule T)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_falsity_unary) \<acute> p
      =
    pp_t_closed_den pp_t_constant_truth_unary \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_falsity_unary) \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_dual_recurrent_full_section_in_domain[OF F] p])
    show "Elem
        (pp_t_closed_den pp_t_constant_truth_unary \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[OF T p])
    fix w
    have component:
        "pp_t_holds
          (pp_t_recurrent_modal_component
              (pp_t_closed_den pp_t_constant_falsity_unary)
            \<acute> p) w"
    proof -
      have probe:
          "pp_t_holds
              (pp_t_recurrent_modal_component
                  (pp_t_closed_den pp_t_constant_falsity_unary)
                \<acute> p) w
            \<longleftrightarrow>
           pp_t_probe_modal_boolean_stock w
            (pp_t_singleton_family_at
              (pp_t_closed_den pp_t_constant_falsity_unary \<acute> p))"
        by (rule pp_t_modal_singleton_operator_probe_apply_holds[
          OF F p])
      show ?thesis
        using probe pp_t_modal_stock_contains_truth_singleton[
          where b=False and w=w]
        unfolding pp_t_closed_constant_falsity_apply[OF p]
        by blast
    qed
    have boundary:
        "Elem
          (pp_t_moving_boundary_operator_probe
              pp_t_probe_modal_boolean_dual_recurrent_seed_at
            \<acute> pp_t_closed_den pp_t_constant_falsity_unary)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_moving_boundary_operator_probe_in_domain F])
    have disjunction:
        "pp_t_holds
          (pp_t_dual_recurrent_full_section
            (pp_t_closed_den pp_t_constant_falsity_unary) \<acute> p) w"
      using pp_t_unary_output_disjunction_apply_holds[
        OF pp_t_recurrent_modal_component_in_domain[OF F]
          boundary p, of w]
        component by blast
    show "pp_t_holds
          (pp_t_dual_recurrent_full_section
            (pp_t_closed_den pp_t_constant_falsity_unary) \<acute> p) w
        =
        pp_t_holds
          (pp_t_closed_den pp_t_constant_truth_unary \<acute> p) w"
      using disjunction
      unfolding pp_t_closed_constant_truth_apply[OF p]
      by simp
  qed
qed

theorem pp_t_dual_constant_sections_absorbed:
  "pp_t_probe_modal_boolean_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_constant_truth_unary))"
  "pp_t_probe_modal_boolean_stock w
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_truth_unary)))"
  "pp_t_probe_modal_boolean_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_constant_falsity_unary))"
  "pp_t_probe_modal_boolean_stock w
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_falsity_unary)))"
proof -
  have truth:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_closed_den pp_t_constant_truth_unary)"
    by (rule pp_t_closed_logical_unary_in_modal_boolean_stock[
      OF pp_t_constant_truth_unary_typed
        pp_t_constant_truth_unary_logical])
  show "pp_t_probe_modal_boolean_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_truth_unary))"
    unfolding pp_t_dual_constant_truth_full_section
    by (rule truth)
  show "pp_t_probe_modal_boolean_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_truth_unary)))"
    unfolding pp_t_dual_constant_truth_full_section
      pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_constant_truth_unary_typed] truth])
  show "pp_t_probe_modal_boolean_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_constant_falsity_unary))"
    unfolding pp_t_dual_constant_falsity_full_section
    by (rule truth)
  show "pp_t_probe_modal_boolean_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_t_constant_falsity_unary)))"
    unfolding pp_t_dual_constant_falsity_full_section
      pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_constant_truth_unary_typed] truth])
qed

end
