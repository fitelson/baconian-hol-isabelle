theory Bacon_PP_ZF_Tree_Dual_Quantified_Absorption
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Full_Modal_Stock.Bacon_PP_ZF_Tree_Dual_Full_Modal_Stock
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers
begin

section \<open>The six quantified indices have the four modal and two constant denotations\<close>

lemma pp_t_dual_HO_leibniz_truth_den:
  "pp_t_closed_den pp_t_HO_leibniz_truth_term
    = pp_t_necessity_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_closed_den pp_t_HO_leibniz_truth_term)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_HO_leibniz_terms_typed(1))
  show "Elem pp_t_necessity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain(1))
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_closed_den pp_t_HO_leibniz_truth_term \<acute> p
      = pp_t_necessity_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_closed_den pp_t_HO_leibniz_truth_term \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(1)] p])
    show "Elem (pp_t_necessity_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(1) p])
    fix w
    show "pp_t_holds
        (pp_t_closed_den pp_t_HO_leibniz_truth_term \<acute> p) w
      =
      pp_t_holds (pp_t_necessity_operator \<acute> p) w"
      using pp_t_HO_leibniz_truth_holds[OF p, of w]
        pp_t_necessity_operator_apply_holds[OF p, of w]
      unfolding pp_t_prop_eqv_truth_iff
      by blast
  qed
qed

lemma pp_t_dual_HO_leibniz_false_den:
  "pp_t_closed_den pp_t_HO_leibniz_false_term
    = pp_t_necessary_falsity_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_closed_den pp_t_HO_leibniz_false_term)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_HO_leibniz_terms_typed(2))
  show "Elem pp_t_necessary_falsity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_negated_modal_operators_in_domain(1))
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_closed_den pp_t_HO_leibniz_false_term \<acute> p
      = pp_t_necessary_falsity_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_closed_den pp_t_HO_leibniz_false_term \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(2)] p])
    show "Elem (pp_t_necessary_falsity_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_negated_modal_operators_in_domain(1) p])
    fix w
    have cp: "Elem (pp_t_complement p) (pp_t_domain Prop)"
      by (rule pp_t_complement_in_domain)
    show "pp_t_holds
        (pp_t_closed_den pp_t_HO_leibniz_false_term \<acute> p) w
      =
      pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) w"
      using pp_t_HO_leibniz_false_holds[OF p, of w]
        pp_t_necessity_operator_apply_holds[OF cp, of w]
      unfolding pp_t_necessary_falsity_operator_apply[OF p]
        pp_t_eqv.simps
      by simp
  qed
qed

lemma pp_t_dual_HO_not_leibniz_truth_den:
  "pp_t_closed_den pp_t_HO_not_leibniz_truth_term
    = pp_t_possible_falsity_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_HO_leibniz_terms_typed(3))
  show "Elem pp_t_possible_falsity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_negated_modal_operators_in_domain(2))
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_closed_den pp_t_HO_not_leibniz_truth_term \<acute> p
      = pp_t_possible_falsity_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_closed_den pp_t_HO_not_leibniz_truth_term \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(3)] p])
    show "Elem (pp_t_possible_falsity_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_negated_modal_operators_in_domain(2) p])
    fix w
    have cp: "Elem (pp_t_complement p) (pp_t_domain Prop)"
      by (rule pp_t_complement_in_domain)
    show "pp_t_holds
        (pp_t_closed_den pp_t_HO_not_leibniz_truth_term \<acute> p) w
      =
      pp_t_holds (pp_t_possible_falsity_operator \<acute> p) w"
      using pp_t_HO_not_leibniz_truth_holds[OF p, of w]
        pp_t_possibility_operator_apply_holds[OF cp, of w]
      unfolding pp_t_possible_falsity_operator_apply[OF p]
        pp_t_eqv.simps
      by auto
  qed
qed

lemma pp_t_dual_HO_not_leibniz_false_den:
  "pp_t_closed_den pp_t_HO_not_leibniz_false_term
    = pp_t_possibility_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_closed_den pp_t_HO_not_leibniz_false_term)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_HO_leibniz_terms_typed(4))
  show "Elem pp_t_possibility_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain(2))
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_closed_den pp_t_HO_not_leibniz_false_term \<acute> p
      = pp_t_possibility_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_closed_den pp_t_HO_not_leibniz_false_term \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(4)] p])
    show "Elem (pp_t_possibility_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(2) p])
    fix w
    show "pp_t_holds
        (pp_t_closed_den pp_t_HO_not_leibniz_false_term \<acute> p) w
      =
      pp_t_holds (pp_t_possibility_operator \<acute> p) w"
      using pp_t_HO_not_leibniz_false_holds[OF p, of w]
        pp_t_possibility_operator_apply_holds[OF p, of w]
      unfolding pp_t_eqv.simps
      by auto
  qed
qed

lemma pp_t_dual_HO_application_dens:
  "pp_t_closed_den pp_t_HO_forall_application_term
    = pp_t_closed_den pp_t_constant_falsity_unary"
  "pp_t_closed_den pp_t_HO_exists_application_term
    = pp_t_closed_den pp_t_constant_truth_unary"
proof -
  show "pp_t_closed_den pp_t_HO_forall_application_term
      = pp_t_closed_den pp_t_constant_falsity_unary"
  proof (rule pp_t_unary_function_ext)
    show "Elem (pp_t_closed_den pp_t_HO_forall_application_term)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule pp_t_HO_application_terms_typed(1))
    show "Elem (pp_t_closed_den pp_t_constant_falsity_unary)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule pp_t_constant_falsity_unary_typed)
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_closed_den pp_t_HO_forall_application_term \<acute> p
        = pp_t_closed_den pp_t_constant_falsity_unary \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          (pp_t_closed_den pp_t_HO_forall_application_term \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_closed_den_in_domain[
            OF pp_t_HO_application_terms_typed(1)] p])
      show "Elem
          (pp_t_closed_den pp_t_constant_falsity_unary \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_closed_den_in_domain[
            OF pp_t_constant_falsity_unary_typed] p])
      fix w
      show "pp_t_holds
          (pp_t_closed_den pp_t_HO_forall_application_term \<acute> p) w
        =
        pp_t_holds
          (pp_t_closed_den pp_t_constant_falsity_unary \<acute> p) w"
        using pp_t_HO_forall_application_never_holds[OF p, of w]
        unfolding pp_t_closed_constant_falsity_apply[OF p]
        by simp
    qed
  qed
  show "pp_t_closed_den pp_t_HO_exists_application_term
      = pp_t_closed_den pp_t_constant_truth_unary"
  proof (rule pp_t_unary_function_ext)
    show "Elem (pp_t_closed_den pp_t_HO_exists_application_term)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule pp_t_HO_application_terms_typed(2))
    show "Elem (pp_t_closed_den pp_t_constant_truth_unary)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule pp_t_constant_truth_unary_typed)
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_closed_den pp_t_HO_exists_application_term \<acute> p
        = pp_t_closed_den pp_t_constant_truth_unary \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          (pp_t_closed_den pp_t_HO_exists_application_term \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_closed_den_in_domain[
            OF pp_t_HO_application_terms_typed(2)] p])
      show "Elem
          (pp_t_closed_den pp_t_constant_truth_unary \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_closed_den_in_domain[
            OF pp_t_constant_truth_unary_typed] p])
      fix w
      show "pp_t_holds
          (pp_t_closed_den pp_t_HO_exists_application_term \<acute> p) w
        =
        pp_t_holds
          (pp_t_closed_den pp_t_constant_truth_unary \<acute> p) w"
        using pp_t_HO_exists_application_always_holds[OF p, of w]
        unfolding pp_t_closed_constant_truth_apply[OF p]
        by simp
    qed
  qed
qed

section \<open>The six classifier sections are already absorbed\<close>

lemma pp_t_dual_modal_stock_subset_full_modal_stock:
  assumes "pp_t_dual_modal_stock w X"
  shows "pp_t_dual_full_modal_stock w X"
  using assms
  unfolding pp_t_dual_full_modal_stock_def
    pp_t_dual_modal_stock_def
  by blast

lemma pp_t_probe_modal_boolean_subset_full_modal_stock:
  assumes "pp_t_probe_modal_boolean_stock w X"
  shows "pp_t_dual_full_modal_stock w X"
  using assms
  unfolding pp_t_dual_full_modal_stock_def
    pp_t_dual_modal_stock_def
    pp_t_dual_identity_negation_stock_def
    pp_t_dual_modal_boundary_stock_def
    pp_t_probe_modal_boolean_stock_def
  by blast

lemma pp_t_dual_modal_generated_section_in_full_stock:
  assumes "P \<in> pp_t_dual_modal_generated_sections"
  shows "pp_t_dual_full_modal_stock w P"
proof -
  have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_modal_generated_section_in_domain[OF assms])
  have base: "pp_t_dual_modal_stock w P"
    unfolding pp_t_dual_modal_stock_def
    using P assms pp_t_eqv_reflexive[OF P, of w]
    by blast
  show ?thesis
    by (rule pp_t_dual_modal_stock_subset_full_modal_stock[OF base])
qed

lemma pp_t_dual_negated_modal_generated_section_in_full_stock:
  assumes "P \<in> pp_t_dual_negated_modal_generated_sections"
  shows "pp_t_dual_full_modal_stock w P"
proof -
  have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule
      pp_t_dual_negated_modal_generated_section_in_domain[OF assms])
  show ?thesis
    unfolding pp_t_dual_full_modal_stock_def
    using P assms pp_t_eqv_reflexive[OF P, of w]
    by blast
qed

theorem pp_t_dual_six_quantified_sections_absorbed:
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_leibniz_truth_term))"
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_leibniz_false_term))"
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_not_leibniz_truth_term))"
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_not_leibniz_false_term))"
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_forall_application_term))"
  "pp_t_dual_full_modal_stock w
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_t_HO_exists_application_term))"
proof -
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_leibniz_truth_term))"
    unfolding pp_t_dual_HO_leibniz_truth_den
    by (rule pp_t_dual_modal_generated_section_in_full_stock)
      (simp add: pp_t_dual_modal_generated_sections_def)
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_leibniz_false_term))"
    unfolding pp_t_dual_HO_leibniz_false_den
    by (rule pp_t_dual_negated_modal_generated_section_in_full_stock)
      (simp add: pp_t_dual_negated_modal_generated_sections_def)
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_not_leibniz_truth_term))"
    unfolding pp_t_dual_HO_not_leibniz_truth_den
    by (rule pp_t_dual_negated_modal_generated_section_in_full_stock)
      (simp add: pp_t_dual_negated_modal_generated_sections_def)
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_not_leibniz_false_term))"
    unfolding pp_t_dual_HO_not_leibniz_false_den
    by (rule pp_t_dual_modal_generated_section_in_full_stock)
      (simp add: pp_t_dual_modal_generated_sections_def)
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_forall_application_term))"
    unfolding pp_t_dual_HO_application_dens(1)
    by (rule pp_t_probe_modal_boolean_subset_full_modal_stock)
      (rule pp_t_dual_constant_sections_absorbed(3))
  show "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_t_HO_exists_application_term))"
    unfolding pp_t_dual_HO_application_dens(2)
    by (rule pp_t_probe_modal_boolean_subset_full_modal_stock)
      (rule pp_t_dual_constant_sections_absorbed(1))
qed

corollary pp_t_dual_six_quantified_sections_and_complements_absorbed:
  assumes
    "P = pp_t_closed_den pp_t_HO_leibniz_truth_term
      \<or> P = pp_t_closed_den pp_t_HO_leibniz_false_term
      \<or> P = pp_t_closed_den pp_t_HO_not_leibniz_truth_term
      \<or> P = pp_t_closed_den pp_t_HO_not_leibniz_false_term
      \<or> P = pp_t_closed_den pp_t_HO_forall_application_term
      \<or> P = pp_t_closed_den pp_t_HO_exists_application_term"
  shows
    "pp_t_dual_full_modal_stock w
      (pp_t_dual_recurrent_full_section P)"
    "pp_t_dual_full_modal_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section P))"
proof -
  show stock:
      "pp_t_dual_full_modal_stock w
        (pp_t_dual_recurrent_full_section P)"
    using assms pp_t_dual_six_quantified_sections_absorbed by blast
  have P_domain:
      "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    using assms
      pp_t_closed_den_in_domain[OF pp_t_HO_leibniz_terms_typed(1)]
      pp_t_closed_den_in_domain[OF pp_t_HO_leibniz_terms_typed(2)]
      pp_t_closed_den_in_domain[OF pp_t_HO_leibniz_terms_typed(3)]
      pp_t_closed_den_in_domain[OF pp_t_HO_leibniz_terms_typed(4)]
      pp_t_closed_den_in_domain[OF pp_t_HO_application_terms_typed(1)]
      pp_t_closed_den_in_domain[OF pp_t_HO_application_terms_typed(2)]
    by blast
  have domain:
      "Elem (pp_t_dual_recurrent_full_section P)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[OF P_domain])
  show "pp_t_dual_full_modal_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section P))"
    by (rule pp_t_dual_full_modal_stock_negation_closed[
      OF domain stock])
qed

end
