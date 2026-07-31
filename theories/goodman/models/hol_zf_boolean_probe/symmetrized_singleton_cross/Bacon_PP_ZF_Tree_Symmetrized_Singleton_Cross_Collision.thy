theory Bacon_PP_ZF_Tree_Symmetrized_Singleton_Cross_Collision
  imports
    Higher_Order_Metaphysics_PP_ZF_Symmetrized_Pair_Simultaneous_Absorption.Bacon_PP_ZF_Tree_Symmetrized_Pair_Simultaneous_Absorption
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Singleton_Family_Elimination
begin

section \<open>The symmetrized probe cannot be a singleton-family value\<close>

lemma pp_t_symmetrized_closed_stock_probe_apply_complement:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_symmetrized_closed_stock_probe
      \<acute> pp_t_complement p
    = pp_t_symmetrized_closed_stock_probe \<acute> p"
proof (rule pp_t_prop_ext)
  show "Elem
      (pp_t_symmetrized_closed_stock_probe
        \<acute> pp_t_complement p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_symmetrized_closed_stock_probe_in_domain
        pp_t_complement_in_domain] .
  show "Elem
      (pp_t_symmetrized_closed_stock_probe \<acute> p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_symmetrized_closed_stock_probe_in_domain p] .
  fix w
  have complemented:
      "pp_t_holds
          (pp_t_symmetrized_closed_stock_probe
            \<acute> pp_t_complement p) w
      \<longleftrightarrow>
      pp_t_closed_logical_stock pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at
          (pp_t_complement p))"
    unfolding pp_t_symmetrized_closed_stock_probe_def
    using pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible
        pp_t_complement_in_domain] .
  have original:
      "pp_t_holds
          (pp_t_symmetrized_closed_stock_probe \<acute> p) w
      \<longleftrightarrow>
      pp_t_closed_logical_stock pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_symmetrized_closed_stock_probe_def
    using pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible p] .
  show "pp_t_holds
        (pp_t_symmetrized_closed_stock_probe
          \<acute> pp_t_complement p) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_symmetrized_closed_stock_probe \<acute> p) w"
    using complemented original
      pp_t_symmetrized_singleton_family_at_complement[OF p]
    by simp
qed

lemma pp_t_proposition_not_equivalent_to_its_complement:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv Prop w (pp_t_complement p) p"
proof
  assume equivalent:
      "pp_t_eqv Prop w (pp_t_complement p) p"
  have same_truth:
      "pp_t_holds (pp_t_complement p) w =
        pp_t_holds p w"
    using pp_t_prop_eqv_at[OF equivalent, of w]
    by simp
  show False
    using same_truth
    by (simp add: pp_t_complement_def)
qed

theorem pp_t_symmetrized_probe_has_no_singleton_family_collision:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    pp_t_symmetrized_closed_stock_probe
    (pp_t_singleton_family_at p)"
proof
  assume collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_symmetrized_closed_stock_probe
        (pp_t_singleton_family_at p)"
  have probe:
      "Elem pp_t_symmetrized_closed_stock_probe
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  have singleton:
      "Elem (pp_t_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_singleton_family_at_in_domain[OF p] .
  have pp: "pp_t_eqv Prop w p p"
    using pp_t_eqv_reflexive[OF p] .
  have at_p:
      "pp_t_eqv Prop w
        (pp_t_symmetrized_closed_stock_probe \<acute> p)
        (pp_t_singleton_family_at p \<acute> p)"
    using collision p pp by auto
  have singleton_at_p:
      "pp_t_holds (pp_t_singleton_family_at p \<acute> p) w"
    using pp_t_singleton_family_at_apply_holds[OF p p, of w]
      pp by blast
  have probe_at_p:
      "pp_t_holds
        (pp_t_symmetrized_closed_stock_probe \<acute> p) w"
    using pp_t_prop_eqv_at[OF at_p, of w]
      singleton_at_p by simp
  have complement_p:
      "Elem (pp_t_complement p) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have complement_self:
      "pp_t_eqv Prop w
        (pp_t_complement p) (pp_t_complement p)"
    using pp_t_eqv_reflexive[OF complement_p] .
  have at_complement:
      "pp_t_eqv Prop w
        (pp_t_symmetrized_closed_stock_probe
          \<acute> pp_t_complement p)
        (pp_t_singleton_family_at p
          \<acute> pp_t_complement p)"
    using collision complement_p complement_self by auto
  have singleton_at_complement:
      "\<not> pp_t_holds
        (pp_t_singleton_family_at p
          \<acute> pp_t_complement p) w"
    using pp_t_singleton_family_at_apply_holds[
      OF p complement_p, of w]
      pp_t_proposition_not_equivalent_to_its_complement[OF p]
    by blast
  have probe_at_complement:
      "\<not> pp_t_holds
        (pp_t_symmetrized_closed_stock_probe
          \<acute> pp_t_complement p) w"
    using pp_t_prop_eqv_at[OF at_complement, of w]
      singleton_at_complement by simp
  show False
    using probe_at_p probe_at_complement
      pp_t_symmetrized_closed_stock_probe_apply_complement[OF p]
    by simp
qed

end
