theory Bacon_PP_ZF_Tree_Boolean_Probe_Collision
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Classification.Bacon_PP_ZF_Tree_Boolean_Probe_Classification
begin

section \<open>The remaining stabilization condition\<close>

definition pp_t_probe_boolean_family_probe :: ZF where
  "pp_t_probe_boolean_family_probe =
    pp_t_family_probe_for_stock
      pp_t_probe_boolean_stock
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_probe_boolean_family_probe_in_domain:
  "Elem pp_t_probe_boolean_family_probe
    (pp_t_domain pp_t_boolean_probe_unary_type)"
  unfolding pp_t_probe_boolean_family_probe_def
  by (rule pp_t_family_probe_for_stock_in_domain[
    OF pp_t_symmetrized_singleton_family_builder_typed
      pp_t_probe_boolean_stock_admissible])

lemma pp_t_probe_boolean_classifier_cone_natural:
  "pp_t_cone_rel
    (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop) s
    (pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_stock)
    (pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_stock)"
  unfolding pp_t_cone_rel.simps
  apply (intro allI impI)
  apply (subst pp_t_classifier_holds)
   apply assumption
  apply (subst pp_t_classifier_holds)
   apply assumption
  apply (rule pp_t_probe_boolean_stock_cone_iff)
    apply assumption+
  apply (fold pp_t_cone_rel.simps)
  apply (fold pp_t_cone_rel.simps)
  apply assumption
  done

lemma pp_t_probe_boolean_family_probe_cone_natural:
  "pp_t_cone_rel pp_t_boolean_probe_unary_type s
    pp_t_probe_boolean_family_probe
    pp_t_probe_boolean_family_probe"
proof -
  let ?builder =
    "pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder)"
  let ?classifier =
    "pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_stock"
  have builder:
      "pp_t_cone_rel
        ((pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) s
        ?builder ?builder"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_family_probe_builder_typed[
            OF pp_t_symmetrized_singleton_family_builder_typed]
          pp_t_family_probe_builder_logical[
            OF pp_t_symmetrized_singleton_family_builder_logical]])
  have classifier_domain:
      "Elem ?classifier
        (pp_t_domain
          (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain)
      (rule pp_t_probe_boolean_stock_admissible)
  have applied:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s
        (?builder \<acute> ?classifier)
        (?builder \<acute> ?classifier)"
    using builder classifier_domain
      pp_t_probe_boolean_classifier_cone_natural
    by auto
  show ?thesis
    using applied
    unfolding pp_t_probe_boolean_family_probe_def
      pp_t_family_probe_for_stock_def
    by simp
qed

theorem
  pp_t_probe_boolean_root_collision_parameter_classification:
  assumes p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at p)"
  shows "p =
    pp_t_word_character_prop
      (pp_t_holds p [])
      (pp_t_holds p [True] \<noteq> pp_t_holds p [])
      (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
proof -
  have family_domain:
      "Elem (pp_t_symmetrized_singleton_family_at p)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule
      pp_t_symmetrized_singleton_family_at_in_domain[OF p])
  have equality:
      "pp_t_probe_boolean_family_probe =
        pp_t_symmetrized_singleton_family_at p"
    by (rule pp_t_root_eqv_imp_eq[
      OF pp_t_probe_boolean_family_probe_in_domain
        family_domain collision])
  have family_cone:
      "\<And>s.
        pp_t_cone_rel pp_t_boolean_probe_unary_type s
          (pp_t_symmetrized_singleton_family_at p)
          (pp_t_symmetrized_singleton_family_at p)"
    using pp_t_probe_boolean_family_probe_cone_natural
    unfolding equality .
  have stable:
      "pp_t_family_same_value_on_relative_views
        pp_t_symmetrized_singleton_family_builder [] p"
    unfolding pp_t_family_same_value_on_relative_views_def
      pp_t_cone_view_empty[OF p]
  proof
    fix s
    show "pp_t_symmetrized_singleton_family_at
          (pp_t_cone_view s p)
        =
        pp_t_symmetrized_singleton_family_at p"
      by (rule
        pp_t_logical_family_cone_natural_forces_same_value[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_singleton_family_builder_logical
            p family_cone])
  qed
  show ?thesis
    by (rule
      pp_t_symmetrized_family_stable_parameter_is_word_character[
        OF p stable])
qed

theorem pp_t_probe_boolean_family_stabilizes_iff_collisions_absorbed:
  "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement
        pp_t_probe_boolean_stock
        pp_t_symmetrized_singleton_family_builder)
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_probe_boolean_family_probe
  \<longleftrightarrow>
  (\<forall>p w.
    Elem p (pp_t_domain Prop)
    \<longrightarrow>
    pp_t_eqv pp_t_boolean_probe_unary_type w
      pp_t_probe_boolean_family_probe
      (pp_t_symmetrized_singleton_family_at p)
    \<longrightarrow>
    pp_t_probe_boolean_stock w
      (pp_t_symmetrized_singleton_family_at p))"
  unfolding pp_t_probe_boolean_family_probe_def
  by (rule
    pp_t_family_probe_stabilizes_iff_collisions_absorbed[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_boolean_stock_admissible])

end
