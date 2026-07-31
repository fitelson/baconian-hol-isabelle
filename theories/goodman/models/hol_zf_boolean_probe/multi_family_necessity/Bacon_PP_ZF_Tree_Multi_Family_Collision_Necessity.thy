theory Bacon_PP_ZF_Tree_Multi_Family_Collision_Necessity
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Absorption.Bacon_PP_ZF_Tree_Multi_Family_Absorption
begin

section \<open>Necessity of cross-collision absorption\<close>

theorem pp_t_one_multi_family_probe_stability_implies_cross_collisions_absorbed:
  assumes i: "i \<in> I"
    and B_typed:
      "\<And>j. j \<in> I \<Longrightarrow>
        [] \<turnstile> B j :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and stable:
      "pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i)"
  shows "\<forall>p w.
    Elem p (pp_t_domain Prop)
    \<longrightarrow>
    (\<exists>j \<in> I.
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S (B j))
        (pp_t_closed_den (B i) \<acute> p))
    \<longrightarrow>
    S w (pp_t_closed_den (B i) \<acute> p)"
proof (intro allI impI)
  fix p w
  assume p: "Elem p (pp_t_domain Prop)"
    and collision:
      "\<exists>j \<in> I.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p)"
  have enlarged_member:
      "pp_t_multi_family_probe_stock_enlargement S B I w
        (pp_t_closed_den (B i) \<acute> p)"
    using collision
    unfolding pp_t_multi_family_probe_stock_enlargement_def
    by blast
  have reevaluated:
      "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
            \<acute> p) w
      \<longleftrightarrow>
      pp_t_multi_family_probe_stock_enlargement S B I w
        (pp_t_closed_den (B i) \<acute> p)"
    using pp_t_family_probe_for_stock_apply_holds[
      OF B_typed[OF i]
        pp_t_multi_family_probe_stock_enlargement_admissible[
          OF B_typed S_admissible]
        p] .
  have reevaluated_true:
      "pp_t_holds
        (pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
          \<acute> p) w"
    using reevaluated enlarged_member by blast
  have old_true:
      "pp_t_holds
        (pp_t_family_probe_for_stock S (B i) \<acute> p) w"
    using reevaluated_true stable by simp
  have old:
      "pp_t_holds
          (pp_t_family_probe_for_stock S (B i) \<acute> p) w
      \<longleftrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p)"
    using pp_t_family_probe_for_stock_apply_holds[
      OF B_typed[OF i] S_admissible p, of w] .
  show "S w (pp_t_closed_den (B i) \<acute> p)"
    using old old_true by blast
qed

end
