theory Bacon_PP_ZF_Tree_Multi_Family_Collision_Sufficiency
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Necessity.Bacon_PP_ZF_Tree_Multi_Family_Collision_Necessity
begin

section \<open>Sufficiency of cross-collision absorption\<close>

theorem pp_t_cross_collisions_absorbed_implies_one_multi_family_probe_stable:
  assumes i: "i \<in> I"
    and B_typed:
      "\<And>j. j \<in> I \<Longrightarrow>
        [] \<turnstile> B j :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and absorbed:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
  shows "pp_t_family_probe_for_stock
      (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
    = pp_t_family_probe_for_stock S (B i)"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock
        (pp_t_multi_family_probe_stock_enlargement S B I) (B i))
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed[OF i]
        pp_t_multi_family_probe_stock_enlargement_admissible[
          OF B_typed S_admissible]] .
  show "Elem (pp_t_family_probe_for_stock S (B i))
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed[OF i] S_admissible] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock
        (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        \<acute> p
      = pp_t_family_probe_for_stock S (B i) \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
          \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF B_typed[OF i]
            pp_t_multi_family_probe_stock_enlargement_admissible[
              OF B_typed S_admissible]]
          p] .
    show "Elem
        (pp_t_family_probe_for_stock S (B i) \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF B_typed[OF i] S_admissible] p] .
    fix w
    have enlarged:
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
    have old:
        "pp_t_holds
          (pp_t_family_probe_for_stock S (B i) \<acute> p) w
        \<longleftrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
      using pp_t_family_probe_for_stock_apply_holds[
        OF B_typed[OF i] S_admissible p, of w] .
    have membership:
        "pp_t_multi_family_probe_stock_enlargement S B I w
            (pp_t_closed_den (B i) \<acute> p)
        \<longleftrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
    proof
      assume enlarged_member:
          "pp_t_multi_family_probe_stock_enlargement S B I w
            (pp_t_closed_den (B i) \<acute> p)"
      show "S w (pp_t_closed_den (B i) \<acute> p)"
      proof (cases "S w (pp_t_closed_den (B i) \<acute> p)")
        case True
        then show ?thesis .
      next
        case False
        have collision:
            "\<exists>j \<in> I.
              pp_t_eqv pp_t_one_context_unary_type w
                (pp_t_family_probe_for_stock S (B j))
                (pp_t_closed_den (B i) \<acute> p)"
          using enlarged_member False
          unfolding pp_t_multi_family_probe_stock_enlargement_def
          by blast
        show ?thesis
          using absorbed[rule_format, OF p collision] .
      qed
    next
      assume old_member:
          "S w (pp_t_closed_den (B i) \<acute> p)"
      show "pp_t_multi_family_probe_stock_enlargement S B I w
          (pp_t_closed_den (B i) \<acute> p)"
        using old_member
        unfolding pp_t_multi_family_probe_stock_enlargement_def
        by blast
    qed
    show "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
            \<acute> p) w
      \<longleftrightarrow>
      pp_t_holds
        (pp_t_family_probe_for_stock S (B i) \<acute> p) w"
      using enlarged old membership by blast
  qed
qed

end
