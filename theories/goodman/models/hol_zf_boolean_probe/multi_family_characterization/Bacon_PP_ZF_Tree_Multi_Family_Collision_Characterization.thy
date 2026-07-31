theory Bacon_PP_ZF_Tree_Multi_Family_Collision_Characterization
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Sufficiency.Bacon_PP_ZF_Tree_Multi_Family_Collision_Sufficiency
begin

section \<open>Exact cross-collision characterizations\<close>

theorem pp_t_one_multi_family_probe_stabilizes_iff_cross_collisions_absorbed:
  assumes i: "i \<in> I"
    and B_typed:
      "\<And>j. j \<in> I \<Longrightarrow>
        [] \<turnstile> B j :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "pp_t_family_probe_for_stock
        (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
      = pp_t_family_probe_for_stock S (B i)
    \<longleftrightarrow>
    (\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (\<exists>j \<in> I.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p))
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p))"
proof
  assume stable:
      "pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i)"
  show "\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (\<exists>j \<in> I.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p))
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p)"
    using pp_t_one_multi_family_probe_stability_implies_cross_collisions_absorbed[
      OF i B_typed S_admissible stable] .
next
  assume absorbed:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
  show "pp_t_family_probe_for_stock
        (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
      = pp_t_family_probe_for_stock S (B i)"
    using pp_t_cross_collisions_absorbed_implies_one_multi_family_probe_stable[
      OF i B_typed S_admissible absorbed] .
qed

theorem pp_t_multi_family_probes_stabilize_iff_cross_collision_matrix_absorbed:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "(\<forall>i \<in> I.
      pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i))
    \<longleftrightarrow>
    (\<forall>i \<in> I. \<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (\<exists>j \<in> I.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p))
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p))"
proof
  assume stable:
      "\<forall>i \<in> I.
        pp_t_family_probe_for_stock
            (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
          = pp_t_family_probe_for_stock S (B i)"
  show "\<forall>i \<in> I. \<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (\<exists>j \<in> I.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p))
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p)"
  proof (intro ballI)
    fix i
    assume i: "i \<in> I"
    show "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
      using pp_t_one_multi_family_probe_stability_implies_cross_collisions_absorbed[
        OF i B_typed S_admissible stable[rule_format, OF i]] .
  qed
next
  assume absorbed:
      "\<forall>i \<in> I. \<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
  show "\<forall>i \<in> I.
      pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i)"
  proof (intro ballI)
    fix i
    assume i: "i \<in> I"
    have absorbed_i:
        "\<forall>p w.
          Elem p (pp_t_domain Prop)
          \<longrightarrow>
          (\<exists>j \<in> I.
            pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_family_probe_for_stock S (B j))
              (pp_t_closed_den (B i) \<acute> p))
          \<longrightarrow>
          S w (pp_t_closed_den (B i) \<acute> p)"
      using absorbed i by blast
    show "pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i)"
      using pp_t_cross_collisions_absorbed_implies_one_multi_family_probe_stable[
        OF i B_typed S_admissible absorbed_i] .
  qed
qed

end
