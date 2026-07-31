theory Bacon_PP_ZF_Tree_Multi_Family_Off_Diagonal
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Collision_Characterization.Bacon_PP_ZF_Tree_Multi_Family_Collision_Characterization
begin

section \<open>Diagonal reflexivity leaves only off-diagonal collisions\<close>

theorem pp_t_diagonally_reflexive_multi_family_probes_stabilize_iff_off_diagonal_collisions_absorbed:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and diagonal:
      "\<And>i p w.
        i \<in> I \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds
          ((pp_t_closed_den (B i) \<acute> p) \<acute> p) w"
  shows
    "(\<forall>i \<in> I.
      pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i))
    \<longleftrightarrow>
    (\<forall>i \<in> I. \<forall>j \<in> I. \<forall>p w.
      j \<noteq> i
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S (B j))
        (pp_t_closed_den (B i) \<acute> p)
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p))"
proof
  assume stable:
      "\<forall>i \<in> I.
        pp_t_family_probe_for_stock
            (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
          = pp_t_family_probe_for_stock S (B i)"
  have criterion:
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
    using pp_t_multi_family_probes_stabilize_iff_cross_collision_matrix_absorbed[
      OF B_typed S_admissible] .
  have all_collisions:
      "\<forall>i \<in> I. \<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
    using criterion stable by (rule iffD1)
  show "\<forall>i \<in> I. \<forall>j \<in> I. \<forall>p w.
      j \<noteq> i
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S (B j))
        (pp_t_closed_den (B i) \<acute> p)
      \<longrightarrow>
      S w (pp_t_closed_den (B i) \<acute> p)"
  proof (intro ballI allI impI)
    fix i j p w
    assume i: "i \<in> I"
      and j: "j \<in> I"
      and p: "Elem p (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p)"
    have some_collision:
        "\<exists>k \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B k))
            (pp_t_closed_den (B i) \<acute> p)"
      using j collision by blast
    show "S w (pp_t_closed_den (B i) \<acute> p)"
      using all_collisions[rule_format, OF i p some_collision] .
  qed
next
  assume off_diagonal:
      "\<forall>i \<in> I. \<forall>j \<in> I. \<forall>p w.
        j \<noteq> i
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p)
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
  have all_collisions:
      "\<forall>i \<in> I. \<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p))
        \<longrightarrow>
        S w (pp_t_closed_den (B i) \<acute> p)"
  proof (intro ballI allI impI)
    fix i p w
    assume i: "i \<in> I"
      and p: "Elem p (pp_t_domain Prop)"
      and some_collision:
        "\<exists>j \<in> I.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B j))
            (pp_t_closed_den (B i) \<acute> p)"
    then obtain j where j: "j \<in> I"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S (B j))
          (pp_t_closed_den (B i) \<acute> p)"
      by blast
    show "S w (pp_t_closed_den (B i) \<acute> p)"
    proof (cases "j = i")
      case True
      have self_collision:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock S (B i))
            (pp_t_closed_den (B i) \<acute> p)"
        using collision True by simp
      show ?thesis
        using pp_t_family_probe_collision_absorbed[
          OF B_typed[OF i] S_admissible diagonal[OF i] p
            self_collision] .
    next
      case False
      show ?thesis
        using off_diagonal[rule_format, OF i j False p collision] .
    qed
  qed
  have criterion:
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
    using pp_t_multi_family_probes_stabilize_iff_cross_collision_matrix_absorbed[
      OF B_typed S_admissible] .
  show "\<forall>i \<in> I.
      pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement S B I) (B i)
        = pp_t_family_probe_for_stock S (B i)"
    using criterion all_collisions by (rule iffD2)
qed

end
