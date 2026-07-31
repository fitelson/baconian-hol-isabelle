theory Bacon_PP_ZF_Tree_Multi_Indexed_Family_Off_Diagonal
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Collision.Bacon_PP_ZF_Tree_Multi_Indexed_Family_Collision
begin

section \<open>Only quotient-off-diagonal indexed collisions remain\<close>

theorem
  pp_t_diagonally_reflexive_multi_indexed_probes_stabilize_iff_off_diagonal_collisions_absorbed:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          \<alpha> i \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and diagonal:
      "\<And>i a p w.
        i \<in> I \<Longrightarrow>
        Elem a (pp_t_domain (\<alpha> i)) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds
          ((((pp_t_closed_den (B i) \<acute> a) \<acute> p) \<acute> p)) w"
  shows
    "(\<forall>i \<in> I.
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i))
    \<longleftrightarrow>
    (\<forall>i \<in> I. \<forall>j \<in> I. \<forall>a b p w.
      Elem a (pp_t_domain (\<alpha> i))
      \<longrightarrow>
      Elem b (pp_t_domain (\<alpha> j))
      \<longrightarrow>
      (j \<noteq> i \<or> \<not> pp_t_eqv (\<alpha> i) w b a)
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
          \<acute> b)
        ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
      \<longrightarrow>
      S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p))"
proof
  assume stable:
      "\<forall>i \<in> I.
        pp_t_indexed_family_probe_for_stock (\<alpha> i)
            (pp_t_multi_indexed_family_section_stock_enlargement
              S \<alpha> B I)
            (B i)
          =
          pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
  have all_collisions:
      "\<forall>i \<in> I. \<forall>a p w.
        Elem a (pp_t_domain (\<alpha> i))
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
              \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p))
        \<longrightarrow>
        S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    using
      pp_t_multi_indexed_family_probes_stabilize_iff_collision_matrix_absorbed[
        OF B_typed S_admissible]
      stable by (rule iffD1)
  show "\<forall>i \<in> I. \<forall>j \<in> I. \<forall>a b p w.
      Elem a (pp_t_domain (\<alpha> i))
      \<longrightarrow>
      Elem b (pp_t_domain (\<alpha> j))
      \<longrightarrow>
      (j \<noteq> i \<or> \<not> pp_t_eqv (\<alpha> i) w b a)
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
          \<acute> b)
        ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
      \<longrightarrow>
      S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    using all_collisions by blast
next
  assume off_diagonal:
      "\<forall>i \<in> I. \<forall>j \<in> I. \<forall>a b p w.
        Elem a (pp_t_domain (\<alpha> i))
        \<longrightarrow>
        Elem b (pp_t_domain (\<alpha> j))
        \<longrightarrow>
        (j \<noteq> i \<or> \<not> pp_t_eqv (\<alpha> i) w b a)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
            \<acute> b)
          ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
        \<longrightarrow>
        S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
  have all_collisions:
      "\<forall>i \<in> I. \<forall>a p w.
        Elem a (pp_t_domain (\<alpha> i))
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
              \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p))
        \<longrightarrow>
        S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
  proof (intro ballI allI impI)
    fix i a p w
    assume i: "i \<in> I"
      and a: "Elem a (pp_t_domain (\<alpha> i))"
      and p: "Elem p (pp_t_domain Prop)"
      and some_collision:
        "\<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
              \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    then obtain j b where j: "j \<in> I"
      and b: "Elem b (pp_t_domain (\<alpha> j))"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
            \<acute> b)
          ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
      by blast
    show "S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    proof (cases "j = i")
      case False
      have off:
          "j \<noteq> i \<or> \<not> pp_t_eqv (\<alpha> i) w b a"
        using False by blast
      show ?thesis
        using off_diagonal[rule_format,
          OF i j a b off p collision] .
    next
      case True
      note ji = True
      then have b_i: "Elem b (pp_t_domain (\<alpha> i))"
        using b by simp
      show ?thesis
      proof (cases "pp_t_eqv (\<alpha> i) w b a")
        case False
        have off: "j \<noteq> i \<or> \<not> pp_t_eqv (\<alpha> i) w b a"
          using False by blast
        show ?thesis
          using off_diagonal[rule_format,
            OF i j a b off p collision] .
      next
        case True
        have probe:
            "Elem
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i))
              (pp_t_domain
                (\<alpha> i \<rightarrow>\<^sub>o
                  pp_t_one_context_unary_type))"
          using pp_t_indexed_family_probe_for_stock_in_domain[
            OF B_typed[OF i] S_admissible] .
        have probe_b:
            "Elem
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> b)
              (pp_t_domain pp_t_one_context_unary_type)"
          using pp_t_indexed_family_probe_section_in_domain[
            OF B_typed[OF i] S_admissible b_i] .
        have probe_a:
            "Elem
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> a)
              (pp_t_domain pp_t_one_context_unary_type)"
          using pp_t_indexed_family_probe_section_in_domain[
            OF B_typed[OF i] S_admissible a] .
        have target:
            "Elem ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
              (pp_t_domain pp_t_one_context_unary_type)"
          using pp_t_indexed_family_value_in_domain_for_stock[
            OF B_typed[OF i] a p] .
        have probes:
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> b)
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> a)"
          using pp_t_arrow_member_respects[
            OF probe b_i a True] .
        have probes_sym:
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> a)
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> b)"
          using pp_t_eqv_symmetric[
            OF probe_b probe_a probes] .
        have collision_i:
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> b)
              ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
          using collision ji by simp
        have self_collision:
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_indexed_family_probe_for_stock
                (\<alpha> i) S (B i) \<acute> a)
              ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
          using pp_t_eqv_transitive[
            OF probe_a probe_b target probes_sym collision_i] .
        show ?thesis
          using pp_t_indexed_family_diagonal_collision_absorbed[
            OF B_typed[OF i] S_admissible a p
              diagonal[OF i a p] self_collision] .
      qed
    qed
  qed
  show "\<forall>i \<in> I.
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
    using
      pp_t_multi_indexed_family_probes_stabilize_iff_collision_matrix_absorbed[
        OF B_typed S_admissible]
      all_collisions by (rule iffD2)
qed

end
