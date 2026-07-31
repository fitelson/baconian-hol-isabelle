theory Bacon_PP_ZF_Tree_Multi_Indexed_Family_Collision
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Stock.Bacon_PP_ZF_Tree_Multi_Indexed_Family_Stock
begin

section \<open>Exact heterogeneous indexed collision matrix\<close>

theorem
  pp_t_one_multi_indexed_family_probe_stabilizes_iff_collisions_absorbed:
  assumes i: "i \<in> I"
    and B_typed:
      "\<And>j. j \<in> I \<Longrightarrow>
        [] \<turnstile> B j :
          \<alpha> j \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "pp_t_indexed_family_probe_for_stock (\<alpha> i)
        (pp_t_multi_indexed_family_section_stock_enlargement
          S \<alpha> B I)
        (B i)
      =
      pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
    \<longleftrightarrow>
    (\<forall>a p w.
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
      S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p))"
proof
  assume stable:
      "pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
  show "\<forall>a p w.
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
  proof (intro allI impI)
    fix a p w
    assume a: "Elem a (pp_t_domain (\<alpha> i))"
      and p: "Elem p (pp_t_domain Prop)"
      and collision:
        "\<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
              \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    have enlarged_member:
        "pp_t_multi_indexed_family_section_stock_enlargement
          S \<alpha> B I w
          ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
      using collision
      unfolding
        pp_t_multi_indexed_family_section_stock_enlargement_def
      by blast
    have reevaluated_true:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock (\<alpha> i)
              (pp_t_multi_indexed_family_section_stock_enlargement
                S \<alpha> B I)
              (B i) \<acute> a) \<acute> p) w"
      using pp_t_indexed_family_probe_for_stock_apply_holds[
        OF B_typed[OF i]
          pp_t_multi_indexed_family_section_stock_enlargement_admissible[
            where I=I and \<alpha>=\<alpha> and B=B and S=S,
            OF B_typed S_admissible]
          a p,
        of w]
        enlarged_member by blast
    have old_true:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
              \<acute> a) \<acute> p) w"
      using reevaluated_true unfolding stable .
    show "S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
      using pp_t_indexed_family_probe_for_stock_apply_holds[
        OF B_typed[OF i] S_admissible a p, of w]
        old_true by blast
  qed
next
  assume absorbed:
      "\<forall>a p w.
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
  show "pp_t_indexed_family_probe_for_stock (\<alpha> i)
        (pp_t_multi_indexed_family_section_stock_enlargement
          S \<alpha> B I)
        (B i)
      =
      pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
  proof (rule pp_t_indexed_unary_function_ext)
    show "Elem
        (pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i))
        (pp_t_domain
          (\<alpha> i \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
      using pp_t_indexed_family_probe_for_stock_in_domain[
        OF B_typed[OF i]
          pp_t_multi_indexed_family_section_stock_enlargement_admissible[
            where I=I and \<alpha>=\<alpha> and B=B and S=S,
            OF B_typed S_admissible]] .
    show "Elem
        (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i))
        (pp_t_domain
          (\<alpha> i \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
      using pp_t_indexed_family_probe_for_stock_in_domain[
        OF B_typed[OF i] S_admissible] .
    fix a
    assume a: "Elem a (pp_t_domain (\<alpha> i))"
    show "pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i) \<acute> a
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
          \<acute> a"
    proof (rule pp_t_unary_function_ext)
      show "Elem
          (pp_t_indexed_family_probe_for_stock (\<alpha> i)
            (pp_t_multi_indexed_family_section_stock_enlargement
              S \<alpha> B I)
            (B i) \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_app_closed[
          OF pp_t_indexed_family_probe_for_stock_in_domain[
            OF B_typed[OF i]
              pp_t_multi_indexed_family_section_stock_enlargement_admissible[
                where I=I and \<alpha>=\<alpha> and B=B and S=S,
                OF B_typed S_admissible]]
            a] .
      show "Elem
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_indexed_family_probe_section_in_domain[
          OF B_typed[OF i] S_admissible a] .
      fix p
      assume p: "Elem p (pp_t_domain Prop)"
      show "(pp_t_indexed_family_probe_for_stock (\<alpha> i)
              (pp_t_multi_indexed_family_section_stock_enlargement
                S \<alpha> B I)
              (B i) \<acute> a) \<acute> p
          =
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a) \<acute> p"
      proof (rule pp_t_prop_ext)
        show "Elem
            ((pp_t_indexed_family_probe_for_stock (\<alpha> i)
                (pp_t_multi_indexed_family_section_stock_enlargement
                  S \<alpha> B I)
                (B i) \<acute> a) \<acute> p)
            (pp_t_domain Prop)"
          using pp_t_app_closed[
            OF pp_t_app_closed[
              OF pp_t_indexed_family_probe_for_stock_in_domain[
                OF B_typed[OF i]
                  pp_t_multi_indexed_family_section_stock_enlargement_admissible[
                    where I=I and \<alpha>=\<alpha> and B=B and S=S,
                    OF B_typed S_admissible]]
                a]
              p] .
        show "Elem
            ((pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
                \<acute> a) \<acute> p)
            (pp_t_domain Prop)"
          using pp_t_app_closed[
            OF pp_t_indexed_family_probe_section_in_domain[
              OF B_typed[OF i] S_admissible a]
            p] .
        fix w
        have enlarged:
            "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock (\<alpha> i)
                  (pp_t_multi_indexed_family_section_stock_enlargement
                    S \<alpha> B I)
                  (B i) \<acute> a) \<acute> p) w
            \<longleftrightarrow>
            pp_t_multi_indexed_family_section_stock_enlargement
              S \<alpha> B I w
              ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
          using pp_t_indexed_family_probe_for_stock_apply_holds[
            OF B_typed[OF i]
              pp_t_multi_indexed_family_section_stock_enlargement_admissible[
                where I=I and \<alpha>=\<alpha> and B=B and S=S,
                OF B_typed S_admissible]
              a p,
            of w] .
        have old:
            "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
                  \<acute> a) \<acute> p) w
            \<longleftrightarrow>
            S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
          using pp_t_indexed_family_probe_for_stock_apply_holds[
            OF B_typed[OF i] S_admissible a p, of w] .
        show "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock (\<alpha> i)
                  (pp_t_multi_indexed_family_section_stock_enlargement
                    S \<alpha> B I)
                  (B i) \<acute> a) \<acute> p) w
            \<longleftrightarrow>
            pp_t_holds
              ((pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
                  \<acute> a) \<acute> p) w"
          using enlarged old absorbed[rule_format, OF a p, of w]
          unfolding
            pp_t_multi_indexed_family_section_stock_enlargement_def
          by blast
      qed
    qed
  qed
qed

theorem
  pp_t_multi_indexed_family_probes_stabilize_iff_collision_matrix_absorbed:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          \<alpha> i \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "(\<forall>i \<in> I.
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i))
    \<longleftrightarrow>
    (\<forall>i \<in> I. \<forall>a p w.
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
  show "\<forall>i \<in> I. \<forall>a p w.
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
  proof (intro ballI)
    fix i
    assume i: "i \<in> I"
    show "\<forall>a p w.
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
        pp_t_one_multi_indexed_family_probe_stabilizes_iff_collisions_absorbed[
          OF i B_typed S_admissible]
        stable[rule_format, OF i]
      by (rule iffD1)
  qed
next
  assume absorbed:
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
  show "\<forall>i \<in> I.
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
  proof (intro ballI)
    fix i
    assume i: "i \<in> I"
    have absorbed_i:
        "\<forall>a p w.
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
      using absorbed i by blast
    show "pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            S \<alpha> B I)
          (B i)
        =
        pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)"
      using
        pp_t_one_multi_indexed_family_probe_stabilizes_iff_collisions_absorbed[
          OF i B_typed S_admissible]
        absorbed_i
      by (rule iffD2)
  qed
qed

end
