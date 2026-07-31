theory Bacon_PP_ZF_Tree_Indexed_Family_Anchor
  imports
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Collision.Bacon_PP_ZF_Tree_Indexed_Family_Collision
begin

section \<open>Uniform anchors absorb an indexed collision matrix\<close>

text \<open>
  A collision equates two unary operators and can therefore be tested at one
  common proposition.  If every old-stock probe section has the same truth
  value at that proposition, and that truth value forces every possible
  family value back into the old stock, then all indexed collisions are
  absorbed simultaneously.
\<close>

theorem pp_t_indexed_family_probe_stabilizes_from_true_anchor:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and q: "Elem q (pp_t_domain Prop)"
    and probe_true:
      "\<And>b w.
        Elem b (pp_t_domain \<alpha>) \<Longrightarrow>
        pp_t_holds
          ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            \<acute> q) w"
    and reflects_stock:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q) w
          \<Longrightarrow>
        S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
  shows
    "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B"
proof -
  have all_collisions:
      "\<forall>a p w.
        Elem a (pp_t_domain \<alpha>)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p))
        \<longrightarrow>
        S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
  proof (intro allI impI)
    fix a p w
    assume a: "Elem a (pp_t_domain \<alpha>)"
      and p: "Elem p (pp_t_domain Prop)"
      and some_collision:
        "\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
    then obtain b where b: "Elem b (pp_t_domain \<alpha>)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
          ((pp_t_closed_den B \<acute> a) \<acute> p)"
      by blast
    have qq: "pp_t_eqv Prop w q q"
      by (rule pp_t_eqv_reflexive[OF q])
    have applications:
        "pp_t_eqv Prop w
          ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            \<acute> q)
          (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q)"
      using pp_t_app_respects[OF collision q q qq] .
    have target_true:
        "pp_t_holds
          (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        probe_true[OF b, of w]
      by simp
    show "S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
      by (rule reflects_stock[OF a p target_true])
  qed
  show ?thesis
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF B_typed S_admissible]
      all_collisions by (rule iffD2)
qed

theorem pp_t_indexed_family_probe_stabilizes_from_false_anchor:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and q: "Elem q (pp_t_domain Prop)"
    and probe_false:
      "\<And>b w.
        Elem b (pp_t_domain \<alpha>) \<Longrightarrow>
        \<not> pp_t_holds
          ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            \<acute> q) w"
    and reflects_stock:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        \<not> pp_t_holds
          (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q) w
          \<Longrightarrow>
        S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
  shows
    "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B"
proof -
  have all_collisions:
      "\<forall>a p w.
        Elem a (pp_t_domain \<alpha>)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p))
        \<longrightarrow>
        S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
  proof (intro allI impI)
    fix a p w
    assume a: "Elem a (pp_t_domain \<alpha>)"
      and p: "Elem p (pp_t_domain Prop)"
      and some_collision:
        "\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
    then obtain b where b: "Elem b (pp_t_domain \<alpha>)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
          ((pp_t_closed_den B \<acute> a) \<acute> p)"
      by blast
    have qq: "pp_t_eqv Prop w q q"
      by (rule pp_t_eqv_reflexive[OF q])
    have applications:
        "pp_t_eqv Prop w
          ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            \<acute> q)
          (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q)"
      using pp_t_app_respects[OF collision q q qq] .
    have target_false:
        "\<not> pp_t_holds
          (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> q) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        probe_false[OF b, of w]
      by simp
    show "S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
      by (rule reflects_stock[OF a p target_false])
  qed
  show ?thesis
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF B_typed S_admissible]
      all_collisions by (rule iffD2)
qed

end
