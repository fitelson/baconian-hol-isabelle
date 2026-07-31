theory Bacon_PP_ZF_Tree_Indexed_Family_Collision
  imports
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Stock_Probe.Bacon_PP_ZF_Tree_Indexed_Family_Stock_Probe
begin

section \<open>Exact collision criterion for uniformly indexed families\<close>

text \<open>
  A single closed family builder may range over every semantic object of an
  object-language type.  Adjoining all sections of its classifier probe
  therefore creates a possibly infinite matrix of collisions, even though the
  builder itself is one finite term.  The next theorem identifies that matrix
  exactly.
\<close>

theorem pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B
    \<longleftrightarrow>
    (\<forall>a p w.
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
      S w ((pp_t_closed_den B \<acute> a) \<acute> p))"
proof
  assume stable:
      "pp_t_indexed_family_probe_for_stock \<alpha>
          (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
        =
        pp_t_indexed_family_probe_for_stock \<alpha> S B"
  show "\<forall>a p w.
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
      and collision:
        "\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
    have enlarged_member:
        "pp_t_indexed_family_section_stock_enlargement \<alpha> S B w
          ((pp_t_closed_den B \<acute> a) \<acute> p)"
      using collision
      unfolding pp_t_indexed_family_section_stock_enlargement_def
      by blast
    have reevaluated_true:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock \<alpha>
              (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
              \<acute> a) \<acute> p) w"
      using pp_t_indexed_family_probe_for_stock_apply_holds[
        OF B_typed
          pp_t_indexed_family_section_stock_enlargement_admissible[
            OF B_typed S_admissible]
          a p,
        of w]
        enlarged_member by blast
    have old_true:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            \<acute> p) w"
      using reevaluated_true unfolding stable .
    show "S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
      using pp_t_indexed_family_probe_for_stock_apply_holds[
        OF B_typed S_admissible a p, of w]
        old_true by blast
  qed
next
  assume absorbed:
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
  show "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B"
  proof (rule pp_t_indexed_unary_function_ext)
    show "Elem
        (pp_t_indexed_family_probe_for_stock \<alpha>
          (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B)
        (pp_t_domain
          (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
      using pp_t_indexed_family_probe_for_stock_in_domain[
        OF B_typed
          pp_t_indexed_family_section_stock_enlargement_admissible[
            OF B_typed S_admissible]] .
    show "Elem (pp_t_indexed_family_probe_for_stock \<alpha> S B)
        (pp_t_domain
          (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
      using pp_t_indexed_family_probe_for_stock_in_domain[
        OF B_typed S_admissible] .
    fix a
    assume a: "Elem a (pp_t_domain \<alpha>)"
    show "pp_t_indexed_family_probe_for_stock \<alpha>
          (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
          \<acute> a
        =
        pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a"
    proof (rule pp_t_unary_function_ext)
      show "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha>
            (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
            \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_app_closed[
          OF pp_t_indexed_family_probe_for_stock_in_domain[
            OF B_typed
              pp_t_indexed_family_section_stock_enlargement_admissible[
                OF B_typed S_admissible]]
            a] .
      show "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_indexed_family_probe_section_in_domain[
          OF B_typed S_admissible a] .
      fix p
      assume p: "Elem p (pp_t_domain Prop)"
      show "(pp_t_indexed_family_probe_for_stock \<alpha>
              (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
              \<acute> a) \<acute> p
          =
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            \<acute> p"
      proof (rule pp_t_prop_ext)
        show "Elem
            ((pp_t_indexed_family_probe_for_stock \<alpha>
                (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
                \<acute> a) \<acute> p)
            (pp_t_domain Prop)"
          using pp_t_app_closed[
            OF pp_t_app_closed[
              OF pp_t_indexed_family_probe_for_stock_in_domain[
                OF B_typed
                  pp_t_indexed_family_section_stock_enlargement_admissible[
                    OF B_typed S_admissible]]
                a]
              p] .
        show "Elem
            ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
              \<acute> p)
            (pp_t_domain Prop)"
          using pp_t_app_closed[
            OF pp_t_indexed_family_probe_section_in_domain[
              OF B_typed S_admissible a]
            p] .
        fix w
        have enlarged:
            "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock \<alpha>
                  (pp_t_indexed_family_section_stock_enlargement \<alpha> S B)
                  B \<acute> a) \<acute> p) w
            \<longleftrightarrow>
            pp_t_indexed_family_section_stock_enlargement \<alpha> S B w
              ((pp_t_closed_den B \<acute> a) \<acute> p)"
          using pp_t_indexed_family_probe_for_stock_apply_holds[
            OF B_typed
              pp_t_indexed_family_section_stock_enlargement_admissible[
                OF B_typed S_admissible]
              a p,
            of w] .
        have old:
            "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
                \<acute> p) w
            \<longleftrightarrow>
            S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
          using pp_t_indexed_family_probe_for_stock_apply_holds[
            OF B_typed S_admissible a p, of w] .
        show "pp_t_holds
              ((pp_t_indexed_family_probe_for_stock \<alpha>
                  (pp_t_indexed_family_section_stock_enlargement \<alpha> S B)
                  B \<acute> a) \<acute> p) w
            \<longleftrightarrow>
            pp_t_holds
              ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
                \<acute> p) w"
          using enlarged old absorbed[rule_format, OF a p, of w]
          unfolding pp_t_indexed_family_section_stock_enlargement_def
          by blast
      qed
    qed
  qed
qed

lemma pp_t_indexed_family_diagonal_collision_absorbed:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
    and diagonal:
      "\<And>v. pp_t_holds
        ((((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> p)) v"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
        ((pp_t_closed_den B \<acute> a) \<acute> p)"
  shows "S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
proof -
  have pp: "pp_t_eqv Prop w p p"
    using pp_t_eqv_reflexive[OF p] .
  have applications:
      "pp_t_eqv Prop w
        ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) \<acute> p)
        (((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> p)"
    using collision p pp by auto
  have probe_true:
      "pp_t_holds
        ((pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      diagonal[of w]
    by simp
  show ?thesis
    using pp_t_indexed_family_probe_for_stock_apply_holds[
      OF B_typed S_admissible a p, of w]
      probe_true by blast
qed

theorem
  pp_t_diagonally_reflexive_indexed_family_probe_stabilizes_iff_quotient_off_diagonal_collisions_absorbed:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and diagonal:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds
          ((((pp_t_closed_den B \<acute> a) \<acute> p) \<acute> p)) w"
  shows
    "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B
    \<longleftrightarrow>
    (\<forall>a b p w.
      Elem a (pp_t_domain \<alpha>)
      \<longrightarrow>
      Elem b (pp_t_domain \<alpha>)
      \<longrightarrow>
      \<not> pp_t_eqv \<alpha> w b a
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
        ((pp_t_closed_den B \<acute> a) \<acute> p)
      \<longrightarrow>
      S w ((pp_t_closed_den B \<acute> a) \<acute> p))"
proof
  assume stable:
      "pp_t_indexed_family_probe_for_stock \<alpha>
          (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
        =
        pp_t_indexed_family_probe_for_stock \<alpha> S B"
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
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF B_typed S_admissible]
      stable by (rule iffD1)
  show "\<forall>a b p w.
      Elem a (pp_t_domain \<alpha>)
      \<longrightarrow>
      Elem b (pp_t_domain \<alpha>)
      \<longrightarrow>
      \<not> pp_t_eqv \<alpha> w b a
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
        ((pp_t_closed_den B \<acute> a) \<acute> p)
      \<longrightarrow>
      S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
    using all_collisions by blast
next
  assume off_diagonal:
      "\<forall>a b p w.
        Elem a (pp_t_domain \<alpha>)
        \<longrightarrow>
        Elem b (pp_t_domain \<alpha>)
        \<longrightarrow>
        \<not> pp_t_eqv \<alpha> w b a
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
          ((pp_t_closed_den B \<acute> a) \<acute> p)
        \<longrightarrow>
        S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
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
    show "S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
    proof (cases "pp_t_eqv \<alpha> w b a")
      case True
      have probe:
          "Elem (pp_t_indexed_family_probe_for_stock \<alpha> S B)
            (pp_t_domain
              (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
        using pp_t_indexed_family_probe_for_stock_in_domain[
          OF B_typed S_admissible] .
      have probe_b:
          "Elem
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_indexed_family_probe_section_in_domain[
          OF B_typed S_admissible b] .
      have probe_a:
          "Elem
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_indexed_family_probe_section_in_domain[
          OF B_typed S_admissible a] .
      have value_dom:
          "Elem ((pp_t_closed_den B \<acute> a) \<acute> p)
            (pp_t_domain pp_t_one_context_unary_type)"
        using pp_t_indexed_family_value_in_domain_for_stock[
          OF B_typed a p] .
      have probes:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)"
        using pp_t_arrow_member_respects[
          OF probe b a True] .
      have probes_sym:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)"
        using pp_t_eqv_symmetric[
          OF probe_b probe_a probes] .
      have self_collision:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
        using pp_t_eqv_transitive[
          OF probe_a probe_b value_dom probes_sym collision] .
      show ?thesis
        using pp_t_indexed_family_diagonal_collision_absorbed[
          OF B_typed S_admissible a p diagonal[OF a p]
            self_collision] .
    next
      case False
      show ?thesis
        using off_diagonal[rule_format,
          OF a b False p collision] .
    qed
  qed
  show "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha> S B) B
      =
      pp_t_indexed_family_probe_for_stock \<alpha> S B"
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF B_typed S_admissible]
      all_collisions by (rule iffD2)
qed

end
