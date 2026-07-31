theory Bacon_PP_ZF_Tree_Family_View_Definability
  imports Bacon_PP_ZF_Tree_Inverse_Cone_Naturality
begin

section \<open>When preservation of a family value characterizes purity\<close>

text \<open>
  For a closed logical family \<open>B\<close>, membership of \<open>B p\<close> in the
  closed logical unary stock implies that every further cone view of the
  current view of \<open>p\<close> has the same value under \<open>B\<close>.  The converse is
  an additional completeness property of the range of \<open>B\<close>.  This section
  identifies that property and proves that it is exactly what is needed.
\<close>

lemma pp_t_cone_view_empty:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_cone_view [] p = p"
  unfolding pp_t_cone_view_def
  using pp_zf_of_b_of_zf[OF p] by simp

definition pp_t_family_same_value_on_relative_views ::
    "oterm \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_family_same_value_on_relative_views B w p \<longleftrightarrow>
    (\<forall>s.
      pp_t_closed_den B \<acute>
          pp_t_cone_view s (pp_t_cone_view w p) =
        pp_t_closed_den B \<acute> pp_t_cone_view w p)"

definition pp_t_family_view_complete :: "oterm \<Rightarrow> bool" where
  "pp_t_family_view_complete B \<longleftrightarrow>
    (\<forall>p.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_family_same_value_on_relative_views B [] p
      \<longrightarrow>
      pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p))"

definition pp_t_family_view_condition_definable ::
    "oterm \<Rightarrow> bool"
where
  "pp_t_family_view_condition_definable B \<longleftrightarrow>
    (\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> (\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (pp_t_holds (pp_t_closed_den S \<acute> p) w
          \<longleftrightarrow>
         pp_t_family_same_value_on_relative_views B w p)))"

definition pp_t_family_probe_has_closed_logical_definition ::
    "oterm \<Rightarrow> bool"
where
  "pp_t_family_probe_has_closed_logical_definition B \<longleftrightarrow>
    (\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> pp_t_family_probe B = pp_t_closed_den S)"

lemma pp_t_family_stock_implies_same_value_on_relative_views:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)"
  shows "pp_t_family_same_value_on_relative_views B w p"
  unfolding pp_t_family_same_value_on_relative_views_def
  using
    pp_t_logical_family_stock_forces_same_value_on_relative_views[
      OF B_typed B_logical p stock]
  by blast

lemma pp_t_family_view_complete_implies_stock:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and complete: "pp_t_family_view_complete B"
    and p: "Elem p (pp_t_domain Prop)"
    and same_value:
      "pp_t_family_same_value_on_relative_views B w p"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_closed_den B \<acute> p)"
proof -
  let ?v = "pp_t_cone_view w p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have v_same:
      "pp_t_family_same_value_on_relative_views B [] ?v"
    using same_value
    unfolding pp_t_family_same_value_on_relative_views_def
    using pp_t_cone_view_empty[OF v]
    by simp
  have root_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> ?v)"
    using complete v v_same
    unfolding pp_t_family_view_complete_def
    by blast
  have cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_logical_family_at_cone_related[
      OF B_typed B_logical p] .
  have stock_iff:
      "pp_t_closed_logical_stock
          pp_t_one_context_unary_type (w @ [])
          (pp_t_closed_den B \<acute> p)
        \<longleftrightarrow>
       pp_t_closed_logical_stock
          pp_t_one_context_unary_type []
          (pp_t_closed_den B \<acute> ?v)"
    using pp_t_closed_logical_stock_cone_iff[
      OF pp_t_logical_family_at_in_domain[OF B_typed p]
        pp_t_logical_family_at_in_domain[OF B_typed v] cone,
      of "[]"] .
  show ?thesis
    using stock_iff root_stock by simp
qed

theorem pp_t_family_stock_iff_same_value_on_relative_views:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and complete: "pp_t_family_view_complete B"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)
    \<longleftrightarrow>
    pp_t_family_same_value_on_relative_views B w p"
proof
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)"
  show "pp_t_family_same_value_on_relative_views B w p"
    using pp_t_family_stock_implies_same_value_on_relative_views[
      OF B_typed B_logical p stock] .
next
  assume same_value:
      "pp_t_family_same_value_on_relative_views B w p"
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)"
    using pp_t_family_view_complete_implies_stock[
      OF B_typed B_logical complete p same_value] .
qed

theorem pp_t_family_view_complete_iff_global_sufficiency:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
  shows "pp_t_family_view_complete B
    \<longleftrightarrow>
    (\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_family_same_value_on_relative_views B w p
      \<longrightarrow>
      pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p))"
proof
  assume complete: "pp_t_family_view_complete B"
  show "\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_family_same_value_on_relative_views B w p
      \<longrightarrow>
      pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)"
    using pp_t_family_view_complete_implies_stock[
      OF B_typed B_logical complete]
    by blast
next
  assume global:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_family_same_value_on_relative_views B w p
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den B \<acute> p)"
  show "pp_t_family_view_complete B"
    unfolding pp_t_family_view_complete_def
  proof (intro allI impI)
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
      and same_value:
        "pp_t_family_same_value_on_relative_views B [] p"
    show "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p)"
      using global p same_value by blast
  qed
qed

theorem
  pp_t_family_probe_eliminable_iff_view_condition_definable:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and complete: "pp_t_family_view_complete B"
  shows "pp_t_family_probe_has_closed_logical_definition B
    \<longleftrightarrow>
    pp_t_family_view_condition_definable B"
proof
  assume eliminable:
      "pp_t_family_probe_has_closed_logical_definition B"
  then obtain S where
      S_typed: "[] \<turnstile> S : pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and probe_S: "pp_t_family_probe B = pp_t_closed_den S"
    unfolding pp_t_family_probe_has_closed_logical_definition_def
    by blast
  show "pp_t_family_view_condition_definable B"
    unfolding pp_t_family_view_condition_definable_def
  proof (rule exI[where x=S], intro conjI allI impI)
    show "[] \<turnstile> S : pp_t_one_context_unary_type"
      by (rule S_typed)
    show "pp_logical_vocabulary S"
      by (rule S_logical)
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
    have probe_stock:
        "pp_t_holds (pp_t_family_probe B \<acute> p) w
          \<longleftrightarrow>
         pp_t_closed_logical_stock
           pp_t_one_context_unary_type w
           (pp_t_closed_den B \<acute> p)"
      using pp_t_family_probe_apply_holds[OF B_typed p, of w] .
    have stock_same:
        "pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den B \<acute> p)
          \<longleftrightarrow>
         pp_t_family_same_value_on_relative_views B w p"
      using pp_t_family_stock_iff_same_value_on_relative_views[
        OF B_typed B_logical complete p] .
    show "pp_t_holds (pp_t_closed_den S \<acute> p) w
        \<longleftrightarrow>
        pp_t_family_same_value_on_relative_views B w p"
      using probe_stock stock_same unfolding probe_S by blast
  qed
next
  assume definable:
      "pp_t_family_view_condition_definable B"
  then obtain S where
      S_typed: "[] \<turnstile> S : pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and S_defines:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_holds (pp_t_closed_den S \<acute> p) w
          \<longleftrightarrow>
         pp_t_family_same_value_on_relative_views B w p)"
    unfolding pp_t_family_view_condition_definable_def
    by blast
  have criterion:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den B \<acute> p)
          \<longleftrightarrow>
         pp_t_holds (pp_t_closed_den S \<acute> p) w)"
  proof -
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den B \<acute> p)
        \<longleftrightarrow>
        pp_t_holds (pp_t_closed_den S \<acute> p) w"
      using pp_t_family_stock_iff_same_value_on_relative_views[
        OF B_typed B_logical complete p, of w]
        S_defines[OF p, of w]
      by blast
  qed
  have probe_S:
      "pp_t_family_probe B = pp_t_closed_den S"
    using pp_t_family_probe_elimination_criterion[
      OF B_typed S_typed criterion] .
  show "pp_t_family_probe_has_closed_logical_definition B"
    unfolding pp_t_family_probe_has_closed_logical_definition_def
    using S_typed S_logical probe_S by blast
qed

corollary pp_t_injective_logical_family_view_complete:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and injective: "pp_t_family_is_injective B"
  shows "pp_t_family_view_complete B"
  unfolding pp_t_family_view_complete_def
proof (intro allI impI)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
    and same_value:
      "pp_t_family_same_value_on_relative_views B [] p"
  have empty: "pp_t_cone_view [] p = p"
    using pp_t_cone_view_empty[OF p] .
  have views: "\<And>s. pp_t_cone_view s p = p"
  proof -
    fix s
    have family_eq:
        "pp_t_closed_den B \<acute> pp_t_cone_view s p =
          pp_t_closed_den B \<acute> p"
      using same_value
      unfolding pp_t_family_same_value_on_relative_views_def
        empty
      by blast
    show "pp_t_cone_view s p = p"
      using injective pp_t_cone_view_in_domain p family_eq
      unfolding pp_t_family_is_injective_def
      by blast
  qed
  have invariant: "\<And>s. pp_t_cone_rel Prop s p p"
  proof -
    fix s
    show "pp_t_cone_rel Prop s p p"
      unfolding pp_t_cone_rel.simps
    proof
      fix u
      have at_view:
          "pp_t_holds (pp_t_cone_view s p) u
            \<longleftrightarrow> pp_t_holds p (s @ u)"
        by simp
      have at_p:
          "pp_t_holds (pp_t_cone_view s p) u
            \<longleftrightarrow> pp_t_holds p u"
        using views[of s] by simp
      show "pp_t_holds p (s @ u) = pp_t_holds p u"
        using at_view at_p by blast
    qed
  qed
  have p_extreme:
      "p = pp_zf_truth (pp_t_holds p [])"
    using pp_t_cone_invariant_prop_collapse[OF p invariant] .
  have p_stock: "pp_t_closed_logical_stock Prop [] p"
    using pp_t_closed_logical_prop_stock_iff_settled[OF p, of "[]"]
      p_extreme
    by (cases "pp_t_holds p []") simp_all
  have B_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) []
        (pp_t_closed_den B)"
    using B_typed B_logical
    by (rule pp_t_closed_logical_stockI)
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type []
      (pp_t_closed_den B \<acute> p)"
    using pp_t_closed_logical_stock_application_closed[
      OF B_stock p_stock] .
qed

corollary pp_t_injective_logical_family_view_condition_definable:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and injective: "pp_t_family_is_injective B"
  shows "pp_t_family_view_condition_definable B"
proof -
  have complete: "pp_t_family_view_complete B"
    using pp_t_injective_logical_family_view_complete[
      OF B_typed B_logical injective] .
  have eliminable:
      "pp_t_family_probe_has_closed_logical_definition B"
    unfolding pp_t_family_probe_has_closed_logical_definition_def
    using pp_t_settled_now_operator_typed
      pp_t_settled_now_operator_logical
      pp_t_injective_family_probe_eliminates_classifier[
        OF B_typed B_logical injective]
    by blast
  show ?thesis
    using
      pp_t_family_probe_eliminable_iff_view_condition_definable[
        OF B_typed B_logical complete]
      eliminable by blast
qed

corollary pp_t_closed_range_family_view_complete:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and closed_range:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den B \<acute> p)"
  shows "pp_t_family_view_complete B"
  unfolding pp_t_family_view_complete_def
  using closed_range by blast

text \<open>
  Thus the equation on cone views has exactly the desired force under two
  independent conditions.  View-completeness says that a value of the
  family which descends unchanged through every cone already has a closed
  logical representative.  Definability says that the corresponding
  proposition condition is expressed by one closed logical operator,
  uniformly in the current world.  The first condition is exactly
  sufficiency for stock membership; given it, the second condition is
  exactly elimination of the one-classifier family probe.
\<close>

end
