theory Bacon_PP_ZF_Tree_Singleton_Family_Elimination
  imports Bacon_PP_ZF_Tree_Indexed_Family_Probe
begin

section \<open>Eliminating the singleton-family occurrence of the classifier\<close>

text \<open>
  The first unresolved one-classifier context asks whether the operator
  \<open>\<lambda>q. \<box>(q \<longleftrightarrow> p)\<close> belongs to the closed logical unary stock.
  The answer is exact: it does just when \<open>p\<close> is settled on the current cone.
  Hence the resulting test is the already logical non-contingency operator.
\<close>

abbreviation pp_t_singleton_family_at :: "ZF \<Rightarrow> ZF" where
  "pp_t_singleton_family_at p \<equiv>
    pp_t_closed_den pp_t_singleton_family_builder \<acute> p"

lemma pp_t_singleton_family_at_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_singleton_family_at p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_singleton_family_builder_typed] p] .

lemma pp_t_singleton_family_at_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds ((pp_t_singleton_family_at p) \<acute> q) w
    \<longleftrightarrow> pp_t_eqv Prop w q p"
proof -
  have beta:
      "(pp_t_singleton_family_at p) \<acute> q =
        pp_t_eval pp_t_default_constants
          (extend_env q (extend_env p pp_t_closed_env))
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))"
    unfolding pp_t_closed_den_def pp_t_singleton_family_builder_def
    using p q by (simp add: Lambda_app)
  show ?thesis
    unfolding beta
    by (simp add: pp_t_eval_ObjBox_holds
        pp_t_prop_eqv_truth_iff prefix_def; blast)
qed

lemma pp_t_singleton_family_at_cone_related:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_cone_rel pp_t_one_context_unary_type s
    (pp_t_singleton_family_at p)
    (pp_t_singleton_family_at (pp_t_cone_view s p))"
proof -
  have builder_cone:
      "pp_t_cone_rel
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) s
        (pp_t_closed_den pp_t_singleton_family_builder)
        (pp_t_closed_den pp_t_singleton_family_builder)"
    using
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_singleton_family_builder_typed
          pp_t_singleton_family_builder_logical] .
  have p_view:
      "pp_t_cone_rel Prop s p (pp_t_cone_view s p)"
    by simp
  show ?thesis
    using builder_cone p pp_t_cone_view_in_domain p_view by simp
qed

theorem pp_t_singleton_family_is_injective:
  "pp_t_family_is_injective pp_t_singleton_family_builder"
  unfolding pp_t_family_is_injective_def
proof (intro allI impI)
  fix p q
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and family_eq:
      "pp_t_singleton_family_at p =
        pp_t_singleton_family_at q"
  have p_true:
      "pp_t_holds ((pp_t_singleton_family_at p) \<acute> p) []"
    using pp_t_singleton_family_at_apply_holds[OF p p]
      pp_t_eqv_reflexive[OF p] by simp
  have q_at_p:
      "pp_t_holds ((pp_t_singleton_family_at q) \<acute> p) []"
    using p_true unfolding family_eq .
  have pq: "pp_t_eqv Prop [] p q"
    using pp_t_singleton_family_at_apply_holds[OF q p, of "[]"]
      q_at_p by blast
  show "p = q"
    using pp_t_root_eqv_imp_eq[OF p q pq] .
qed

lemma pp_t_singleton_family_cone_natural_forces_view:
  assumes p: "Elem p (pp_t_domain Prop)"
    and natural:
      "pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at p)"
  shows "pp_t_cone_view s p = p"
proof -
  let ?v = "pp_t_cone_view s p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have p_v: "pp_t_cone_rel Prop s p ?v"
    by simp
  have outputs:
      "pp_t_cone_rel Prop s
        ((pp_t_singleton_family_at p) \<acute> p)
        ((pp_t_singleton_family_at p) \<acute> ?v)"
    using natural p v p_v by simp
  have left_true:
      "\<And>u. pp_t_holds
        ((pp_t_singleton_family_at p) \<acute> p) (s @ u)"
    using pp_t_singleton_family_at_apply_holds[OF p p]
      pp_t_eqv_reflexive[OF p] by simp
  have right_true:
      "pp_t_holds ((pp_t_singleton_family_at p) \<acute> ?v) []"
    using outputs left_true by simp
  have v_p: "pp_t_eqv Prop [] ?v p"
    using pp_t_singleton_family_at_apply_holds[OF p v, of "[]"]
      right_true by blast
  show "?v = p"
    using pp_t_root_eqv_imp_eq[OF v p v_p] .
qed

theorem pp_t_singleton_family_determines_parameter_on_cones:
  "pp_t_family_determines_parameter_on_cones
    pp_t_singleton_family_builder"
  using pp_t_injective_logical_family_determines_parameter_on_cones[
    OF pp_t_singleton_family_builder_typed
      pp_t_singleton_family_builder_logical
      pp_t_singleton_family_is_injective] .

lemma pp_t_singleton_family_root_stock_imp_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_singleton_family_at p)"
  shows "p = pp_zf_truth (pp_t_holds p [])"
proof -
  obtain M where M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and family_M:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_singleton_family_at p) (pp_t_closed_den M)"
    using stock unfolding pp_t_closed_logical_stock_def by blast
  have family:
      "Elem (pp_t_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_singleton_family_at_in_domain[OF p] .
  have M:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have family_eq:
      "pp_t_singleton_family_at p = pp_t_closed_den M"
    using pp_t_root_eqv_imp_eq[OF family M family_M] .
  have family_natural:
      "\<And>s. pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at p)"
    unfolding family_eq
    using
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF M_typed M_logical] .
  have invariant: "\<And>s. pp_t_cone_rel Prop s p p"
  proof -
    fix s
    have view: "pp_t_cone_view s p = p"
      using p family_natural[of s]
      by (rule pp_t_singleton_family_cone_natural_forces_view)
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
        using view by simp
      show "pp_t_holds p (s @ u) = pp_t_holds p u"
        using at_view at_p by blast
    qed
  qed
  show ?thesis
    using pp_t_cone_invariant_prop_collapse[OF p invariant] .
qed

lemma pp_t_singleton_family_in_stock_if_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth True)
        \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_singleton_family_at p)"
proof -
  have p_stock: "pp_t_closed_logical_stock Prop w p"
    using p settled
  proof (elim disjE)
    assume p_true:
        "pp_t_eqv Prop w p (pp_zf_truth True)"
    show ?thesis
      unfolding pp_t_closed_logical_stock_def
    proof (intro conjI)
      show "Elem p (pp_t_domain Prop)" by (rule p)
      show "\<exists>M. [] \<turnstile> M : Prop
          \<and> pp_logical_vocabulary M
          \<and> pp_t_eqv Prop w p (pp_t_closed_den M)"
        using p_true
        by (intro exI[of _ ObjTrue] conjI typed_ObjTrue)
          (simp_all add: pp_logical_vocabulary_def ObjTrue_def
            pp_t_closed_den_def pp_t_eval_ObjTrue)
    qed
  next
    assume p_false:
        "pp_t_eqv Prop w p (pp_zf_truth False)"
    show ?thesis
      unfolding pp_t_closed_logical_stock_def
    proof (intro conjI)
      show "Elem p (pp_t_domain Prop)" by (rule p)
      show "\<exists>M. [] \<turnstile> M : Prop
          \<and> pp_logical_vocabulary M
          \<and> pp_t_eqv Prop w p (pp_t_closed_den M)"
        using p_false
        by (intro exI[of _ ObjFalse] conjI typed_ObjFalse)
          (simp_all add: pp_logical_vocabulary_def ObjFalse_def
            ObjTrue_def pp_t_closed_den_def pp_t_eval_ObjTrue)
    qed
  qed
  have builder_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) w
        (pp_t_closed_den pp_t_singleton_family_builder)"
    using pp_t_singleton_family_builder_typed
      pp_t_singleton_family_builder_logical
    by (rule pp_t_closed_logical_stockI)
  show ?thesis
    using pp_t_closed_logical_stock_application_closed[
      OF builder_stock p_stock] .
qed

theorem pp_t_singleton_family_in_closed_stock_iff_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_singleton_family_at p)
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)"
  let ?v = "pp_t_cone_view w p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at ?v)"
    using pp_t_singleton_family_at_cone_related[OF p] .
  have root_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_singleton_family_at ?v)"
    using pp_t_closed_logical_stock_cone_iff[
      OF pp_t_singleton_family_at_in_domain[OF p]
        pp_t_singleton_family_at_in_domain[OF v] cone,
      of "[]"] stock
    by simp
  have v_extreme:
      "?v = pp_zf_truth (pp_t_holds ?v [])"
    using pp_t_singleton_family_root_stock_imp_settled[
      OF v root_stock] .
  show "pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
  proof (cases "pp_t_holds ?v []")
    case True
    then have v_true: "?v = pp_zf_truth True"
      using v_extreme by simp
    have "pp_t_eqv Prop w p (pp_zf_truth True)"
    proof (simp only: pp_t_eqv.simps, intro allI impI)
      fix z
      assume "prefix w z"
      then obtain u where z: "z = w @ u"
        unfolding prefix_def by blast
      have "pp_t_holds ?v u"
        using v_true by simp
      then show "pp_t_holds p z =
          pp_t_holds (pp_zf_truth True) z"
        unfolding z by simp
    qed
    then show ?thesis by blast
  next
    case False
    then have v_false: "?v = pp_zf_truth False"
      using v_extreme by simp
    have "pp_t_eqv Prop w p (pp_zf_truth False)"
    proof (simp only: pp_t_eqv.simps, intro allI impI)
      fix z
      assume "prefix w z"
      then obtain u where z: "z = w @ u"
        unfolding prefix_def by blast
      have "\<not> pp_t_holds ?v u"
        using v_false by simp
      then show "pp_t_holds p z =
          pp_t_holds (pp_zf_truth False) z"
        unfolding z by simp
    qed
    then show ?thesis by blast
  qed
next
  assume settled:
      "pp_t_eqv Prop w p (pp_zf_truth True)
        \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_singleton_family_at p)"
    using pp_t_singleton_family_in_stock_if_settled[
      OF p settled] .
qed

lemma pp_t_singleton_test_apply_eq_settled_now:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_one_step_singleton_test \<acute> p =
    pp_t_closed_den pp_t_settled_now_operator \<acute> p"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_one_step_singleton_test \<acute> p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[OF pp_t_singleton_test_in_domain p] .
  show "Elem
      (pp_t_closed_den pp_t_settled_now_operator \<acute> p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[
        OF pp_t_settled_now_operator_typed] p] .
  fix w
  show "pp_t_holds (pp_t_one_step_singleton_test \<acute> p) w
      \<longleftrightarrow>
      pp_t_holds
        (pp_t_closed_den pp_t_settled_now_operator \<acute> p) w"
    using
      pp_t_singleton_test_apply_holds_iff_family_in_stock[
        OF p, of w]
      pp_t_singleton_family_in_closed_stock_iff_settled[
        OF p, of w]
      pp_t_settled_now_apply_holds[OF p, of w]
    by blast
qed

theorem pp_t_singleton_test_eliminates_classifier:
  "pp_t_one_step_singleton_test =
    pp_t_closed_den pp_t_settled_now_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem pp_t_one_step_singleton_test
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_test_in_domain)
  show "Elem (pp_t_closed_den pp_t_settled_now_operator)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_settled_now_operator_typed] .
  fix p
  assume "Elem p (pp_t_domain Prop)"
  then show "pp_t_one_step_singleton_test \<acute> p =
      pp_t_closed_den pp_t_settled_now_operator \<acute> p"
    by (rule pp_t_singleton_test_apply_eq_settled_now)
qed

corollary pp_t_singleton_test_elimination_is_an_instance:
  "pp_t_family_probe pp_t_singleton_family_builder =
    pp_t_closed_den pp_t_settled_now_operator"
  using
    pp_t_parameter_determining_family_probe_eliminates_classifier[
      OF pp_t_singleton_family_builder_typed
        pp_t_singleton_family_builder_logical
        pp_t_singleton_family_determines_parameter_on_cones] .

corollary pp_t_singleton_test_in_closed_logical_stock:
  "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    pp_t_one_step_singleton_test"
  unfolding pp_t_singleton_test_eliminates_classifier
  using pp_t_settled_now_operator_typed
    pp_t_settled_now_operator_logical
  by (rule pp_t_closed_logical_stockI)

corollary pp_t_singleton_test_context_is_eliminable:
  "\<exists>S.
    [] \<turnstile> S : pp_t_one_context_unary_type
    \<and> pp_logical_vocabulary S
    \<and> pp_t_one_step_expr_den pp_t_singleton_test_expr =
      pp_t_closed_den S"
  using pp_t_settled_now_operator_typed
    pp_t_settled_now_operator_logical
  unfolding pp_t_singleton_test_expr_den
    pp_t_singleton_test_eliminates_classifier
  by blast

end
