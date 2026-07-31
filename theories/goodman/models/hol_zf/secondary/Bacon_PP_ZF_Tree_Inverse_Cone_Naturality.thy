theory Bacon_PP_ZF_Tree_Inverse_Cone_Naturality
  imports Bacon_PP_ZF_Tree_One_Classifier_Contexts
begin

section \<open>Logical families whose cone behavior determines their parameter\<close>

text \<open>
  The singleton-family calculation uses only one special property of the
  family: if an instance of the family is unchanged by passage to a cone,
  then its proposition parameter is unchanged by passage to that cone.  We
  isolate that condition here.  It applies to any closed logical family of
  unary operators, not merely to the displayed singleton family.
\<close>

definition pp_t_family_determines_parameter_on_cones ::
    "oterm \<Rightarrow> bool"
where
  "pp_t_family_determines_parameter_on_cones B \<longleftrightarrow>
    (\<forall>p s.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)
      \<longrightarrow>
      pp_t_cone_view s p = p)"

definition pp_t_family_is_injective :: "oterm \<Rightarrow> bool" where
  "pp_t_family_is_injective B \<longleftrightarrow>
    (\<forall>p q.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      Elem q (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_closed_den B \<acute> p = pp_t_closed_den B \<acute> q
      \<longrightarrow>
      p = q)"

lemma pp_t_logical_family_at_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_closed_den B \<acute> p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[OF B_typed] p] .

lemma pp_t_logical_family_at_cone_related:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_cone_rel pp_t_one_context_unary_type s
    (pp_t_closed_den B \<acute> p)
    (pp_t_closed_den B \<acute> pp_t_cone_view s p)"
proof -
  have B_cone:
      "pp_t_cone_rel
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) s
        (pp_t_closed_den B) (pp_t_closed_den B)"
    using
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF B_typed B_logical] .
  have p_view:
      "pp_t_cone_rel Prop s p (pp_t_cone_view s p)"
    by simp
  show ?thesis
    using B_cone p pp_t_cone_view_in_domain p_view by simp
qed

lemma pp_t_logical_family_cone_natural_forces_same_value:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and p: "Elem p (pp_t_domain Prop)"
    and self:
      "pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)"
  shows "pp_t_closed_den B \<acute> pp_t_cone_view s p =
    pp_t_closed_den B \<acute> p"
proof -
  let ?v = "pp_t_cone_view s p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have family_p:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_logical_family_at_in_domain[OF B_typed p] .
  have family_v:
      "Elem (pp_t_closed_den B \<acute> ?v)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_logical_family_at_in_domain[OF B_typed v] .
  have shifted:
      "pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_logical_family_at_cone_related[
      OF B_typed B_logical p] .
  have left_reflexive:
      "pp_t_eqv pp_t_one_context_unary_type (s @ [])
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)"
    using pp_t_eqv_reflexive[OF family_p] .
  have right_eqv:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> ?v)
        (pp_t_closed_den B \<acute> p)"
    using pp_t_cone_compatible_all[
      of pp_t_one_context_unary_type s]
      family_p family_v family_p family_p shifted self
      left_reflexive
    unfolding pp_t_cone_compatible_def
    by blast
  have family_eq:
      "pp_t_closed_den B \<acute> ?v =
        pp_t_closed_den B \<acute> p"
    using pp_t_root_eqv_imp_eq[
      OF family_v family_p right_eqv] .
  show ?thesis by (rule family_eq)
qed

theorem pp_t_logical_family_root_stock_forces_same_value_on_all_views:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p)"
  shows "\<And>s.
    pp_t_closed_den B \<acute> pp_t_cone_view s p =
      pp_t_closed_den B \<acute> p"
proof -
  obtain M where M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and family_M:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p) (pp_t_closed_den M)"
    using stock unfolding pp_t_closed_logical_stock_def by blast
  have family:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_logical_family_at_in_domain[OF B_typed p] .
  have M:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have family_eq:
      "pp_t_closed_den B \<acute> p = pp_t_closed_den M"
    using pp_t_root_eqv_imp_eq[OF family M family_M] .
  have self:
      "\<And>s. pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)"
    unfolding family_eq
    using
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF M_typed M_logical] .
  fix s
  show "pp_t_closed_den B \<acute> pp_t_cone_view s p =
      pp_t_closed_den B \<acute> p"
    using pp_t_logical_family_cone_natural_forces_same_value[
      OF B_typed B_logical p self] .
qed

theorem pp_t_logical_family_stock_forces_same_value_on_relative_views:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)"
  shows "\<And>s.
    pp_t_closed_den B \<acute>
        pp_t_cone_view s (pp_t_cone_view w p) =
      pp_t_closed_den B \<acute> pp_t_cone_view w p"
proof -
  let ?v = "pp_t_cone_view w p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_logical_family_at_cone_related[
      OF B_typed B_logical p] .
  have root_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_closed_logical_stock_cone_iff[
      OF pp_t_logical_family_at_in_domain[OF B_typed p]
        pp_t_logical_family_at_in_domain[OF B_typed v] cone,
      of "[]"] stock
    by simp
  fix s
  show "pp_t_closed_den B \<acute> pp_t_cone_view s ?v =
      pp_t_closed_den B \<acute> ?v"
    using
      pp_t_logical_family_root_stock_forces_same_value_on_all_views[
        OF B_typed B_logical v root_stock, of s] .
qed

theorem pp_t_injective_logical_family_determines_parameter_on_cones:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and injective: "pp_t_family_is_injective B"
  shows "pp_t_family_determines_parameter_on_cones B"
  unfolding pp_t_family_determines_parameter_on_cones_def
proof (intro allI impI)
  fix p s
  assume p: "Elem p (pp_t_domain Prop)"
    and self:
      "pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)"
  have same_value:
      "pp_t_closed_den B \<acute> pp_t_cone_view s p =
        pp_t_closed_den B \<acute> p"
    using pp_t_logical_family_cone_natural_forces_same_value[
      OF B_typed B_logical p self] .
  show "pp_t_cone_view s p = p"
    using injective pp_t_cone_view_in_domain p same_value
    unfolding pp_t_family_is_injective_def
    by blast
qed

lemma pp_t_closed_logical_prop_stock_iff_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock Prop w p
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof
  assume p_stock: "pp_t_closed_logical_stock Prop w p"
  then obtain M where
      M_typed: "[] \<turnstile> M : Prop"
    and M_logical: "pp_logical_vocabulary M"
    and pM: "pp_t_eqv Prop w p (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have M_root:
      "pp_t_eqv Prop []
        (pp_t_closed_den M)
        (pp_zf_truth (pp_t_holds (pp_t_closed_den M) []))"
    using pp_t_closed_logical_prop_den_root_truth[
      OF M_typed M_logical] .
  have M_world:
      "pp_t_eqv Prop w
        (pp_t_closed_den M)
        (pp_zf_truth (pp_t_holds (pp_t_closed_den M) []))"
    using pp_t_eqv_persistent[OF M_root, of w] by simp
  have p_truth:
      "pp_t_eqv Prop w p
        (pp_zf_truth (pp_t_holds (pp_t_closed_den M) []))"
    using pp_t_eqv_transitive[
      OF p pp_t_closed_den_in_domain[OF M_typed]
        pp_t_truth_in_domain pM M_world] .
  show "pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
    using p_truth
    by (cases "pp_t_holds (pp_t_closed_den M) []") simp_all
next
  assume settled:
      "pp_t_eqv Prop w p (pp_zf_truth True)
        \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
  show "pp_t_closed_logical_stock Prop w p"
    using p settled
  proof (elim disjE)
    assume p_true:
        "pp_t_eqv Prop w p (pp_zf_truth True)"
    show ?thesis
      unfolding pp_t_closed_logical_stock_def
    proof (intro conjI)
      show "Elem p (pp_t_domain Prop)" by (rule p)
      show "\<exists>M.
          [] \<turnstile> M : Prop
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
      show "\<exists>M.
          [] \<turnstile> M : Prop
          \<and> pp_logical_vocabulary M
          \<and> pp_t_eqv Prop w p (pp_t_closed_den M)"
        using p_false
        by (intro exI[of _ ObjFalse] conjI typed_ObjFalse)
          (simp_all add: pp_logical_vocabulary_def ObjFalse_def
            ObjTrue_def pp_t_closed_den_def pp_t_eval_ObjTrue)
    qed
  qed
qed

lemma pp_t_parameter_determining_family_root_stock_imp_settled:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
    and p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p)"
  shows "p = pp_zf_truth (pp_t_holds p [])"
proof -
  obtain M where M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and family_M:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> p) (pp_t_closed_den M)"
    using stock unfolding pp_t_closed_logical_stock_def by blast
  have family:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_logical_family_at_in_domain[OF B_typed p] .
  have M:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have family_eq:
      "pp_t_closed_den B \<acute> p = pp_t_closed_den M"
    using pp_t_root_eqv_imp_eq[OF family M family_M] .
  have family_natural:
      "\<And>s. pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> p)"
    unfolding family_eq
    using
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF M_typed M_logical] .
  have views: "\<And>s. pp_t_cone_view s p = p"
    using determines p family_natural
    unfolding pp_t_family_determines_parameter_on_cones_def
    by blast
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
  show ?thesis
    using pp_t_cone_invariant_prop_collapse[OF p invariant] .
qed

theorem pp_t_parameter_determining_family_in_stock_iff_settled:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)"
  let ?v = "pp_t_cone_view w p"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w
        (pp_t_closed_den B \<acute> p)
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_logical_family_at_cone_related[
      OF B_typed B_logical p] .
  have root_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_closed_den B \<acute> ?v)"
    using pp_t_closed_logical_stock_cone_iff[
      OF pp_t_logical_family_at_in_domain[OF B_typed p]
        pp_t_logical_family_at_in_domain[OF B_typed v] cone,
      of "[]"] stock
    by simp
  have v_extreme:
      "?v = pp_zf_truth (pp_t_holds ?v [])"
    using pp_t_parameter_determining_family_root_stock_imp_settled[
      OF B_typed B_logical determines v root_stock] .
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
  have p_stock: "pp_t_closed_logical_stock Prop w p"
    using pp_t_closed_logical_prop_stock_iff_settled[OF p]
      settled by blast
  have B_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) w
        (pp_t_closed_den B)"
    using B_typed B_logical
    by (rule pp_t_closed_logical_stockI)
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)"
    using pp_t_closed_logical_stock_application_closed[
      OF B_stock p_stock] .
qed

theorem pp_t_parameter_determining_family_probe_eliminates_classifier:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
  shows "pp_t_family_probe B =
    pp_t_closed_den pp_t_settled_now_operator"
  using pp_t_family_probe_elimination_criterion[
    OF B_typed pp_t_settled_now_operator_typed]
    pp_t_parameter_determining_family_in_stock_iff_settled[
      OF B_typed B_logical determines]
    pp_t_settled_now_apply_holds
  by blast

corollary pp_t_injective_family_probe_eliminates_classifier:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and injective: "pp_t_family_is_injective B"
  shows "pp_t_family_probe B =
    pp_t_closed_den pp_t_settled_now_operator"
  using
    pp_t_parameter_determining_family_probe_eliminates_classifier[
      OF B_typed B_logical
        pp_t_injective_logical_family_determines_parameter_on_cones[
          OF B_typed B_logical injective]] .

definition pp_t_constant_truth_unary :: oterm where
  "pp_t_constant_truth_unary = pp_constant_operator ObjTrue"

lemma pp_t_constant_truth_unary_typed:
  "[] \<turnstile> pp_t_constant_truth_unary :
    pp_t_one_context_unary_type"
  unfolding pp_t_constant_truth_unary_def
  using typed_pp_constant_operator[
    OF typed_ObjTrue, where \<Gamma>="[]"]
  unfolding pp_unary_ty_def .

lemma pp_t_constant_truth_unary_logical:
  "pp_logical_vocabulary pp_t_constant_truth_unary"
  by (simp add: pp_t_constant_truth_unary_def
      pp_constant_operator_def pp_constant_builder_def
      pp_logical_vocabulary_def ObjTrue_def)

lemma pp_t_constant_truth_unary_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
    (pp_t_closed_den pp_t_constant_truth_unary \<acute> p) w"
  unfolding pp_t_constant_truth_unary_def
    pp_constant_operator_def pp_constant_builder_def
    pp_t_closed_den_def
  using pp_t_truth_in_domain p
  by (simp add: Lambda_app pp_t_eval_ObjTrue)

theorem pp_t_closed_range_family_probe_eliminates_classifier:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and closed_range:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den B \<acute> p)"
  shows "pp_t_family_probe B =
    pp_t_closed_den pp_t_constant_truth_unary"
  using pp_t_family_probe_elimination_criterion[
    OF B_typed pp_t_constant_truth_unary_typed]
    closed_range pp_t_constant_truth_unary_apply_holds
  by blast

corollary pp_t_constant_family_probe_eliminates_classifier:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and constant_family:
      "\<And>p q.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        Elem q (pp_t_domain Prop) \<Longrightarrow>
        pp_t_closed_den B \<acute> p =
          pp_t_closed_den B \<acute> q"
  shows "pp_t_family_probe B =
    pp_t_closed_den pp_t_constant_truth_unary"
proof (rule pp_t_closed_range_family_probe_eliminates_classifier[
    OF B_typed])
  fix p w
  assume p: "Elem p (pp_t_domain Prop)"
  have truth: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  let ?M = "App B ObjTrue"
  have M_typed:
      "[] \<turnstile> ?M : pp_t_one_context_unary_type"
    using B_typed typed_ObjTrue by (rule has_type.App)
  have M_logical: "pp_logical_vocabulary ?M"
    using B_logical
    by (simp add: pp_logical_vocabulary_def ObjTrue_def)
  have M_den:
      "pp_t_closed_den ?M =
        pp_t_closed_den B \<acute> pp_zf_truth True"
    by (simp add: pp_t_closed_den_def pp_t_eval_ObjTrue)
  have p_eq:
      "pp_t_closed_den B \<acute> p = pp_t_closed_den ?M"
    unfolding M_den
    using constant_family[OF p truth] .
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)"
    unfolding p_eq
    using M_typed M_logical
    by (rule pp_t_closed_logical_stockI)
qed

corollary pp_t_closed_range_family_probe_in_closed_logical_stock:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and closed_range:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den B \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w (pp_t_family_probe B)"
proof -
  have probe:
      "pp_t_family_probe B =
        pp_t_closed_den pp_t_constant_truth_unary"
    using pp_t_closed_range_family_probe_eliminates_classifier[
      OF B_typed closed_range] .
  show ?thesis
    unfolding probe
    using pp_t_constant_truth_unary_typed
      pp_t_constant_truth_unary_logical
    by (rule pp_t_closed_logical_stockI)
qed

corollary
  pp_t_parameter_determining_family_probe_in_closed_logical_stock:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w (pp_t_family_probe B)"
  unfolding
    pp_t_parameter_determining_family_probe_eliminates_classifier[
      OF B_typed B_logical determines]
  using pp_t_settled_now_operator_typed
    pp_t_settled_now_operator_logical
  by (rule pp_t_closed_logical_stockI)

theorem pp_t_parameter_determining_family_postprocessing_eliminates:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
    and H_typed:
      "[] \<turnstile> H :
        pp_t_one_context_unary_type \<rightarrow>\<^sub>o \<sigma>"
  shows "pp_t_closed_den H \<acute> pp_t_family_probe B =
    pp_t_closed_den (App H pp_t_settled_now_operator)"
proof -
  have probe:
      "pp_t_family_probe B =
        pp_t_closed_den pp_t_settled_now_operator"
    using
      pp_t_parameter_determining_family_probe_eliminates_classifier[
        OF B_typed B_logical determines] .
  show ?thesis
    unfolding probe pp_t_closed_den_def
    using pp_t_closed_den_in_domain[
      OF pp_t_settled_now_operator_typed]
    by simp
qed

corollary
  pp_t_parameter_determining_family_postprocessing_in_closed_stock:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and B_logical: "pp_logical_vocabulary B"
    and determines:
      "pp_t_family_determines_parameter_on_cones B"
    and H_typed:
      "[] \<turnstile> H :
        pp_t_one_context_unary_type \<rightarrow>\<^sub>o \<sigma>"
    and H_logical: "pp_logical_vocabulary H"
  shows "pp_t_closed_logical_stock \<sigma> w
    (pp_t_closed_den H \<acute> pp_t_family_probe B)"
proof -
  have app_typed:
      "[] \<turnstile> App H pp_t_settled_now_operator : \<sigma>"
    using H_typed pp_t_settled_now_operator_typed
    by (rule has_type.App)
  have app_logical:
      "pp_logical_vocabulary
        (App H pp_t_settled_now_operator)"
    using H_logical pp_t_settled_now_operator_logical
    by (simp add: pp_logical_vocabulary_def)
  show ?thesis
    unfolding
      pp_t_parameter_determining_family_postprocessing_eliminates[
        OF B_typed B_logical determines H_typed]
    using app_typed app_logical
    by (rule pp_t_closed_logical_stockI)
qed

text \<open>
  These results exhaust the inverse argument itself.  They eliminate every
  family test whose family determines its proposition parameter on cones;
  injectivity is a simple sufficient condition.  They also eliminate the
  opposite degenerate case in which every value of the family is already a
  closed logical operator, including every constant family.  Arbitrary
  closed logical postprocessing adds no new case.

  This is not an exhaustive classification of all one-occurrence contexts.
  A nonconstant, noninjective family may identify several propositions in
  one fibre.  Cone-naturality then says only that every cone view of the
  parameter remains in that fibre.  Eliminating its classifier test requires
  a closed logical definition of that fibre condition.  Contexts in which
  the classifier occurs inside the scope of a higher-order quantifier require
  the corresponding uniform definition.  Those fibre and quantified cases,
  rather than the injective cases, are the remaining one-occurrence
  problem.
\<close>

end
