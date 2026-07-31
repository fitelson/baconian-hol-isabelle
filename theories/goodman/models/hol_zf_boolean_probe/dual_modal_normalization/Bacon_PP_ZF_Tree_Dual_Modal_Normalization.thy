theory Bacon_PP_ZF_Tree_Dual_Modal_Normalization
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Depth_Two.Bacon_PP_ZF_Tree_Dual_Modal_Depth_Two
begin

section \<open>The two remaining positive S4 modal forms\<close>

definition pp_t_box_diamond_box_unary :: oterm where
  "pp_t_box_diamond_box_unary =
    pp_compose pp_t_necessity_unary pp_t_diamond_box_unary"

definition pp_t_diamond_box_diamond_unary :: oterm where
  "pp_t_diamond_box_diamond_unary =
    pp_compose pp_t_possibility_unary pp_t_box_diamond_unary"

lemma pp_t_modal_depth_three_terms_typed:
  "[] \<turnstile> pp_t_box_diamond_box_unary :
    pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_diamond_box_diamond_unary :
    pp_t_one_context_unary_type"
proof -
  have N:
      "[] \<turnstile> pp_t_necessity_unary : pp_unary_ty"
    using pp_t_modal_unary_terms_typed(1)
    unfolding pp_unary_ty_def .
  have M:
      "[] \<turnstile> pp_t_possibility_unary : pp_unary_ty"
    using pp_t_modal_unary_terms_typed(2)
    unfolding pp_unary_ty_def .
  have MN:
      "[] \<turnstile> pp_t_diamond_box_unary : pp_unary_ty"
    using pp_t_modal_depth_two_terms_typed(2)
    unfolding pp_unary_ty_def .
  have NM:
      "[] \<turnstile> pp_t_box_diamond_unary : pp_unary_ty"
    using pp_t_modal_depth_two_terms_typed(1)
    unfolding pp_unary_ty_def .
  show "[] \<turnstile> pp_t_box_diamond_box_unary :
      pp_t_one_context_unary_type"
    unfolding pp_t_box_diamond_box_unary_def
    using typed_pp_compose[OF N MN]
    unfolding pp_unary_ty_def .
  show "[] \<turnstile> pp_t_diamond_box_diamond_unary :
      pp_t_one_context_unary_type"
    unfolding pp_t_diamond_box_diamond_unary_def
    using typed_pp_compose[OF M NM]
    unfolding pp_unary_ty_def .
qed

lemma pp_t_modal_depth_three_terms_logical:
  "pp_logical_vocabulary pp_t_box_diamond_box_unary"
  "pp_logical_vocabulary pp_t_diamond_box_diamond_unary"
  unfolding pp_t_box_diamond_box_unary_def
    pp_t_diamond_box_diamond_unary_def
  using pp_t_modal_unary_terms_logical
    pp_t_modal_depth_two_terms_logical
  by (simp_all add: pp_compose_def
      pp_logical_vocabulary_def shift_def)

abbreviation pp_t_box_diamond_box_operator :: ZF where
  "pp_t_box_diamond_box_operator \<equiv>
    pp_t_closed_den pp_t_box_diamond_box_unary"

abbreviation pp_t_diamond_box_diamond_operator :: ZF where
  "pp_t_diamond_box_diamond_operator \<equiv>
    pp_t_closed_den pp_t_diamond_box_diamond_unary"

lemma pp_t_modal_depth_three_operators_in_domain:
  "Elem pp_t_box_diamond_box_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  "Elem pp_t_diamond_box_diamond_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_closed_den_in_domain,
      rule pp_t_modal_depth_three_terms_typed)+

lemma pp_t_box_diamond_box_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_box_diamond_box_operator \<acute> p
      = pp_t_necessity_operator \<acute>
          (pp_t_diamond_box_operator \<acute> p)"
  unfolding pp_t_box_diamond_box_unary_def
    pp_t_closed_den_compose
  by (rule pp_t_qd_precompose_apply[OF p])

lemma pp_t_diamond_box_diamond_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_diamond_box_diamond_operator \<acute> p
      = pp_t_possibility_operator \<acute>
          (pp_t_box_diamond_operator \<acute> p)"
  unfolding pp_t_diamond_box_diamond_unary_def
    pp_t_closed_den_compose
  by (rule pp_t_qd_precompose_apply[OF p])

lemma pp_t_box_diamond_box_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_box_diamond_box_operator \<acute> p) w
      \<longleftrightarrow>
     (\<forall>a. prefix w a \<longrightarrow>
       (\<exists>b. prefix a b
         \<and> (\<forall>c. prefix b c \<longrightarrow> pp_t_holds p c)))"
proof -
  have MNp:
      "Elem (pp_t_diamond_box_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(2) p])
  show ?thesis
    unfolding pp_t_box_diamond_box_operator_apply[OF p]
      pp_t_necessity_operator_apply_holds[OF MNp]
      pp_t_diamond_box_operator_apply_holds[OF p]
    by blast
qed

lemma pp_t_diamond_box_diamond_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_diamond_box_diamond_operator \<acute> p) w
      \<longleftrightarrow>
     (\<exists>a. prefix w a
       \<and> (\<forall>b. prefix a b \<longrightarrow>
         (\<exists>c. prefix b c \<and> pp_t_holds p c)))"
proof -
  have NMp:
      "Elem (pp_t_box_diamond_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(1) p])
  show ?thesis
    unfolding pp_t_diamond_box_diamond_operator_apply[OF p]
      pp_t_possibility_operator_apply_holds[OF NMp]
      pp_t_box_diamond_operator_apply_holds[OF p]
    by blast
qed

section \<open>The depth-three complement fixed-point obstructions\<close>

lemma pp_t_no_box_diamond_box_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_box_diamond_box_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Fq = "pp_t_box_diamond_box_operator \<acute> ?q"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  assume fixed: "pp_t_eqv Prop w p ?Fq"
  have contradiction_if_true:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds p v
        \<Longrightarrow> False"
  proof -
    fix v
    assume wv: "prefix w v"
      and p_v: "pp_t_holds p v"
    have fixed_v: "pp_t_eqv Prop v p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wv])
    have Fq_v: "pp_t_holds ?Fq v"
      using pp_t_prop_eqv_at[OF fixed_v, of v] p_v by simp
    obtain b where vb: "prefix v b"
      and all_q:
        "\<forall>c. prefix b c \<longrightarrow> pp_t_holds ?q c"
      using pp_t_box_diamond_box_operator_apply_holds[OF q, of v]
        Fq_v
      by (meson prefix_order.refl)
    have not_p_b: "\<not> pp_t_holds p b"
      using all_q[rule_format, OF prefix_order.refl] by simp
    have wb: "prefix w b"
      by (rule prefix_order.trans[OF wv vb])
    have fixed_b: "pp_t_eqv Prop b p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wb])
    have not_Fq_b: "\<not> pp_t_holds ?Fq b"
      using pp_t_prop_eqv_at[OF fixed_b, of b] not_p_b
      by simp
    have Fq_b: "pp_t_holds ?Fq b"
    proof -
      have recurrent:
          "\<forall>a. prefix b a \<longrightarrow>
            (\<exists>c. prefix a c
              \<and> (\<forall>d. prefix c d \<longrightarrow>
                pp_t_holds ?q d))"
      proof (intro allI impI)
        fix a
        assume ba: "prefix b a"
        have all_q_a:
            "\<forall>d. prefix a d \<longrightarrow> pp_t_holds ?q d"
          using all_q prefix_order.trans[OF ba] by blast
        show "\<exists>c. prefix a c
            \<and> (\<forall>d. prefix c d \<longrightarrow>
              pp_t_holds ?q d)"
          using all_q_a by (intro exI[of _ a]) simp
      qed
      show ?thesis
        using pp_t_box_diamond_box_operator_apply_holds[OF q, of b]
          recurrent
        by blast
    qed
    show False using Fq_b not_Fq_b by blast
  qed
  show False
  proof (cases "pp_t_holds p w")
    case True
    show False
      by (rule contradiction_if_true[OF prefix_order.refl True])
  next
    case False
    have not_Fq_w: "\<not> pp_t_holds ?Fq w"
      using pp_t_prop_eqv_at[OF fixed, of w] False by simp
    have failure:
        "\<not> (\<forall>a. prefix w a \<longrightarrow>
          (\<exists>b. prefix a b
            \<and> (\<forall>c. prefix b c \<longrightarrow>
              pp_t_holds ?q c)))"
      using pp_t_box_diamond_box_operator_apply_holds[OF q, of w]
        not_Fq_w
      by simp
    obtain a where wa: "prefix w a"
      and no_q_cone:
        "\<forall>b. prefix a b \<longrightarrow>
          \<not> (\<forall>c. prefix b c \<longrightarrow> pp_t_holds ?q c)"
      using failure by blast
    obtain c where ac: "prefix a c"
      and not_q_c: "\<not> pp_t_holds ?q c"
      using no_q_cone[rule_format, OF prefix_order.refl]
      by blast
    have p_c: "pp_t_holds p c"
      using not_q_c by simp
    have wc: "prefix w c"
      by (rule prefix_order.trans[OF wa ac])
    show False
      by (rule contradiction_if_true[OF wc p_c])
  qed
qed

lemma pp_t_no_diamond_box_diamond_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_diamond_box_diamond_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Fq = "pp_t_diamond_box_diamond_operator \<acute> ?q"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  assume fixed: "pp_t_eqv Prop w p ?Fq"
  have contradiction_if_true:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds p v
        \<Longrightarrow> False"
  proof -
    fix v
    assume wv: "prefix w v"
      and p_v: "pp_t_holds p v"
    have fixed_v: "pp_t_eqv Prop v p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wv])
    have Fq_v: "pp_t_holds ?Fq v"
      using pp_t_prop_eqv_at[OF fixed_v, of v] p_v by simp
    obtain a where va: "prefix v a"
      and dense_q:
        "\<forall>b. prefix a b \<longrightarrow>
          (\<exists>c. prefix b c \<and> pp_t_holds ?q c)"
      using pp_t_diamond_box_diamond_operator_apply_holds[OF q, of v]
        Fq_v
      by blast
    obtain c where ac: "prefix a c"
      and q_c: "pp_t_holds ?q c"
      using dense_q[rule_format, OF prefix_order.refl] by blast
    have not_p_c: "\<not> pp_t_holds p c"
      using q_c by simp
    have wc: "prefix w c"
      by (rule prefix_order.trans[
        OF wv prefix_order.trans[OF va ac]])
    have fixed_c: "pp_t_eqv Prop c p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wc])
    have not_Fq_c: "\<not> pp_t_holds ?Fq c"
      using pp_t_prop_eqv_at[OF fixed_c, of c] not_p_c
      by simp
    have dense_q_c:
        "\<forall>b. prefix c b \<longrightarrow>
          (\<exists>d. prefix b d \<and> pp_t_holds ?q d)"
      using dense_q prefix_order.trans[OF ac] by blast
    have Fq_c: "pp_t_holds ?Fq c"
    proof -
      have witness:
          "\<exists>a. prefix c a
            \<and> (\<forall>b. prefix a b \<longrightarrow>
              (\<exists>d. prefix b d \<and> pp_t_holds ?q d))"
        using dense_q_c by (intro exI[of _ c]) simp
      show ?thesis
        using
          pp_t_diamond_box_diamond_operator_apply_holds[OF q, of c]
          witness
        by blast
    qed
    show False using Fq_c not_Fq_c by blast
  qed
  show False
  proof (cases "pp_t_holds p w")
    case True
    show False
      by (rule contradiction_if_true[OF prefix_order.refl True])
  next
    case False
    have not_Fq_w: "\<not> pp_t_holds ?Fq w"
      using pp_t_prop_eqv_at[OF fixed, of w] False by simp
    have failure:
        "\<forall>a. prefix w a \<longrightarrow>
          \<not> (\<forall>b. prefix a b \<longrightarrow>
            (\<exists>c. prefix b c \<and> pp_t_holds ?q c))"
      using pp_t_diamond_box_diamond_operator_apply_holds[OF q, of w]
        not_Fq_w
      by blast
    obtain b where wb: "prefix w b"
      and no_q:
        "\<not> (\<exists>c. prefix b c \<and> pp_t_holds ?q c)"
      using failure[rule_format, OF prefix_order.refl]
      by blast
    have not_q_b: "\<not> pp_t_holds ?q b"
      using no_q by auto
    have p_b: "pp_t_holds p b"
      using not_q_b by simp
    show False
      by (rule contradiction_if_true[OF wb p_b])
  qed
qed

section \<open>A uniform recurrence theorem for truth-preserving operators\<close>

definition pp_t_preserves_truth_cones :: "ZF \<Rightarrow> bool" where
  "pp_t_preserves_truth_cones F
    \<longleftrightarrow>
    (\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> pp_t_holds p v)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> pp_t_holds (F \<acute> p) v))"

lemma pp_t_box_diamond_box_preserves_truth_cones:
  "pp_t_preserves_truth_cones pp_t_box_diamond_box_operator"
  unfolding pp_t_preserves_truth_cones_def
proof (intro allI impI)
  fix p w v
  assume p: "Elem p (pp_t_domain Prop)"
    and true: "\<forall>v. prefix w v \<longrightarrow> pp_t_holds p v"
    and wv: "prefix w v"
  have pattern:
      "\<forall>a. prefix v a \<longrightarrow>
        (\<exists>b. prefix a b
          \<and> (\<forall>c. prefix b c \<longrightarrow> pp_t_holds p c))"
  proof (intro allI impI)
    fix a
    assume va: "prefix v a"
    have wa: "prefix w a"
      by (rule prefix_order.trans[OF wv va])
    have future:
        "\<forall>c. prefix a c \<longrightarrow> pp_t_holds p c"
      using true prefix_order.trans[OF wa] by blast
    show "\<exists>b. prefix a b
        \<and> (\<forall>c. prefix b c \<longrightarrow> pp_t_holds p c)"
      using future by (intro exI[of _ a]) simp
  qed
  show "pp_t_holds (pp_t_box_diamond_box_operator \<acute> p) v"
    using pp_t_box_diamond_box_operator_apply_holds[OF p, of v]
      pattern
    by blast
qed

lemma pp_t_diamond_box_diamond_preserves_truth_cones:
  "pp_t_preserves_truth_cones pp_t_diamond_box_diamond_operator"
  unfolding pp_t_preserves_truth_cones_def
proof (intro allI impI)
  fix p w v
  assume p: "Elem p (pp_t_domain Prop)"
    and true: "\<forall>v. prefix w v \<longrightarrow> pp_t_holds p v"
    and wv: "prefix w v"
  have dense:
      "\<forall>b. prefix v b \<longrightarrow>
        (\<exists>c. prefix b c \<and> pp_t_holds p c)"
  proof (intro allI impI)
    fix b
    assume vb: "prefix v b"
    have wb: "prefix w b"
      by (rule prefix_order.trans[OF wv vb])
    show "\<exists>c. prefix b c \<and> pp_t_holds p c"
      using true[rule_format, OF wb]
      by (intro exI[of _ b]) simp
  qed
  have pattern:
      "\<exists>a. prefix v a
        \<and> (\<forall>b. prefix a b \<longrightarrow>
          (\<exists>c. prefix b c \<and> pp_t_holds p c))"
    using dense by (intro exI[of _ v]) simp
  show "pp_t_holds
      (pp_t_diamond_box_diamond_operator \<acute> p) v"
    using
      pp_t_diamond_box_diamond_operator_apply_holds[OF p, of v]
      pattern
    by blast
qed

lemma pp_t_dual_truth_cone_boundary_recurrence:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and preserves: "pp_t_preserves_truth_cones F"
  shows
    "pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at F w"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?R = "pp_t_probe_modal_boolean_dual_recurrent_seed_at"
  obtain t where true_cone:
      "pp_t_eqv Prop t ?r (pp_zf_truth True)"
    using pp_t_dual_recurrent_root_seed_has_true_cone by blast
  obtain f where false_cone:
      "pp_t_eqv Prop f ?r (pp_zf_truth False)"
    using pp_t_dual_recurrent_root_seed_has_false_cone by blast
  have r: "Elem ?r (pp_t_domain Prop)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec
    by blast
  let ?v = "w @ t"
  have Rw: "Elem (?R w) (pp_t_domain Prop)"
    by (rule
      pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have all_true:
      "\<forall>z. prefix ?v z \<longrightarrow> pp_t_holds (?R w) z"
  proof (intro allI impI)
    fix z
    assume future: "prefix ?v z"
    obtain u where z: "z = (w @ t) @ u"
      using future unfolding prefix_def by blast
    have r_true: "pp_t_holds ?r (t @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF true_cone, of "t @ u"],
        of "t @ u"]
      by simp
    show "pp_t_holds (?R w) z"
      using r_true
      unfolding z
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  have F_true:
      "\<forall>z. prefix ?v z \<longrightarrow>
        pp_t_holds (F \<acute> ?R w) z"
    using preserves Rw all_true
    unfolding pp_t_preserves_truth_cones_def by blast
  have target:
      "pp_t_eqv Prop ?v (F \<acute> ?R w) (pp_zf_truth True)"
    using F_true unfolding pp_t_prop_eqv_truth_iff .
  have truth_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth True)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_truth_boundary[
      OF r true_cone false_cone])
  have target_domain: "Elem (F \<acute> ?R w) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F Rw])
  have target_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (F \<acute> ?R w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain truth_boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using target_boundary
    by (intro exI[of _ ?v]) simp
qed

corollary pp_t_dual_modal_depth_three_boundary_recurrences:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_box_diamond_box_operator w"
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_diamond_box_diamond_operator w"
proof -
  show "pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_box_diamond_box_operator w"
    by (rule pp_t_dual_truth_cone_boundary_recurrence[
      OF pp_t_modal_depth_three_operators_in_domain(1)
        pp_t_box_diamond_box_preserves_truth_cones])
  show "pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_diamond_box_diamond_operator w"
    by (rule pp_t_dual_truth_cone_boundary_recurrence[
      OF pp_t_modal_depth_three_operators_in_domain(2)
        pp_t_diamond_box_diamond_preserves_truth_cones])
qed

section \<open>Guarded-cone anti-patching at depth three\<close>

lemma pp_t_dual_negation_guard_box_diamond_box_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_box_diamond_box_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_box_diamond_box_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof -
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have inner:
      "pp_t_eqv Prop v
        (pp_t_diamond_box_operator \<acute> ?Rw)
        (pp_t_diamond_box_operator \<acute> pp_t_complement ?Rv)"
    using pp_t_dual_negation_guard_diamond_box_target[of w]
    unfolding v_def .
  have left:
      "Elem (pp_t_diamond_box_operator \<acute> ?Rw)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(2) Rw])
  have right:
      "Elem (pp_t_diamond_box_operator \<acute> pp_t_complement ?Rv)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(2) cRv])
  have outer:
      "pp_t_eqv Prop v
        (pp_t_necessity_operator \<acute>
          (pp_t_diamond_box_operator \<acute> ?Rw))
        (pp_t_necessity_operator \<acute>
          (pp_t_diamond_box_operator \<acute> pp_t_complement ?Rv))"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_modal_operators_in_domain(1)]
        left right inner])
  show ?thesis
    using outer
    unfolding pp_t_box_diamond_box_operator_apply[OF Rw]
      pp_t_box_diamond_box_operator_apply[OF cRv] .
qed

lemma pp_t_dual_negation_guard_diamond_box_diamond_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_diamond_box_diamond_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_diamond_box_diamond_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof -
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have inner:
      "pp_t_eqv Prop v
        (pp_t_box_diamond_operator \<acute> ?Rw)
        (pp_t_box_diamond_operator \<acute> pp_t_complement ?Rv)"
    using pp_t_dual_negation_guard_box_diamond_target[of w]
    unfolding v_def .
  have left:
      "Elem (pp_t_box_diamond_operator \<acute> ?Rw)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(1) Rw])
  have right:
      "Elem (pp_t_box_diamond_operator \<acute> pp_t_complement ?Rv)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(1) cRv])
  have outer:
      "pp_t_eqv Prop v
        (pp_t_possibility_operator \<acute>
          (pp_t_box_diamond_operator \<acute> ?Rw))
        (pp_t_possibility_operator \<acute>
          (pp_t_box_diamond_operator \<acute> pp_t_complement ?Rv))"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_modal_operators_in_domain(2)]
        left right inner])
  show ?thesis
    using outer
    unfolding pp_t_diamond_box_diamond_operator_apply[OF Rw]
      pp_t_diamond_box_diamond_operator_apply[OF cRv] .
qed

theorem pp_t_dual_modal_depth_three_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_box_diamond_box_operator
    (pp_t_recurrent_modal_component
      pp_t_box_diamond_box_operator) w"
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_diamond_box_diamond_operator
    (pp_t_recurrent_modal_component
      pp_t_diamond_box_diamond_operator) w"
proof -
  show "pp_t_operator_boundary_antipatching
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_box_diamond_box_operator
      (pp_t_recurrent_modal_component
        pp_t_box_diamond_box_operator) w"
    by (rule pp_t_dual_negation_guard_modal_antipatching[
      where v="w @ [True, True]"
        and b="pp_t_box_diamond_box_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))",
      OF _ pp_t_modal_depth_three_operators_in_domain(1)
        pp_t_app_closed[
          OF pp_t_modal_depth_three_operators_in_domain(1)
            pp_t_complement_in_domain]
        pp_t_dual_negation_guard_box_diamond_box_target])
      (simp,
       rule pp_t_no_box_diamond_box_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  show "pp_t_operator_boundary_antipatching
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_diamond_box_diamond_operator
      (pp_t_recurrent_modal_component
        pp_t_diamond_box_diamond_operator) w"
    by (rule pp_t_dual_negation_guard_modal_antipatching[
      where v="w @ [True, True]"
        and b="pp_t_diamond_box_diamond_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))",
      OF _ pp_t_modal_depth_three_operators_in_domain(2)
        pp_t_app_closed[
          OF pp_t_modal_depth_three_operators_in_domain(2)
            pp_t_complement_in_domain]
        pp_t_dual_negation_guard_diamond_box_diamond_target])
      (simp,
       rule pp_t_no_diamond_box_diamond_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
qed

corollary pp_t_dual_modal_depth_three_sections_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section
      pp_t_box_diamond_box_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        pp_t_box_diamond_box_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section
      pp_t_diamond_box_diamond_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        pp_t_diamond_box_diamond_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section
        pp_t_box_diamond_box_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_depth_three_operators_in_domain(1)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_depth_three_operators_in_domain(1)]
        pp_t_dual_modal_depth_three_boundary_antipatching(1)])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          pp_t_box_diamond_box_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_depth_three_operators_in_domain(1)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_depth_three_operators_in_domain(1)]
          pp_t_dual_modal_depth_three_boundary_recurrences(1)])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section
        pp_t_diamond_box_diamond_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_depth_three_operators_in_domain(2)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_depth_three_operators_in_domain(2)]
        pp_t_dual_modal_depth_three_boundary_antipatching(2)])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          pp_t_diamond_box_diamond_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_depth_three_operators_in_domain(2)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_depth_three_operators_in_domain(2)]
          pp_t_dual_modal_depth_three_boundary_recurrences(2)])
qed

section \<open>A general negation-closed section extension\<close>

definition pp_t_negation_closed_section_extension ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      ZF set \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_negation_closed_section_extension S D w X
    \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_one_context_unary_type)
    \<and>
    (S w X
      \<or>
     (\<exists>P \<in> D.
       pp_t_eqv pp_t_one_context_unary_type w X P
       \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
         (pp_t_pointwise_complement P)))"

lemma pp_t_negation_closed_section_extension_admissible:
  assumes S:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and D:
      "\<And>P. P \<in> D \<Longrightarrow>
        Elem P (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_predicate_admissible pp_t_one_context_unary_type
      (pp_t_negation_closed_section_extension S D)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have base: "S v X = S v Y"
    using S X Y XY wv
    unfolding pp_t_predicate_admissible_def by blast
  have class_eq:
      "\<And>P. Elem P (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type v X P
          =
        pp_t_eqv pp_t_one_context_unary_type v Y P"
  proof -
    fix P
    assume P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    show "pp_t_eqv pp_t_one_context_unary_type v X P
        =
      pp_t_eqv pp_t_one_context_unary_type v Y P"
      using pp_t_reverse_eqv_class_predicate_admissible[OF P]
        X Y XY wv
      unfolding pp_t_predicate_admissible_def by blast
  qed
  show
      "pp_t_negation_closed_section_extension S D v X
        = pp_t_negation_closed_section_extension S D v Y"
    unfolding pp_t_negation_closed_section_extension_def
    using X Y base class_eq D pp_t_pointwise_complement_in_domain
    by blast
qed

lemma pp_t_negation_closed_section_extension_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_negation_closed_section_extension S D w X"
    and S_negation:
      "\<And>Y. Elem Y (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S w Y
        \<Longrightarrow> S w (pp_t_pointwise_complement Y)"
    and D:
      "\<And>P. P \<in> D \<Longrightarrow>
        Elem P (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_negation_closed_section_extension S D w
      (pp_t_pointwise_complement X)"
proof -
  let ?N = pp_t_pointwise_complement
  have NX: "Elem (?N X) (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  from stock have cases:
      "S w X
      \<or>
       (\<exists>P \<in> D.
        pp_t_eqv pp_t_one_context_unary_type w X P
        \<or>
        pp_t_eqv pp_t_one_context_unary_type w X (?N P))"
    unfolding pp_t_negation_closed_section_extension_def by blast
  from cases show ?thesis
  proof
    assume base: "S w X"
    show ?thesis
      unfolding pp_t_negation_closed_section_extension_def
      using NX S_negation[OF X base] by blast
  next
    assume generated:
        "\<exists>P \<in> D.
          pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w X (?N P)"
    obtain P where Pset: "P \<in> D"
      and XP:
        "pp_t_eqv pp_t_one_context_unary_type w X P
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X (?N P)"
      using generated by blast
    have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
      by (rule D[OF Pset])
    have NP: "Elem (?N P) (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF P])
    have result:
        "pp_t_eqv pp_t_one_context_unary_type w (?N X) P
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w (?N X) (?N P)"
    proof -
      from XP show ?thesis
      proof
        assume XP0:
            "pp_t_eqv pp_t_one_context_unary_type w X P"
        then show ?thesis
          using pp_t_pointwise_complement_respects_equivalence[
            OF X P] by blast
      next
        assume XP1:
            "pp_t_eqv pp_t_one_context_unary_type w X (?N P)"
        have complements:
            "pp_t_eqv pp_t_one_context_unary_type w
              (?N X) (?N (?N P))"
          by (rule pp_t_pointwise_complement_respects_equivalence[
            OF X NP XP1])
        have involution: "?N (?N P) = P"
          by (rule pp_t_pointwise_complement_involution[OF P])
        show ?thesis using complements unfolding involution by blast
      qed
    qed
    show ?thesis
      unfolding pp_t_negation_closed_section_extension_def
      using NX Pset result by blast
  qed
qed

theorem pp_t_negation_closed_section_extension_recombines:
  assumes base:
      "pp_t_unary_recombines_at S R w"
    and R: "Elem R (pp_t_domain Prop)"
    and D:
      "\<And>P. P \<in> D \<Longrightarrow>
        Elem P (pp_t_domain pp_t_one_context_unary_type)"
    and safe:
      "\<And>P. P \<in> D \<Longrightarrow>
        pp_t_recombination_safe_unary_operator P R w"
    and safe_complement:
      "\<And>P. P \<in> D \<Longrightarrow>
        pp_t_recombination_safe_unary_operator
          (pp_t_pointwise_complement P) R w"
  shows
    "pp_t_unary_recombines_at
      (pp_t_negation_closed_section_extension S D) R w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock:
      "pp_t_negation_closed_section_extension S D w X"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> R) v"
    and q: "Elem q (pp_t_domain Prop)"
  have X_safe: "pp_t_recombination_safe_unary_operator X R w"
  proof -
    from stock have cases:
        "S w X
        \<or>
         (\<exists>P \<in> D.
          pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w X
            (pp_t_pointwise_complement P))"
      unfolding pp_t_negation_closed_section_extension_def by blast
    from cases show ?thesis
    proof
      assume old: "S w X"
      show ?thesis
        using base X old
        unfolding pp_t_unary_recombines_at_def
          pp_t_recombination_safe_unary_operator_def
        by blast
    next
      assume generated:
          "\<exists>P \<in> D.
            pp_t_eqv pp_t_one_context_unary_type w X P
            \<or>
            pp_t_eqv pp_t_one_context_unary_type w X
              (pp_t_pointwise_complement P)"
      obtain P where Pset: "P \<in> D"
        and XP:
          "pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
            (pp_t_pointwise_complement P)"
        using generated by blast
      have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
        by (rule D[OF Pset])
      have NP:
          "Elem (pp_t_pointwise_complement P)
            (pp_t_domain pp_t_one_context_unary_type)"
        by (rule pp_t_pointwise_complement_in_domain[OF P])
      from XP show ?thesis
      proof
        assume XP0:
            "pp_t_eqv pp_t_one_context_unary_type w X P"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X P XP0 R safe[OF Pset]])
      next
        assume XP1:
            "pp_t_eqv pp_t_one_context_unary_type w X
              (pp_t_pointwise_complement P)"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X NP XP1 R safe_complement[OF Pset]])
      qed
    qed
  qed
  show "pp_t_holds (X \<acute> q) w"
    using X_safe necessary q
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
qed

section \<open>The complete positive-modal generated stock\<close>

definition pp_t_dual_modal_depth_three_generated_sections :: "ZF set"
where
  "pp_t_dual_modal_depth_three_generated_sections =
    {pp_t_dual_recurrent_full_section
        pp_t_box_diamond_box_operator,
     pp_t_dual_recurrent_full_section
        pp_t_diamond_box_diamond_operator}"

lemma pp_t_dual_modal_depth_three_generated_section_in_domain:
  assumes "P \<in> pp_t_dual_modal_depth_three_generated_sections"
  shows "Elem P (pp_t_domain pp_t_one_context_unary_type)"
proof -
  have cases:
      "P = pp_t_dual_recurrent_full_section
          pp_t_box_diamond_box_operator
      \<or>
       P = pp_t_dual_recurrent_full_section
          pp_t_diamond_box_diamond_operator"
    using assms
    unfolding pp_t_dual_modal_depth_three_generated_sections_def
    by blast
  then show ?thesis
  proof
    assume P:
        "P = pp_t_dual_recurrent_full_section
          pp_t_box_diamond_box_operator"
    show ?thesis
      unfolding P
      by (rule pp_t_dual_recurrent_full_section_in_domain[
        OF pp_t_modal_depth_three_operators_in_domain(1)])
  next
    assume P:
        "P = pp_t_dual_recurrent_full_section
          pp_t_diamond_box_diamond_operator"
    show ?thesis
      unfolding P
      by (rule pp_t_dual_recurrent_full_section_in_domain[
        OF pp_t_modal_depth_three_operators_in_domain(2)])
  qed
qed

abbreviation pp_t_dual_positive_modal_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_dual_positive_modal_stock \<equiv>
    pp_t_negation_closed_section_extension
      pp_t_dual_modal_depth_two_stock
      pp_t_dual_modal_depth_three_generated_sections"

lemma pp_t_dual_positive_modal_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_dual_positive_modal_stock"
  by (rule pp_t_negation_closed_section_extension_admissible[
    OF pp_t_dual_modal_depth_two_stock_admissible
      pp_t_dual_modal_depth_three_generated_section_in_domain])

lemma pp_t_dual_positive_modal_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_positive_modal_stock w X"
  shows
    "pp_t_dual_positive_modal_stock w
      (pp_t_pointwise_complement X)"
  by (rule
    pp_t_negation_closed_section_extension_negation_closed[
      OF X stock pp_t_dual_modal_depth_two_stock_negation_closed
        pp_t_dual_modal_depth_three_generated_section_in_domain])

theorem pp_t_dual_positive_modal_stock_recombines:
  "pp_t_unary_recombines_at pp_t_dual_positive_modal_stock
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof (rule pp_t_negation_closed_section_extension_recombines[
    OF pp_t_dual_modal_depth_two_stock_recombines
      pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
      pp_t_dual_modal_depth_three_generated_section_in_domain])
  fix P
  assume P: "P \<in> pp_t_dual_modal_depth_three_generated_sections"
  then show "pp_t_recombination_safe_unary_operator P
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    unfolding pp_t_dual_modal_depth_three_generated_sections_def
    using pp_t_dual_modal_depth_three_sections_safe
    by blast
next
  fix P
  assume P: "P \<in> pp_t_dual_modal_depth_three_generated_sections"
  then show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement P)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    unfolding pp_t_dual_modal_depth_three_generated_sections_def
    using pp_t_dual_modal_depth_three_sections_safe
    by blast
qed

lemma pp_t_dual_modal_depth_two_stock_subset_positive_modal_stock:
  assumes "pp_t_dual_modal_depth_two_stock w X"
  shows "pp_t_dual_positive_modal_stock w X"
  using assms
  unfolding pp_t_negation_closed_section_extension_def
    pp_t_dual_modal_depth_two_stock_def
  by blast

section \<open>The seven positive S4 modal operators\<close>

lemma pp_t_box_diamond_operator_precompose:
  "pp_t_box_diamond_operator =
    pp_t_qd_precompose
      pp_t_necessity_operator pp_t_possibility_operator"
  unfolding pp_t_box_diamond_unary_def
    pp_t_closed_den_compose by simp

lemma pp_t_diamond_box_operator_precompose:
  "pp_t_diamond_box_operator =
    pp_t_qd_precompose
      pp_t_possibility_operator pp_t_necessity_operator"
  unfolding pp_t_diamond_box_unary_def
    pp_t_closed_den_compose by simp

lemma pp_t_box_diamond_box_operator_precompose:
  "pp_t_box_diamond_box_operator =
    pp_t_qd_precompose
      pp_t_necessity_operator pp_t_diamond_box_operator"
  unfolding pp_t_box_diamond_box_unary_def
    pp_t_closed_den_compose by simp

lemma pp_t_diamond_box_diamond_operator_precompose:
  "pp_t_diamond_box_diamond_operator =
    pp_t_qd_precompose
      pp_t_possibility_operator pp_t_box_diamond_operator"
  unfolding pp_t_diamond_box_diamond_unary_def
    pp_t_closed_den_compose by simp

lemma pp_t_qd_precompose_associative:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and H: "Elem H (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_qd_precompose F (pp_t_qd_precompose G H)
      = pp_t_qd_precompose (pp_t_qd_precompose F G) H"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_qd_precompose F (pp_t_qd_precompose G H))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[
      OF F pp_t_qd_precompose_in_domain[OF G H]])
  show "Elem (pp_t_qd_precompose (pp_t_qd_precompose F G) H)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[
      OF pp_t_qd_precompose_in_domain[OF F G] H])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have Hp: "Elem (H \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF H p])
  have GHp: "Elem (G \<acute> (H \<acute> p)) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF G Hp])
  show "pp_t_qd_precompose F (pp_t_qd_precompose G H) \<acute> p
      = pp_t_qd_precompose (pp_t_qd_precompose F G) H \<acute> p"
    unfolding pp_t_qd_precompose_apply[OF p]
      pp_t_qd_precompose_apply[OF Hp]
      pp_t_qd_precompose_apply[OF GHp] ..
qed

lemma pp_t_qd_precompose_identity_right:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_qd_precompose F (pp_t_closed_den prop_id) = F"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_qd_precompose F (pp_t_closed_den prop_id))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[
      OF F pp_t_closed_den_in_domain[OF typed_prop_id]])
  show "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule F)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_qd_precompose F (pp_t_closed_den prop_id) \<acute> p
      = F \<acute> p"
    unfolding pp_t_qd_precompose_apply[OF p]
      pp_t_closed_identity_apply[OF p] ..
qed

lemma pp_t_box_diamond_operator_idempotent:
  "pp_t_qd_precompose
      pp_t_box_diamond_operator pp_t_box_diamond_operator
    = pp_t_box_diamond_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_qd_precompose
        pp_t_box_diamond_operator pp_t_box_diamond_operator)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain)
      (rule pp_t_modal_depth_two_operators_in_domain)+
  show "Elem pp_t_box_diamond_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_depth_two_operators_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have NMp:
      "Elem (pp_t_box_diamond_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(1) p])
  show
      "pp_t_qd_precompose
          pp_t_box_diamond_operator pp_t_box_diamond_operator \<acute> p
        = pp_t_box_diamond_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_qd_precompose
          pp_t_box_diamond_operator pp_t_box_diamond_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_qd_precompose_in_domain[
          OF pp_t_modal_depth_two_operators_in_domain(1)
            pp_t_modal_depth_two_operators_in_domain(1)] p])
    show "Elem (pp_t_box_diamond_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule NMp)
    fix w
    show
        "pp_t_holds
          (pp_t_qd_precompose
            pp_t_box_diamond_operator pp_t_box_diamond_operator
            \<acute> p) w
        =
        pp_t_holds (pp_t_box_diamond_operator \<acute> p) w"
      unfolding pp_t_qd_precompose_apply[OF p]
      using pp_t_box_diamond_operator_apply_holds[OF NMp, of w]
        pp_t_box_diamond_operator_apply_holds[OF p]
      by (meson prefix_order.refl prefix_order.trans)
  qed
qed

lemma pp_t_diamond_box_operator_idempotent:
  "pp_t_qd_precompose
      pp_t_diamond_box_operator pp_t_diamond_box_operator
    = pp_t_diamond_box_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_qd_precompose
        pp_t_diamond_box_operator pp_t_diamond_box_operator)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain)
      (rule pp_t_modal_depth_two_operators_in_domain)+
  show "Elem pp_t_diamond_box_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_depth_two_operators_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have MNp:
      "Elem (pp_t_diamond_box_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(2) p])
  show
      "pp_t_qd_precompose
          pp_t_diamond_box_operator pp_t_diamond_box_operator \<acute> p
        = pp_t_diamond_box_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_qd_precompose
          pp_t_diamond_box_operator pp_t_diamond_box_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_qd_precompose_in_domain[
          OF pp_t_modal_depth_two_operators_in_domain(2)
            pp_t_modal_depth_two_operators_in_domain(2)] p])
    show "Elem (pp_t_diamond_box_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule MNp)
    fix w
    show
        "pp_t_holds
          (pp_t_qd_precompose
            pp_t_diamond_box_operator pp_t_diamond_box_operator
            \<acute> p) w
        =
        pp_t_holds (pp_t_diamond_box_operator \<acute> p) w"
      unfolding pp_t_qd_precompose_apply[OF p]
      using pp_t_diamond_box_operator_apply_holds[OF MNp, of w]
        pp_t_diamond_box_operator_apply_holds[OF p]
      by (meson prefix_order.refl prefix_order.trans)
  qed
qed

lemma pp_t_positive_modal_absorptions:
  "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_box_diamond_operator
    = pp_t_box_diamond_operator"
  "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_diamond_box_operator
    = pp_t_diamond_box_operator"
  "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_box_diamond_box_operator
    = pp_t_box_diamond_box_operator"
  "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_diamond_box_diamond_operator
    = pp_t_diamond_box_diamond_operator"
  "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_diamond_box_diamond_operator
    = pp_t_box_diamond_operator"
  "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_box_diamond_box_operator
    = pp_t_diamond_box_operator"
proof -
  show "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_box_diamond_operator
      = pp_t_box_diamond_operator"
    unfolding pp_t_box_diamond_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_modal_operators_in_domain(1)
          pp_t_modal_operators_in_domain(2)]
      pp_t_box_box_operator_collapse
    by simp
  show "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_diamond_box_operator
      = pp_t_diamond_box_operator"
    unfolding pp_t_diamond_box_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_modal_operators_in_domain(2)
          pp_t_modal_operators_in_domain(1)]
      pp_t_diamond_diamond_operator_collapse
    by simp
  show "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_box_diamond_box_operator
      = pp_t_box_diamond_box_operator"
    unfolding pp_t_box_diamond_box_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_modal_operators_in_domain(1)
          pp_t_modal_depth_two_operators_in_domain(2)]
      pp_t_box_box_operator_collapse
    by simp
  show "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_diamond_box_diamond_operator
      = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_diamond_box_diamond_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_modal_operators_in_domain(2)
          pp_t_modal_depth_two_operators_in_domain(1)]
      pp_t_diamond_diamond_operator_collapse
    by simp
  have NM_domain:
      "Elem pp_t_box_diamond_operator
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_depth_two_operators_in_domain)
  show "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_diamond_box_diamond_operator
      = pp_t_box_diamond_operator"
    unfolding pp_t_diamond_box_diamond_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_modal_operators_in_domain(2) NM_domain]
      pp_t_box_diamond_operator_precompose[symmetric]
      pp_t_box_diamond_operator_idempotent
    by simp
  have MN_domain:
      "Elem pp_t_diamond_box_operator
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_depth_two_operators_in_domain)
  show "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_box_diamond_box_operator
      = pp_t_diamond_box_operator"
    unfolding pp_t_box_diamond_box_operator_precompose
      pp_t_qd_precompose_associative[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_modal_operators_in_domain(1) MN_domain]
      pp_t_diamond_box_operator_precompose[symmetric]
      pp_t_diamond_box_operator_idempotent
    by simp
qed

definition pp_t_positive_modal_normal_form :: "ZF \<Rightarrow> bool" where
  "pp_t_positive_modal_normal_form F
    \<longleftrightarrow>
    F = pp_t_closed_den prop_id
    \<or> F = pp_t_necessity_operator
    \<or> F = pp_t_possibility_operator
    \<or> F = pp_t_box_diamond_operator
    \<or> F = pp_t_diamond_box_operator
    \<or> F = pp_t_box_diamond_box_operator
    \<or> F = pp_t_diamond_box_diamond_operator"

lemma pp_t_positive_modal_normal_form_box:
  assumes "pp_t_positive_modal_normal_form F"
  shows
    "pp_t_positive_modal_normal_form
      (pp_t_qd_precompose pp_t_necessity_operator F)"
proof -
  from assms have cases:
      "F = pp_t_closed_den prop_id
      \<or> F = pp_t_necessity_operator
      \<or> F = pp_t_possibility_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_box_diamond_box_operator
      \<or> F = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_positive_modal_normal_form_def .
  then show ?thesis
  proof (elim disjE)
    assume F: "F = pp_t_closed_den prop_id"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(1)]
      by blast
  next
    assume F: "F = pp_t_necessity_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_box_box_operator_collapse
      by blast
  next
    assume F: "F = pp_t_possibility_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_box_diamond_operator_precompose[symmetric]
      by blast
  next
    assume F: "F = pp_t_box_diamond_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(1)
      by blast
  next
    assume F: "F = pp_t_diamond_box_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_box_diamond_box_operator_precompose[symmetric]
      by blast
  next
    assume F: "F = pp_t_box_diamond_box_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(3)
      by blast
  next
    assume F: "F = pp_t_diamond_box_diamond_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(5)
      by blast
  qed
qed

lemma pp_t_positive_modal_normal_form_diamond:
  assumes "pp_t_positive_modal_normal_form F"
  shows
    "pp_t_positive_modal_normal_form
      (pp_t_qd_precompose pp_t_possibility_operator F)"
proof -
  from assms have cases:
      "F = pp_t_closed_den prop_id
      \<or> F = pp_t_necessity_operator
      \<or> F = pp_t_possibility_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_box_diamond_box_operator
      \<or> F = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_positive_modal_normal_form_def .
  then show ?thesis
  proof (elim disjE)
    assume F: "F = pp_t_closed_den prop_id"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(2)]
      by blast
  next
    assume F: "F = pp_t_necessity_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_diamond_box_operator_precompose[symmetric]
      by blast
  next
    assume F: "F = pp_t_possibility_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_diamond_diamond_operator_collapse
      by blast
  next
    assume F: "F = pp_t_box_diamond_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_diamond_box_diamond_operator_precompose[symmetric]
      by blast
  next
    assume F: "F = pp_t_diamond_box_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(2)
      by blast
  next
    assume F: "F = pp_t_box_diamond_box_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(6)
      by blast
  next
    assume F: "F = pp_t_diamond_box_diamond_operator"
    show ?thesis
      unfolding F pp_t_positive_modal_normal_form_def
      using pp_t_positive_modal_absorptions(4)
      by blast
  qed
qed

inductive pp_t_positive_modal_word :: "ZF \<Rightarrow> bool" where
  identity:
    "pp_t_positive_modal_word (pp_t_closed_den prop_id)"
| box:
    "pp_t_positive_modal_word F
      \<Longrightarrow>
     pp_t_positive_modal_word
      (pp_t_qd_precompose pp_t_necessity_operator F)"
| diamond:
    "pp_t_positive_modal_word F
      \<Longrightarrow>
     pp_t_positive_modal_word
      (pp_t_qd_precompose pp_t_possibility_operator F)"

theorem pp_t_positive_modal_word_normalization:
  assumes "pp_t_positive_modal_word F"
  shows "pp_t_positive_modal_normal_form F"
  using assms
proof induction
  case identity
  show ?case
    unfolding pp_t_positive_modal_normal_form_def by blast
next
  case (box F)
  show ?case
    by (rule pp_t_positive_modal_normal_form_box[OF box.IH])
next
  case (diamond F)
  show ?case
    by (rule pp_t_positive_modal_normal_form_diamond[OF diamond.IH])
qed

section \<open>Absorption of every positive modal word\<close>

lemma pp_t_positive_modal_normal_form_in_domain:
  assumes "pp_t_positive_modal_normal_form F"
  shows "Elem F (pp_t_domain pp_t_one_context_unary_type)"
proof -
  from assms have cases:
      "F = pp_t_closed_den prop_id
      \<or> F = pp_t_necessity_operator
      \<or> F = pp_t_possibility_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_box_diamond_box_operator
      \<or> F = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_positive_modal_normal_form_def .
  then show ?thesis
  proof (elim disjE)
    assume F: "F = pp_t_closed_den prop_id"
    show ?thesis
      unfolding F
      by (rule pp_t_closed_den_in_domain, rule typed_prop_id)
  next
    assume "F = pp_t_necessity_operator"
    then show ?thesis
      using pp_t_modal_operators_in_domain(1) by simp
  next
    assume "F = pp_t_possibility_operator"
    then show ?thesis
      using pp_t_modal_operators_in_domain(2) by simp
  next
    assume "F = pp_t_box_diamond_operator"
    then show ?thesis
      using pp_t_modal_depth_two_operators_in_domain(1) by simp
  next
    assume "F = pp_t_diamond_box_operator"
    then show ?thesis
      using pp_t_modal_depth_two_operators_in_domain(2) by simp
  next
    assume "F = pp_t_box_diamond_box_operator"
    then show ?thesis
      using pp_t_modal_depth_three_operators_in_domain(1) by simp
  next
    assume "F = pp_t_diamond_box_diamond_operator"
    then show ?thesis
      using pp_t_modal_depth_three_operators_in_domain(2) by simp
  qed
qed

lemma pp_t_dual_identity_section_in_positive_modal_stock:
  "pp_t_dual_positive_modal_stock w pp_t_dual_identity_section"
proof -
  have domain:
      "Elem pp_t_dual_identity_section
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_identity_section_in_domain)
  have identity_stock:
      "pp_t_dual_identity_negation_stock w
        pp_t_dual_identity_section"
    unfolding pp_t_dual_identity_negation_stock_def
    using domain pp_t_eqv_reflexive[OF domain, of w]
    by blast
  have modal_stock:
      "pp_t_dual_modal_stock w pp_t_dual_identity_section"
    unfolding pp_t_dual_modal_stock_def
    using domain identity_stock by blast
  have full_stock:
      "pp_t_dual_full_modal_stock w pp_t_dual_identity_section"
    unfolding pp_t_dual_full_modal_stock_def
    using domain modal_stock by blast
  have depth_two_stock:
      "pp_t_dual_modal_depth_two_stock w
        pp_t_dual_identity_section"
    unfolding pp_t_dual_modal_depth_two_stock_def
    using domain full_stock by blast
  show ?thesis
    by (rule
      pp_t_dual_modal_depth_two_stock_subset_positive_modal_stock[
        OF depth_two_stock])
qed

lemma pp_t_dual_modal_generated_section_in_positive_modal_stock:
  assumes "P \<in> pp_t_dual_modal_generated_sections"
  shows "pp_t_dual_positive_modal_stock w P"
  apply (rule pp_t_dual_modal_depth_two_stock_subset_positive_modal_stock)
  apply (rule pp_t_dual_full_modal_stock_subset_depth_two_stock)
  by (rule pp_t_dual_modal_generated_section_in_full_stock[OF assms])

lemma pp_t_dual_modal_depth_three_generated_section_in_positive_modal_stock:
  assumes "P \<in> pp_t_dual_modal_depth_three_generated_sections"
  shows "pp_t_dual_positive_modal_stock w P"
proof -
  have domain:
      "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule
      pp_t_dual_modal_depth_three_generated_section_in_domain[OF assms])
  show ?thesis
    unfolding pp_t_negation_closed_section_extension_def
    using domain assms pp_t_eqv_reflexive[OF domain, of w]
    by blast
qed

theorem pp_t_positive_modal_normal_form_sections_absorbed:
  assumes normal: "pp_t_positive_modal_normal_form F"
  shows
    "pp_t_dual_positive_modal_stock w
      (pp_t_dual_recurrent_full_section F)"
    "pp_t_dual_positive_modal_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))"
proof -
  from normal have cases:
      "F = pp_t_closed_den prop_id
      \<or> F = pp_t_necessity_operator
      \<or> F = pp_t_possibility_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_box_diamond_box_operator
      \<or> F = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_positive_modal_normal_form_def .
  show stock:
      "pp_t_dual_positive_modal_stock w
        (pp_t_dual_recurrent_full_section F)"
  proof (rule disjE[OF cases])
    assume F: "F = pp_t_closed_den prop_id"
    show ?thesis
      unfolding F
      by (rule pp_t_dual_identity_section_in_positive_modal_stock)
  next
    assume rest:
        "F = pp_t_necessity_operator
        \<or> F = pp_t_possibility_operator
        \<or> F = pp_t_box_diamond_operator
        \<or> F = pp_t_diamond_box_operator
        \<or> F = pp_t_box_diamond_box_operator
        \<or> F = pp_t_diamond_box_diamond_operator"
    then show ?thesis
    proof (elim disjE)
      assume F: "F = pp_t_necessity_operator"
      show ?thesis
        unfolding F
        apply (rule
          pp_t_dual_modal_generated_section_in_positive_modal_stock)
        unfolding pp_t_dual_modal_generated_sections_def
        by simp
    next
      assume F: "F = pp_t_possibility_operator"
      show ?thesis
        unfolding F
        apply (rule
          pp_t_dual_modal_generated_section_in_positive_modal_stock)
        unfolding pp_t_dual_modal_generated_sections_def
        by simp
    next
      assume F: "F = pp_t_box_diamond_operator"
      show ?thesis
        apply (rule
          pp_t_dual_modal_depth_two_stock_subset_positive_modal_stock)
        apply (rule pp_t_modal_depth_two_sections_normalize(1))
        unfolding F pp_t_modal_depth_two_indices_def
        by simp
    next
      assume F: "F = pp_t_diamond_box_operator"
      show ?thesis
        apply (rule
          pp_t_dual_modal_depth_two_stock_subset_positive_modal_stock)
        apply (rule pp_t_modal_depth_two_sections_normalize(1))
        unfolding F pp_t_modal_depth_two_indices_def
        by simp
    next
      assume F: "F = pp_t_box_diamond_box_operator"
      show ?thesis
        apply (rule
          pp_t_dual_modal_depth_three_generated_section_in_positive_modal_stock)
        unfolding F pp_t_dual_modal_depth_three_generated_sections_def
        by simp
    next
      assume F: "F = pp_t_diamond_box_diamond_operator"
      show ?thesis
        apply (rule
          pp_t_dual_modal_depth_three_generated_section_in_positive_modal_stock)
        unfolding F pp_t_dual_modal_depth_three_generated_sections_def
        by simp
    qed
  qed
  have section_domain:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_positive_modal_normal_form_in_domain[OF normal]])
  show
      "pp_t_dual_positive_modal_stock w
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section F))"
    by (rule pp_t_dual_positive_modal_stock_negation_closed[
      OF section_domain stock])
qed

corollary pp_t_positive_modal_word_sections_absorbed:
  assumes "pp_t_positive_modal_word F"
  shows
    "pp_t_dual_positive_modal_stock w
      (pp_t_dual_recurrent_full_section F)"
    "pp_t_dual_positive_modal_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))"
  by (rule pp_t_positive_modal_normal_form_sections_absorbed[
      OF pp_t_positive_modal_word_normalization[OF assms]])+

end
