theory Bacon_PP_ZF_Tree_Dual_Modal_Depth_Two
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Quantified_Absorption.Bacon_PP_ZF_Tree_Dual_Quantified_Absorption
begin

section \<open>The two genuine modal-depth-two alternations\<close>

definition pp_t_box_diamond_unary :: oterm where
  "pp_t_box_diamond_unary =
    pp_compose pp_t_necessity_unary pp_t_possibility_unary"

definition pp_t_diamond_box_unary :: oterm where
  "pp_t_diamond_box_unary =
    pp_compose pp_t_possibility_unary pp_t_necessity_unary"

lemma pp_t_modal_depth_two_terms_typed:
  "[] \<turnstile> pp_t_box_diamond_unary :
    pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_diamond_box_unary :
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
  show "[] \<turnstile> pp_t_box_diamond_unary :
      pp_t_one_context_unary_type"
    unfolding pp_t_box_diamond_unary_def
    using typed_pp_compose[OF N M]
    unfolding pp_unary_ty_def .
  show "[] \<turnstile> pp_t_diamond_box_unary :
      pp_t_one_context_unary_type"
    unfolding pp_t_diamond_box_unary_def
    using typed_pp_compose[OF M N]
    unfolding pp_unary_ty_def .
qed

lemma pp_t_modal_depth_two_terms_logical:
  "pp_logical_vocabulary pp_t_box_diamond_unary"
  "pp_logical_vocabulary pp_t_diamond_box_unary"
  unfolding pp_t_box_diamond_unary_def
    pp_t_diamond_box_unary_def
  using pp_t_modal_unary_terms_logical
  by (simp_all add: pp_compose_def
      pp_logical_vocabulary_def shift_def)

abbreviation pp_t_box_diamond_operator :: ZF where
  "pp_t_box_diamond_operator \<equiv>
    pp_t_closed_den pp_t_box_diamond_unary"

abbreviation pp_t_diamond_box_operator :: ZF where
  "pp_t_diamond_box_operator \<equiv>
    pp_t_closed_den pp_t_diamond_box_unary"

lemma pp_t_modal_depth_two_operators_in_domain:
  "Elem pp_t_box_diamond_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  "Elem pp_t_diamond_box_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_closed_den_in_domain,
      rule pp_t_modal_depth_two_terms_typed)+

lemma pp_t_box_diamond_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_box_diamond_operator \<acute> p
      = pp_t_necessity_operator \<acute>
          (pp_t_possibility_operator \<acute> p)"
  unfolding pp_t_box_diamond_unary_def
    pp_t_closed_den_compose
  by (rule pp_t_qd_precompose_apply[OF p])

lemma pp_t_diamond_box_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_diamond_box_operator \<acute> p
      = pp_t_possibility_operator \<acute>
          (pp_t_necessity_operator \<acute> p)"
  unfolding pp_t_diamond_box_unary_def
    pp_t_closed_den_compose
  by (rule pp_t_qd_precompose_apply[OF p])

lemma pp_t_box_diamond_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_box_diamond_operator \<acute> p) w
      \<longleftrightarrow>
     (\<forall>v. prefix w v \<longrightarrow>
       (\<exists>u. prefix v u \<and> pp_t_holds p u))"
proof -
  have Mp:
      "Elem (pp_t_possibility_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2) p])
  show ?thesis
    unfolding pp_t_box_diamond_operator_apply[OF p]
      pp_t_necessity_operator_apply_holds[OF Mp]
      pp_t_possibility_operator_apply_holds[OF p]
    by blast
qed

lemma pp_t_diamond_box_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_diamond_box_operator \<acute> p) w
      \<longleftrightarrow>
     (\<exists>v. prefix w v
       \<and> (\<forall>u. prefix v u \<longrightarrow> pp_t_holds p u))"
proof -
  have Np:
      "Elem (pp_t_necessity_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1) p])
  show ?thesis
    unfolding pp_t_diamond_box_operator_apply[OF p]
      pp_t_possibility_operator_apply_holds[OF Np]
      pp_t_necessity_operator_apply_holds[OF p]
    by blast
qed

section \<open>The repeated modalities collapse on the S4 tree\<close>

lemma pp_t_box_box_operator_collapse:
  "pp_t_qd_precompose
      pp_t_necessity_operator pp_t_necessity_operator
    = pp_t_necessity_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_qd_precompose
        pp_t_necessity_operator pp_t_necessity_operator)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain)
      (rule pp_t_modal_operators_in_domain)+
  show "Elem pp_t_necessity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have Np: "Elem (pp_t_necessity_operator \<acute> p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1) p])
  show
      "pp_t_qd_precompose
          pp_t_necessity_operator pp_t_necessity_operator \<acute> p
        = pp_t_necessity_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_qd_precompose
          pp_t_necessity_operator pp_t_necessity_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_qd_precompose_in_domain[
          OF pp_t_modal_operators_in_domain(1)
            pp_t_modal_operators_in_domain(1)] p])
    show "Elem (pp_t_necessity_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule Np)
    fix w
    show
        "pp_t_holds
          (pp_t_qd_precompose
            pp_t_necessity_operator pp_t_necessity_operator \<acute> p) w
        =
        pp_t_holds (pp_t_necessity_operator \<acute> p) w"
      unfolding pp_t_qd_precompose_apply[OF p]
      using pp_t_necessity_operator_apply_holds[OF Np, of w]
        pp_t_necessity_operator_apply_holds[OF p]
      by (meson prefix_order.refl prefix_order.trans)
  qed
qed

lemma pp_t_diamond_diamond_operator_collapse:
  "pp_t_qd_precompose
      pp_t_possibility_operator pp_t_possibility_operator
    = pp_t_possibility_operator"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_qd_precompose
        pp_t_possibility_operator pp_t_possibility_operator)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_qd_precompose_in_domain)
      (rule pp_t_modal_operators_in_domain)+
  show "Elem pp_t_possibility_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have Mp: "Elem (pp_t_possibility_operator \<acute> p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2) p])
  show
      "pp_t_qd_precompose
          pp_t_possibility_operator pp_t_possibility_operator \<acute> p
        = pp_t_possibility_operator \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_qd_precompose
          pp_t_possibility_operator pp_t_possibility_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_qd_precompose_in_domain[
          OF pp_t_modal_operators_in_domain(2)
            pp_t_modal_operators_in_domain(2)] p])
    show "Elem (pp_t_possibility_operator \<acute> p)
        (pp_t_domain Prop)"
      by (rule Mp)
    fix w
    show
        "pp_t_holds
          (pp_t_qd_precompose
            pp_t_possibility_operator pp_t_possibility_operator \<acute> p) w
        =
        pp_t_holds (pp_t_possibility_operator \<acute> p) w"
      unfolding pp_t_qd_precompose_apply[OF p]
      using pp_t_possibility_operator_apply_holds[OF Mp, of w]
        pp_t_possibility_operator_apply_holds[OF p]
      by (meson prefix_order.refl prefix_order.trans)
  qed
qed

section \<open>Neither alternation has a complement fixed point\<close>

lemma pp_t_no_box_diamond_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_box_diamond_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Fq = "pp_t_box_diamond_operator \<acute> ?q"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  assume fixed: "pp_t_eqv Prop w p ?Fq"
  have contradiction_if_false:
      "\<And>v. prefix w v \<Longrightarrow> \<not> pp_t_holds p v
        \<Longrightarrow> False"
  proof -
    fix v
    assume wv: "prefix w v"
      and not_p_v: "\<not> pp_t_holds p v"
    have fixed_v: "pp_t_eqv Prop v p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wv])
    have not_Fq_v: "\<not> pp_t_holds ?Fq v"
      using pp_t_prop_eqv_at[OF fixed_v, of v] not_p_v
      by simp
    have not_all:
        "\<not> (\<forall>u. prefix v u \<longrightarrow>
          (\<exists>z. prefix u z \<and> pp_t_holds ?q z))"
      using pp_t_box_diamond_operator_apply_holds[OF q, of v]
        not_Fq_v
      by simp
    obtain u where vu: "prefix v u"
      and no_q: "\<not> (\<exists>z. prefix u z \<and> pp_t_holds ?q z)"
      using not_all by blast
    have not_possible:
        "\<not> pp_t_holds
          (pp_t_possibility_operator \<acute> ?q) u"
      using pp_t_possibility_operator_apply_holds[OF q, of u]
        no_q
      by simp
    have p_u: "pp_t_holds p u"
      using pp_t_possibility_operator_apply_holds[OF q, of u]
        not_possible
      by auto
    have wu: "prefix w u"
      by (rule prefix_order.trans[OF wv vu])
    have fixed_u: "pp_t_eqv Prop u p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wu])
    have Fq_u: "pp_t_holds ?Fq u"
      using pp_t_prop_eqv_at[OF fixed_u, of u] p_u by simp
    have possible_u:
        "pp_t_holds (pp_t_possibility_operator \<acute> ?q) u"
    proof -
      have all_possible:
          "\<forall>v. prefix u v \<longrightarrow>
            (\<exists>z. prefix v z \<and> pp_t_holds ?q z)"
        using pp_t_box_diamond_operator_apply_holds[OF q, of u]
          Fq_u
        by blast
      show ?thesis
        using pp_t_possibility_operator_apply_holds[OF q, of u]
          all_possible[rule_format, OF prefix_order.refl]
        by blast
    qed
    show False using possible_u not_possible by blast
  qed
  show False
  proof (cases "pp_t_holds p w")
    case False
    show False
      by (rule contradiction_if_false[OF prefix_order.refl False])
  next
    case True
    have Fq_w: "pp_t_holds ?Fq w"
      using pp_t_prop_eqv_at[OF fixed, of w] True by simp
    have possible_w:
        "pp_t_holds (pp_t_possibility_operator \<acute> ?q) w"
    proof -
      have all_possible:
          "\<forall>v. prefix w v \<longrightarrow>
            (\<exists>z. prefix v z \<and> pp_t_holds ?q z)"
        using pp_t_box_diamond_operator_apply_holds[OF q, of w]
          Fq_w
        by blast
      show ?thesis
        using pp_t_possibility_operator_apply_holds[OF q, of w]
          all_possible[rule_format, OF prefix_order.refl]
        by blast
    qed
    obtain v where wv: "prefix w v"
      and q_v: "pp_t_holds ?q v"
      using pp_t_possibility_operator_apply_holds[OF q, of w]
        possible_w
      by blast
    have not_p_v: "\<not> pp_t_holds p v"
      using q_v by simp
    show False
      by (rule contradiction_if_false[OF wv not_p_v])
  qed
qed

lemma pp_t_no_diamond_box_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_diamond_box_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Fq = "pp_t_diamond_box_operator \<acute> ?q"
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
    obtain u where vu: "prefix v u"
      and all_q:
        "\<forall>z. prefix u z \<longrightarrow> pp_t_holds ?q z"
      using pp_t_diamond_box_operator_apply_holds[OF q, of v]
        Fq_v
      by blast
    have not_p_u: "\<not> pp_t_holds p u"
      using all_q[rule_format, OF prefix_order.refl] by simp
    have wu: "prefix w u"
      by (rule prefix_order.trans[OF wv vu])
    have fixed_u: "pp_t_eqv Prop u p ?Fq"
      by (rule pp_t_eqv_persistent[OF fixed wu])
    have not_Fq_u: "\<not> pp_t_holds ?Fq u"
      using pp_t_prop_eqv_at[OF fixed_u, of u] not_p_u
      by simp
    have Fq_u: "pp_t_holds ?Fq u"
    proof -
      have witness:
          "\<exists>v. prefix u v
            \<and> (\<forall>z. prefix v z \<longrightarrow> pp_t_holds ?q z)"
        using all_q by (intro exI[of _ u]) simp
      show ?thesis
        using pp_t_diamond_box_operator_apply_holds[OF q, of u]
          witness
        by blast
    qed
    show False using Fq_u not_Fq_u by blast
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
    have no_box:
        "\<forall>v. prefix w v \<longrightarrow>
          \<not> (\<forall>u. prefix v u \<longrightarrow> pp_t_holds ?q u)"
      using pp_t_diamond_box_operator_apply_holds[OF q, of w]
        not_Fq_w
      by blast
    obtain u where wu: "prefix w u"
      and not_q_u: "\<not> pp_t_holds ?q u"
      using no_box[rule_format, OF prefix_order.refl]
      by blast
    have p_u: "pp_t_holds p u"
      using not_q_u by simp
    show False
      by (rule contradiction_if_true[OF wu p_u])
  qed
qed

section \<open>Boundary recurrence for the two alternations\<close>

theorem pp_t_dual_recurrent_box_diamond_boundary_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_box_diamond_operator w"
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
  have cross_true:
      "\<forall>z. prefix ?v z \<longrightarrow>
        pp_t_holds (pp_t_box_diamond_operator \<acute> ?R w) z"
  proof (intro allI impI)
    fix z
    assume vz: "prefix ?v z"
    have dense:
        "\<forall>a. prefix z a \<longrightarrow>
          (\<exists>u. prefix a u \<and> pp_t_holds (?R w) u)"
    proof (intro allI impI)
      fix a
      assume za: "prefix z a"
      have va: "prefix ?v a"
        by (rule prefix_order.trans[OF vz za])
      show "\<exists>u. prefix a u \<and> pp_t_holds (?R w) u"
        using all_true[rule_format, OF va]
        by (intro exI[of _ a]) simp
    qed
    show "pp_t_holds
        (pp_t_box_diamond_operator \<acute> ?R w) z"
      using pp_t_box_diamond_operator_apply_holds[OF Rw, of z]
        dense
      by blast
  qed
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_box_diamond_operator \<acute> ?R w)
        (pp_zf_truth True)"
    using cross_true
    unfolding pp_t_prop_eqv_truth_iff .
  have truth_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth True)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_truth_boundary[
      OF r true_cone false_cone])
  have target_domain:
      "Elem (pp_t_box_diamond_operator \<acute> ?R w)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(1) Rw])
  have target_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v
        (pp_t_box_diamond_operator \<acute> ?R w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain truth_boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using target_boundary
    by (intro exI[of _ ?v]) simp
qed

theorem pp_t_dual_recurrent_diamond_box_boundary_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_diamond_box_operator w"
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
  let ?v = "w @ f"
  have Rw: "Elem (?R w) (pp_t_domain Prop)"
    by (rule
      pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have all_false:
      "\<forall>z. prefix ?v z \<longrightarrow> \<not> pp_t_holds (?R w) z"
  proof (intro allI impI)
    fix z
    assume future: "prefix ?v z"
    obtain u where z: "z = (w @ f) @ u"
      using future unfolding prefix_def by blast
    have r_false: "\<not> pp_t_holds ?r (f @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF false_cone, of "f @ u"],
        of "f @ u"]
      by simp
    show "\<not> pp_t_holds (?R w) z"
      using r_false
      unfolding z
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  have cross_false:
      "\<forall>z. prefix ?v z \<longrightarrow>
        \<not> pp_t_holds (pp_t_diamond_box_operator \<acute> ?R w) z"
  proof (intro allI impI notI)
    fix z
    assume vz: "prefix ?v z"
      and cross:
        "pp_t_holds (pp_t_diamond_box_operator \<acute> ?R w) z"
    obtain a where za: "prefix z a"
      and all_true:
        "\<forall>u. prefix a u \<longrightarrow> pp_t_holds (?R w) u"
      using pp_t_diamond_box_operator_apply_holds[OF Rw, of z]
        cross
      by blast
    have va: "prefix ?v a"
      by (rule prefix_order.trans[OF vz za])
    show False
      using all_false[rule_format, OF va]
        all_true[rule_format, OF prefix_order.refl]
      by blast
  qed
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_diamond_box_operator \<acute> ?R w)
        (pp_zf_truth False)"
    unfolding pp_t_eqv.simps
    using cross_false by simp
  have falsity_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth False)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_falsity_boundary[
      OF r true_cone false_cone])
  have target_domain:
      "Elem (pp_t_diamond_box_operator \<acute> ?R w)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_depth_two_operators_in_domain(2) Rw])
  have target_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v
        (pp_t_diamond_box_operator \<acute> ?R w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain falsity_boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using target_boundary
    by (intro exI[of _ ?v]) simp
qed

section \<open>The guarded negation cone supplies anti-patching\<close>

lemma pp_t_dual_negation_guard_box_diamond_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_box_diamond_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_box_diamond_operator \<acute>
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
        (pp_t_possibility_operator \<acute> ?Rw)
        (pp_t_possibility_operator \<acute> pp_t_complement ?Rv)"
    using pp_t_dual_negation_guard_possibility_target[of w]
    unfolding v_def .
  have MRw:
      "Elem (pp_t_possibility_operator \<acute> ?Rw)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2) Rw])
  have McRv:
      "Elem
        (pp_t_possibility_operator \<acute> pp_t_complement ?Rv)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2) cRv])
  have outer:
      "pp_t_eqv Prop v
        (pp_t_necessity_operator \<acute>
          (pp_t_possibility_operator \<acute> ?Rw))
        (pp_t_necessity_operator \<acute>
          (pp_t_possibility_operator \<acute> pp_t_complement ?Rv))"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_modal_operators_in_domain(1)]
        MRw McRv inner])
  show ?thesis
    using outer
    unfolding pp_t_box_diamond_operator_apply[OF Rw]
      pp_t_box_diamond_operator_apply[OF cRv] .
qed

lemma pp_t_dual_negation_guard_diamond_box_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_diamond_box_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_diamond_box_operator \<acute>
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
        (pp_t_necessity_operator \<acute> ?Rw)
        (pp_t_necessity_operator \<acute> pp_t_complement ?Rv)"
    using pp_t_dual_negation_guard_necessity_target[of w]
    unfolding v_def .
  have NRw:
      "Elem (pp_t_necessity_operator \<acute> ?Rw)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1) Rw])
  have NcRv:
      "Elem
        (pp_t_necessity_operator \<acute> pp_t_complement ?Rv)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1) cRv])
  have outer:
      "pp_t_eqv Prop v
        (pp_t_possibility_operator \<acute>
          (pp_t_necessity_operator \<acute> ?Rw))
        (pp_t_possibility_operator \<acute>
          (pp_t_necessity_operator \<acute> pp_t_complement ?Rv))"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_modal_operators_in_domain(2)]
        NRw NcRv inner])
  show ?thesis
    using outer
    unfolding pp_t_diamond_box_operator_apply[OF Rw]
      pp_t_diamond_box_operator_apply[OF cRv] .
qed

theorem pp_t_dual_recurrent_box_diamond_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_box_diamond_operator
    (pp_t_recurrent_modal_component pp_t_box_diamond_operator) w"
  by (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, True]"
      and b="pp_t_box_diamond_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at
            (w @ [True, True]))",
    OF _ pp_t_modal_depth_two_operators_in_domain(1)
      pp_t_app_closed[
        OF pp_t_modal_depth_two_operators_in_domain(1)
          pp_t_complement_in_domain]
      pp_t_dual_negation_guard_box_diamond_target])
    (simp,
     rule pp_t_no_box_diamond_of_complement_fixed_point[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])

theorem pp_t_dual_recurrent_diamond_box_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_diamond_box_operator
    (pp_t_recurrent_modal_component pp_t_diamond_box_operator) w"
  by (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, True]"
      and b="pp_t_diamond_box_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at
            (w @ [True, True]))",
    OF _ pp_t_modal_depth_two_operators_in_domain(2)
      pp_t_app_closed[
        OF pp_t_modal_depth_two_operators_in_domain(2)
          pp_t_complement_in_domain]
      pp_t_dual_negation_guard_diamond_box_target])
    (simp,
     rule pp_t_no_diamond_box_of_complement_fixed_point[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])

section \<open>The modal-depth-two enlargement\<close>

corollary pp_t_dual_modal_depth_two_sections_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section pp_t_box_diamond_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section pp_t_box_diamond_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section pp_t_diamond_box_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section pp_t_diamond_box_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_box_diamond_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_depth_two_operators_in_domain(1)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_depth_two_operators_in_domain(1)]
        pp_t_dual_recurrent_box_diamond_boundary_antipatching])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_box_diamond_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_depth_two_operators_in_domain(1)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_depth_two_operators_in_domain(1)]
          pp_t_dual_recurrent_box_diamond_boundary_recurrence])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_diamond_box_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_depth_two_operators_in_domain(2)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_depth_two_operators_in_domain(2)]
        pp_t_dual_recurrent_diamond_box_boundary_antipatching])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_diamond_box_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_depth_two_operators_in_domain(2)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_depth_two_operators_in_domain(2)]
          pp_t_dual_recurrent_diamond_box_boundary_recurrence])
qed

definition pp_t_dual_modal_depth_two_generated_sections :: "ZF set"
where
  "pp_t_dual_modal_depth_two_generated_sections =
    {pp_t_dual_recurrent_full_section pp_t_box_diamond_operator,
     pp_t_dual_recurrent_full_section pp_t_diamond_box_operator}"

lemma pp_t_dual_modal_depth_two_generated_section_in_domain:
  assumes "P \<in> pp_t_dual_modal_depth_two_generated_sections"
  shows "Elem P (pp_t_domain pp_t_one_context_unary_type)"
proof -
  have cases:
      "P = pp_t_dual_recurrent_full_section
          pp_t_box_diamond_operator
      \<or>
       P = pp_t_dual_recurrent_full_section
          pp_t_diamond_box_operator"
    using assms
    unfolding pp_t_dual_modal_depth_two_generated_sections_def
    by blast
  then show ?thesis
  proof
    assume P:
        "P = pp_t_dual_recurrent_full_section
          pp_t_box_diamond_operator"
    show ?thesis
      unfolding P
      by (rule pp_t_dual_recurrent_full_section_in_domain[
        OF pp_t_modal_depth_two_operators_in_domain(1)])
  next
    assume P:
        "P = pp_t_dual_recurrent_full_section
          pp_t_diamond_box_operator"
    show ?thesis
      unfolding P
      by (rule pp_t_dual_recurrent_full_section_in_domain[
        OF pp_t_modal_depth_two_operators_in_domain(2)])
  qed
qed

definition pp_t_dual_modal_depth_two_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_dual_modal_depth_two_stock w X
    \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_one_context_unary_type)
    \<and>
    (pp_t_dual_full_modal_stock w X
      \<or>
     (\<exists>P \<in> pp_t_dual_modal_depth_two_generated_sections.
       pp_t_eqv pp_t_one_context_unary_type w X P
       \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
         (pp_t_pointwise_complement P)))"

lemma pp_t_dual_modal_depth_two_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_dual_modal_depth_two_stock"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have base:
      "pp_t_dual_full_modal_stock v X
        = pp_t_dual_full_modal_stock v Y"
    using pp_t_dual_full_modal_stock_admissible X Y XY wv
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
  show "pp_t_dual_modal_depth_two_stock v X
      = pp_t_dual_modal_depth_two_stock v Y"
    unfolding pp_t_dual_modal_depth_two_stock_def
    using X Y base class_eq
      pp_t_dual_modal_depth_two_generated_section_in_domain
      pp_t_pointwise_complement_in_domain
    by blast
qed

lemma pp_t_dual_modal_depth_two_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_modal_depth_two_stock w X"
  shows
    "pp_t_dual_modal_depth_two_stock w
      (pp_t_pointwise_complement X)"
proof -
  let ?N = pp_t_pointwise_complement
  have NX: "Elem (?N X) (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  from stock have cases:
      "pp_t_dual_full_modal_stock w X
      \<or>
       (\<exists>P \<in> pp_t_dual_modal_depth_two_generated_sections.
        pp_t_eqv pp_t_one_context_unary_type w X P
        \<or>
        pp_t_eqv pp_t_one_context_unary_type w X (?N P))"
    unfolding pp_t_dual_modal_depth_two_stock_def by blast
  from cases show ?thesis
  proof
    assume base: "pp_t_dual_full_modal_stock w X"
    show ?thesis
      unfolding pp_t_dual_modal_depth_two_stock_def
      using NX pp_t_dual_full_modal_stock_negation_closed[OF X base]
      by blast
  next
    assume generated:
        "\<exists>P \<in> pp_t_dual_modal_depth_two_generated_sections.
          pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w X (?N P)"
    obtain P where
        Pset: "P \<in> pp_t_dual_modal_depth_two_generated_sections"
      and XP:
        "pp_t_eqv pp_t_one_context_unary_type w X P
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X (?N P)"
      using generated by blast
    have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
      by (rule
        pp_t_dual_modal_depth_two_generated_section_in_domain[OF Pset])
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
      unfolding pp_t_dual_modal_depth_two_stock_def
      using NX Pset result by blast
  qed
qed

theorem pp_t_dual_modal_depth_two_stock_recombines:
  "pp_t_unary_recombines_at pp_t_dual_modal_depth_two_stock
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_modal_depth_two_stock w X"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> ?r) v"
    and q: "Elem q (pp_t_domain Prop)"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have safe: "pp_t_recombination_safe_unary_operator X ?r w"
  proof -
    from stock have cases:
        "pp_t_dual_full_modal_stock w X
        \<or>
         (\<exists>P \<in> pp_t_dual_modal_depth_two_generated_sections.
          pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w X
            (pp_t_pointwise_complement P))"
      unfolding pp_t_dual_modal_depth_two_stock_def by blast
    from cases show ?thesis
    proof
      assume base: "pp_t_dual_full_modal_stock w X"
      show ?thesis
        using pp_t_dual_full_modal_stock_recombines X base
        unfolding pp_t_unary_recombines_at_def
          pp_t_recombination_safe_unary_operator_def
        by blast
    next
      assume generated:
          "\<exists>P \<in> pp_t_dual_modal_depth_two_generated_sections.
            pp_t_eqv pp_t_one_context_unary_type w X P
            \<or>
            pp_t_eqv pp_t_one_context_unary_type w X
              (pp_t_pointwise_complement P)"
      obtain P where
          Pset: "P \<in> pp_t_dual_modal_depth_two_generated_sections"
        and XP:
          "pp_t_eqv pp_t_one_context_unary_type w X P
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
            (pp_t_pointwise_complement P)"
        using generated by blast
      have P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
        by (rule
          pp_t_dual_modal_depth_two_generated_section_in_domain[OF Pset])
      have NP: "Elem (pp_t_pointwise_complement P)
          (pp_t_domain pp_t_one_context_unary_type)"
        by (rule pp_t_pointwise_complement_in_domain[OF P])
      have P_safe:
          "pp_t_recombination_safe_unary_operator P ?r w"
        and NP_safe:
          "pp_t_recombination_safe_unary_operator
            (pp_t_pointwise_complement P) ?r w"
        using Pset
        unfolding pp_t_dual_modal_depth_two_generated_sections_def
        by (auto intro: pp_t_dual_modal_depth_two_sections_safe)
      from XP show ?thesis
      proof
        assume XP0:
            "pp_t_eqv pp_t_one_context_unary_type w X P"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X P XP0 r P_safe])
      next
        assume XP1:
            "pp_t_eqv pp_t_one_context_unary_type w X
              (pp_t_pointwise_complement P)"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X NP XP1 r NP_safe])
      qed
    qed
  qed
  show "pp_t_holds (X \<acute> q) w"
    using safe necessary q
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
qed

section \<open>Normalization of every modal word of length two\<close>

definition pp_t_modal_depth_two_indices :: "ZF set" where
  "pp_t_modal_depth_two_indices =
    {pp_t_qd_precompose
        pp_t_necessity_operator pp_t_necessity_operator,
     pp_t_box_diamond_operator,
     pp_t_diamond_box_operator,
     pp_t_qd_precompose
        pp_t_possibility_operator pp_t_possibility_operator}"

lemma pp_t_dual_full_modal_stock_subset_depth_two_stock:
  assumes "pp_t_dual_full_modal_stock w X"
  shows "pp_t_dual_modal_depth_two_stock w X"
  using assms
  unfolding pp_t_dual_modal_depth_two_stock_def
    pp_t_dual_full_modal_stock_def
  by blast

lemma pp_t_modal_depth_two_index_in_domain:
  assumes "F \<in> pp_t_modal_depth_two_indices"
  shows "Elem F (pp_t_domain pp_t_one_context_unary_type)"
proof -
  from assms have cases:
      "F = pp_t_qd_precompose
          pp_t_necessity_operator pp_t_necessity_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_qd_precompose
          pp_t_possibility_operator pp_t_possibility_operator"
    unfolding pp_t_modal_depth_two_indices_def by blast
  then show ?thesis
    using pp_t_modal_depth_two_operators_in_domain
      pp_t_qd_precompose_in_domain[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_modal_operators_in_domain(1)]
      pp_t_qd_precompose_in_domain[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_modal_operators_in_domain(2)]
    by blast
qed

theorem pp_t_modal_depth_two_sections_normalize:
  assumes "F \<in> pp_t_modal_depth_two_indices"
  shows
    "pp_t_dual_modal_depth_two_stock w
      (pp_t_dual_recurrent_full_section F)"
    "pp_t_dual_modal_depth_two_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))"
proof -
  have cases:
      "F = pp_t_qd_precompose
          pp_t_necessity_operator pp_t_necessity_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_qd_precompose
          pp_t_possibility_operator pp_t_possibility_operator"
    using assms
    unfolding pp_t_modal_depth_two_indices_def by blast
  show stock:
      "pp_t_dual_modal_depth_two_stock w
        (pp_t_dual_recurrent_full_section F)"
  proof (rule disjE[OF cases])
    assume F:
        "F = pp_t_qd_precompose
          pp_t_necessity_operator pp_t_necessity_operator"
    have F0: "F = pp_t_necessity_operator"
      using F pp_t_box_box_operator_collapse by simp
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_full_modal_stock_subset_depth_two_stock)
      apply (rule pp_t_dual_modal_generated_section_in_full_stock)
      by (simp add: pp_t_dual_modal_generated_sections_def)
  next
    assume rest:
        "F = pp_t_box_diamond_operator
        \<or> F = pp_t_diamond_box_operator
        \<or> F = pp_t_qd_precompose
          pp_t_possibility_operator pp_t_possibility_operator"
    then show ?thesis
    proof
      assume F: "F = pp_t_box_diamond_operator"
      have P:
          "pp_t_dual_recurrent_full_section F
            \<in> pp_t_dual_modal_depth_two_generated_sections"
        unfolding F pp_t_dual_modal_depth_two_generated_sections_def
        by simp
      have domain:
          "Elem (pp_t_dual_recurrent_full_section F)
            (pp_t_domain pp_t_one_context_unary_type)"
        by (rule pp_t_dual_recurrent_full_section_in_domain)
          (use F pp_t_modal_depth_two_operators_in_domain(1) in simp)
      show ?thesis
        unfolding pp_t_dual_modal_depth_two_stock_def
        using domain P pp_t_eqv_reflexive[OF domain, of w]
        by blast
    next
      assume rest:
          "F = pp_t_diamond_box_operator
          \<or> F = pp_t_qd_precompose
            pp_t_possibility_operator pp_t_possibility_operator"
      then show ?thesis
      proof
        assume F: "F = pp_t_diamond_box_operator"
        have P:
            "pp_t_dual_recurrent_full_section F
              \<in> pp_t_dual_modal_depth_two_generated_sections"
          unfolding F pp_t_dual_modal_depth_two_generated_sections_def
          by simp
        have domain:
            "Elem (pp_t_dual_recurrent_full_section F)
              (pp_t_domain pp_t_one_context_unary_type)"
          by (rule pp_t_dual_recurrent_full_section_in_domain)
            (use F pp_t_modal_depth_two_operators_in_domain(2) in simp)
        show ?thesis
          unfolding pp_t_dual_modal_depth_two_stock_def
          using domain P pp_t_eqv_reflexive[OF domain, of w]
          by blast
      next
        assume F:
            "F = pp_t_qd_precompose
              pp_t_possibility_operator pp_t_possibility_operator"
        have F0: "F = pp_t_possibility_operator"
          using F pp_t_diamond_diamond_operator_collapse by simp
        show ?thesis
          unfolding F0
          apply (rule pp_t_dual_full_modal_stock_subset_depth_two_stock)
          apply (rule pp_t_dual_modal_generated_section_in_full_stock)
          by (simp add: pp_t_dual_modal_generated_sections_def)
      qed
    qed
  qed
  have domain:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_modal_depth_two_index_in_domain[OF assms]])
  show "pp_t_dual_modal_depth_two_stock w
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))"
    by (rule pp_t_dual_modal_depth_two_stock_negation_closed[
      OF domain stock])
qed

end
