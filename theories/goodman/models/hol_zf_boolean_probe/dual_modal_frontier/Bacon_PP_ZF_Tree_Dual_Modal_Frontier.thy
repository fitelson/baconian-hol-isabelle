theory Bacon_PP_ZF_Tree_Dual_Modal_Frontier
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Constant_Absorption.Bacon_PP_ZF_Tree_Dual_Constant_Absorption
begin

section \<open>Closed necessity and possibility indices\<close>

definition pp_t_necessity_unary :: oterm where
  "pp_t_necessity_unary =
    Lam Prop (\<box>\<^sub>o (Var 0))"

definition pp_t_possibility_unary :: oterm where
  "pp_t_possibility_unary =
    Lam Prop (\<diamond>\<^sub>o (Var 0))"

lemma pp_t_modal_unary_terms_typed:
  "[] \<turnstile> pp_t_necessity_unary :
    pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_possibility_unary :
    pp_t_one_context_unary_type"
  by (rule infer_type_sound;
      simp add: pp_t_necessity_unary_def
        pp_t_possibility_unary_def
        ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)+

lemma pp_t_modal_unary_terms_logical:
  "pp_logical_vocabulary pp_t_necessity_unary"
  "pp_logical_vocabulary pp_t_possibility_unary"
  by (simp_all add: pp_t_necessity_unary_def
      pp_t_possibility_unary_def
      pp_logical_vocabulary_def
      ObjDiamond_def ObjBox_def ObjTrue_def)

abbreviation pp_t_necessity_operator :: ZF where
  "pp_t_necessity_operator \<equiv>
    pp_t_closed_den pp_t_necessity_unary"

abbreviation pp_t_possibility_operator :: ZF where
  "pp_t_possibility_operator \<equiv>
    pp_t_closed_den pp_t_possibility_unary"

lemma pp_t_modal_operators_in_domain:
  "Elem pp_t_necessity_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  "Elem pp_t_possibility_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_closed_den_in_domain,
      rule pp_t_modal_unary_terms_typed)+

lemma pp_t_necessity_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_necessity_operator \<acute> p) w
      \<longleftrightarrow>
     (\<forall>v. prefix w v \<longrightarrow> pp_t_holds p v)"
  unfolding pp_t_closed_den_def pp_t_necessity_unary_def
  using p
  by (simp add: Lambda_app pp_t_eval_ObjBox_holds)

lemma pp_t_possibility_operator_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_possibility_operator \<acute> p) w
      \<longleftrightarrow>
     (\<exists>v. prefix w v \<and> pp_t_holds p v)"
  unfolding pp_t_closed_den_def pp_t_possibility_unary_def
  using p
  by (simp add: Lambda_app pp_t_eval_ObjDiamond_holds)

lemma pp_t_modal_operators_in_modal_stock:
  "pp_t_probe_modal_boolean_stock w pp_t_necessity_operator"
  "pp_t_probe_modal_boolean_stock w pp_t_possibility_operator"
  by (rule pp_t_closed_logical_unary_in_modal_boolean_stock,
      rule pp_t_modal_unary_terms_typed,
      rule pp_t_modal_unary_terms_logical)+

section \<open>Recombination forces true and false cones in the seed\<close>

lemma pp_t_recombination_nonuniversal_counterworld:
  assumes r: "Elem r (pp_t_domain Prop)"
    and X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "Pure w X"
    and recombines: "pp_t_unary_recombines_at Pure r w"
    and q: "Elem q (pp_t_domain Prop)"
    and counterexample: "\<not> pp_t_holds (X \<acute> q) w"
  shows
    "\<exists>v. prefix w v \<and> \<not> pp_t_holds (X \<acute> r) v"
proof (rule ccontr)
  assume no_witness:
      "\<not> (\<exists>v. prefix w v
        \<and> \<not> pp_t_holds (X \<acute> r) v)"
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> r) v"
    using no_witness by blast
  have universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w"
    using recombines X stock necessary
    unfolding pp_t_unary_recombines_at_def
    by blast
  show False
    using universal q counterexample by blast
qed

lemma pp_t_dual_recurrent_root_seed_has_true_cone:
  "\<exists>v.
    pp_t_eqv Prop v
      pp_t_probe_modal_boolean_dual_recurrent_root_seed
      (pp_zf_truth True)"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?N = "pp_t_necessity_operator"
  let ?X = "pp_t_pointwise_complement ?N"
  let ?q = "pp_zf_truth True"
  have r: "Elem ?r (pp_t_domain Prop)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec
    by blast
  have N: "Elem ?N (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain(1))
  have X: "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF N])
  have N_stock: "pp_t_probe_modal_boolean_stock [] ?N"
    by (rule pp_t_modal_operators_in_modal_stock(1))
  have X_stock: "pp_t_probe_modal_boolean_stock [] ?X"
    unfolding pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF N N_stock])
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have Nq: "pp_t_holds (?N \<acute> ?q) []"
    using pp_t_necessity_operator_apply_holds[OF q, of "[]"]
    by simp
  have not_Xq: "\<not> pp_t_holds (?X \<acute> ?q) []"
    using pp_t_pointwise_complement_holds[
      OF q, of ?N "[]"]
      Nq by simp
  obtain v where
      not_Xr: "\<not> pp_t_holds (?X \<acute> ?r) v"
    using pp_t_recombination_nonuniversal_counterworld[
      where Pure=pp_t_probe_modal_boolean_stock,
      OF r X X_stock
        pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[
          THEN conjunct2, THEN conjunct1]
        q not_Xq]
    by blast
  have Nr: "pp_t_holds (?N \<acute> ?r) v"
    using pp_t_pointwise_complement_holds[
      OF r, of ?N v]
      not_Xr by simp
  have all_true:
      "\<forall>z. prefix v z \<longrightarrow> pp_t_holds ?r z"
    using pp_t_necessity_operator_apply_holds[OF r, of v]
      Nr by blast
  have equivalent:
      "pp_t_eqv Prop v ?r (pp_zf_truth True)"
    using all_true
    unfolding pp_t_prop_eqv_truth_iff .
  show ?thesis
    by (rule exI[of _ v]) (rule equivalent)
qed

lemma pp_t_dual_recurrent_root_seed_has_false_cone:
  "\<exists>v.
    pp_t_eqv Prop v
      pp_t_probe_modal_boolean_dual_recurrent_root_seed
      (pp_zf_truth False)"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?M = "pp_t_possibility_operator"
  let ?q = "pp_zf_truth False"
  have r: "Elem ?r (pp_t_domain Prop)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec
    by blast
  have M: "Elem ?M (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_modal_operators_in_domain(2))
  have M_stock: "pp_t_probe_modal_boolean_stock [] ?M"
    by (rule pp_t_modal_operators_in_modal_stock(2))
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have not_Mq: "\<not> pp_t_holds (?M \<acute> ?q) []"
    using pp_t_possibility_operator_apply_holds[OF q, of "[]"]
    by simp
  obtain v where
      not_Mr: "\<not> pp_t_holds (?M \<acute> ?r) v"
    using pp_t_recombination_nonuniversal_counterworld[
      where Pure=pp_t_probe_modal_boolean_stock,
      OF r M M_stock
        pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[
          THEN conjunct2, THEN conjunct1]
        q not_Mq]
    by blast
  have all_false:
      "\<forall>z. prefix v z \<longrightarrow> \<not> pp_t_holds ?r z"
    using pp_t_possibility_operator_apply_holds[OF r, of v]
      not_Mr by blast
  have equivalent:
      "pp_t_eqv Prop v ?r (pp_zf_truth False)"
    unfolding pp_t_eqv.simps
    using all_false by simp
  show ?thesis
    by (rule exI[of _ v]) (rule equivalent)
qed

lemma pp_t_reset_seed_on_truth_boundary:
  assumes r: "Elem r (pp_t_domain Prop)"
    and true_cone: "pp_t_eqv Prop t r (pp_zf_truth True)"
    and false_cone: "pp_t_eqv Prop f r (pp_zf_truth False)"
  shows
    "pp_t_fundamental_boundary
      (pp_t_cone_lift w r) w (pp_zf_truth True)"
proof -
  have reset: "Elem (pp_t_cone_lift w r) (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have not_equivalent:
      "\<not> pp_t_eqv Prop w
        (pp_t_cone_lift w r) (pp_zf_truth True)"
  proof
    assume equivalent:
        "pp_t_eqv Prop w
          (pp_t_cone_lift w r) (pp_zf_truth True)"
    have at_false:
        "pp_t_holds (pp_t_cone_lift w r) (w @ f)
          \<longleftrightarrow>
         pp_t_holds (pp_zf_truth True) (w @ f)"
      by (rule pp_t_prop_eqv_at[OF equivalent], simp)
    have r_false: "\<not> pp_t_holds r f"
      using pp_t_prop_eqv_at[OF false_cone, of f]
      by simp
    show False
      using at_false r_false
      by (simp add: pp_t_cone_lift_holds)
  qed
  have recovered:
      "pp_t_eqv Prop (w @ t)
        (pp_t_cone_lift w r) (pp_zf_truth True)"
  unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix (w @ t) z"
    obtain u where z: "z = (w @ t) @ u"
      using future unfolding prefix_def
      by blast
    have r_true: "pp_t_holds r (t @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF true_cone, of "t @ u"],
        of "t @ u"]
      by simp
    show "pp_t_holds (pp_t_cone_lift w r) z
        = pp_t_holds (pp_zf_truth True) z"
      using r_true
      unfolding z
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem (pp_zf_truth True) (pp_t_domain Prop)"
      by (rule pp_t_truth_in_domain)
    show "\<not> pp_t_eqv Prop w
        (pp_t_cone_lift w r) (pp_zf_truth True)"
      by (rule not_equivalent)
    show "\<exists>v. prefix w v \<and>
        pp_t_eqv Prop v
          (pp_t_cone_lift w r) (pp_zf_truth True)"
    proof (rule exI[of _ "w @ t"], intro conjI)
      show "prefix w (w @ t)" by simp
      show "pp_t_eqv Prop (w @ t)
          (pp_t_cone_lift w r) (pp_zf_truth True)"
        by (rule recovered)
    qed
  qed
qed

lemma pp_t_reset_seed_on_falsity_boundary:
  assumes r: "Elem r (pp_t_domain Prop)"
    and true_cone: "pp_t_eqv Prop t r (pp_zf_truth True)"
    and false_cone: "pp_t_eqv Prop f r (pp_zf_truth False)"
  shows
    "pp_t_fundamental_boundary
      (pp_t_cone_lift w r) w (pp_zf_truth False)"
proof -
  have reset: "Elem (pp_t_cone_lift w r) (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have not_equivalent:
      "\<not> pp_t_eqv Prop w
        (pp_t_cone_lift w r) (pp_zf_truth False)"
  proof
    assume equivalent:
        "pp_t_eqv Prop w
          (pp_t_cone_lift w r) (pp_zf_truth False)"
    have at_true:
        "pp_t_holds (pp_t_cone_lift w r) (w @ t)
          \<longleftrightarrow>
         pp_t_holds (pp_zf_truth False) (w @ t)"
      by (rule pp_t_prop_eqv_at[OF equivalent], simp)
    have r_true: "pp_t_holds r t"
      using pp_t_prop_eqv_at[OF true_cone, of t]
      by simp
    show False
      using at_true r_true
      by (simp add: pp_t_cone_lift_holds)
  qed
  have recovered:
      "pp_t_eqv Prop (w @ f)
        (pp_t_cone_lift w r) (pp_zf_truth False)"
  unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix (w @ f) z"
    obtain u where z: "z = (w @ f) @ u"
      using future unfolding prefix_def
      by blast
    have r_false: "\<not> pp_t_holds r (f @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF false_cone, of "f @ u"],
        of "f @ u"]
      by simp
    show "pp_t_holds (pp_t_cone_lift w r) z
        = pp_t_holds (pp_zf_truth False) z"
      using r_false
      unfolding z
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem (pp_zf_truth False) (pp_t_domain Prop)"
      by (rule pp_t_truth_in_domain)
    show "\<not> pp_t_eqv Prop w
        (pp_t_cone_lift w r) (pp_zf_truth False)"
      by (rule not_equivalent)
    show "\<exists>v. prefix w v \<and>
        pp_t_eqv Prop v
          (pp_t_cone_lift w r) (pp_zf_truth False)"
    proof (rule exI[of _ "w @ f"], intro conjI)
      show "prefix w (w @ f)" by simp
      show "pp_t_eqv Prop (w @ f)
          (pp_t_cone_lift w r) (pp_zf_truth False)"
        by (rule recovered)
    qed
  qed
qed

theorem pp_t_dual_recurrent_necessity_boundary_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_necessity_operator w"
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
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_necessity_operator \<acute> ?R w)
        (pp_zf_truth True)"
  proof -
    have Rw: "Elem (?R w) (pp_t_domain Prop)"
      by (rule
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
    have all_true:
        "\<forall>z. prefix ?v z \<longrightarrow>
          pp_t_holds (?R w) z"
    proof (intro allI impI)
      fix z
      assume future: "prefix ?v z"
      obtain u where z: "z = (w @ t) @ u"
        using future unfolding prefix_def
        by blast
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
    have necessary_true:
        "\<forall>z. prefix ?v z \<longrightarrow>
          pp_t_holds (pp_t_necessity_operator \<acute> ?R w) z"
    proof (intro allI impI)
      fix z
      assume vz: "prefix ?v z"
      have after_z:
          "\<forall>u. prefix z u \<longrightarrow> pp_t_holds (?R w) u"
      proof (intro allI impI)
        fix u
        assume zu: "prefix z u"
        have vu: "prefix ?v u"
          by (rule prefix_order.trans[OF vz zu])
        show "pp_t_holds (?R w) u"
          using all_true vu by blast
      qed
      show "pp_t_holds (pp_t_necessity_operator \<acute> ?R w) z"
        using pp_t_necessity_operator_apply_holds[OF Rw, of z]
          after_z
        by blast
    qed
    show ?thesis
      using necessary_true
      unfolding pp_t_prop_eqv_truth_iff .
  qed
  have truth_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth True)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_truth_boundary[
      OF r true_cone false_cone])
  have target_domain:
      "Elem (pp_t_necessity_operator \<acute> ?R w)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1)
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  have target_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v
        (pp_t_necessity_operator \<acute> ?R w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain truth_boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using target_boundary
    by (intro exI[of _ ?v]) simp
qed

theorem pp_t_dual_recurrent_possibility_boundary_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_possibility_operator w"
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
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_possibility_operator \<acute> ?R w)
        (pp_zf_truth False)"
  proof -
    have Rw: "Elem (?R w) (pp_t_domain Prop)"
      by (rule
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
    have all_false:
        "\<forall>z. prefix ?v z \<longrightarrow>
          \<not> pp_t_holds (?R w) z"
    proof (intro allI impI)
      fix z
      assume future: "prefix ?v z"
      obtain u where z: "z = (w @ f) @ u"
        using future unfolding prefix_def
        by blast
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
    have possibility_false:
        "\<forall>z. prefix ?v z \<longrightarrow>
          \<not> pp_t_holds
            (pp_t_possibility_operator \<acute> ?R w) z"
    proof (intro allI impI)
      fix z
      assume vz: "prefix ?v z"
      show "\<not> pp_t_holds
          (pp_t_possibility_operator \<acute> ?R w) z"
      proof
        assume possible:
            "pp_t_holds (pp_t_possibility_operator \<acute> ?R w) z"
        obtain u where zu: "prefix z u"
          and true_u: "pp_t_holds (?R w) u"
          using pp_t_possibility_operator_apply_holds[OF Rw, of z]
            possible
          by blast
        have vu: "prefix ?v u"
          by (rule prefix_order.trans[OF vz zu])
        show False
          using all_false vu true_u by blast
      qed
    qed
    show ?thesis
      unfolding pp_t_eqv.simps
      using possibility_false by simp
  qed
  have falsity_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth False)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_falsity_boundary[
      OF r true_cone false_cone])
  have target_domain:
      "Elem (pp_t_possibility_operator \<acute> ?R w)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2)
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  have target_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v
        (pp_t_possibility_operator \<acute> ?R w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain falsity_boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using target_boundary
    by (intro exI[of _ ?v]) simp
qed

section \<open>The modal singleton components are genuinely nonuniversal\<close>

lemma pp_t_no_necessity_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_necessity_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Nq = "pp_t_necessity_operator \<acute> ?q"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  assume fixed: "pp_t_eqv Prop w p ?Nq"
  have at_w:
      "pp_t_holds p w \<longleftrightarrow> pp_t_holds ?Nq w"
    by (rule pp_t_prop_eqv_at[OF fixed], simp)
  show False
  proof (cases "pp_t_holds p w")
    case True
    then have Nq: "pp_t_holds ?Nq w"
      using at_w by blast
    have not_p: "\<not> pp_t_holds p w"
      using pp_t_necessity_operator_apply_holds[OF q, of w]
        Nq by simp
    show False using True not_p by blast
  next
    case False
    then have not_Nq: "\<not> pp_t_holds ?Nq w"
      using at_w by blast
    have not_all:
        "\<not> (\<forall>v. prefix w v \<longrightarrow> pp_t_holds ?q v)"
      using pp_t_necessity_operator_apply_holds[OF q, of w]
        not_Nq by blast
    obtain v where wv: "prefix w v"
      and not_q_v: "\<not> pp_t_holds ?q v"
      using not_all by blast
    have p_v: "pp_t_holds p v"
      using not_q_v by simp
    have fixed_v: "pp_t_eqv Prop v p ?Nq"
      by (rule pp_t_eqv_persistent[OF fixed wv])
    have at_v:
        "pp_t_holds p v \<longleftrightarrow> pp_t_holds ?Nq v"
      by (rule pp_t_prop_eqv_at[OF fixed_v], simp)
    have Nq_v: "pp_t_holds ?Nq v"
      using at_v p_v by blast
    have not_p_v: "\<not> pp_t_holds p v"
      using pp_t_necessity_operator_apply_holds[OF q, of v]
        Nq_v by simp
    show False using p_v not_p_v by blast
  qed
qed

lemma pp_t_no_possibility_of_complement_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv Prop w p
      (pp_t_possibility_operator \<acute> pp_t_complement p)"
proof
  let ?q = "pp_t_complement p"
  let ?Mq = "pp_t_possibility_operator \<acute> ?q"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  assume fixed: "pp_t_eqv Prop w p ?Mq"
  have at_w:
      "pp_t_holds p w \<longleftrightarrow> pp_t_holds ?Mq w"
    by (rule pp_t_prop_eqv_at[OF fixed], simp)
  show False
  proof (cases "pp_t_holds p w")
    case False
    have Mq: "pp_t_holds ?Mq w"
      using pp_t_possibility_operator_apply_holds[OF q, of w]
        False by auto
    show False using at_w False Mq by blast
  next
    case True
    then have Mq: "pp_t_holds ?Mq w"
      using at_w by blast
    obtain v where wv: "prefix w v"
      and not_p_v: "\<not> pp_t_holds p v"
      using pp_t_possibility_operator_apply_holds[OF q, of w]
        Mq by auto
    have fixed_v: "pp_t_eqv Prop v p ?Mq"
      by (rule pp_t_eqv_persistent[OF fixed wv])
    have at_v:
        "pp_t_holds p v \<longleftrightarrow> pp_t_holds ?Mq v"
      by (rule pp_t_prop_eqv_at[OF fixed_v], simp)
    have Mq_v: "pp_t_holds ?Mq v"
      using pp_t_possibility_operator_apply_holds[OF q, of v]
        not_p_v by auto
    show False using at_v not_p_v Mq_v by blast
  qed
qed

lemma pp_t_dual_recurrent_singleton_impure_if_unreachable:
  assumes p: "Elem p (pp_t_domain Prop)"
    and unreachable:
      "\<And>v. prefix w v \<Longrightarrow>
        \<not> pp_t_eqv Prop v
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) p"
  shows
    "\<not> pp_t_probe_modal_boolean_stock w
      (pp_t_singleton_family_at p)"
proof
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?S = "pp_t_singleton_family_at p"
  assume singleton: "pp_t_probe_modal_boolean_stock w ?S"
  have S: "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  have complement:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_pointwise_complement ?S)"
    unfolding pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF S singleton])
  obtain v where wv: "prefix w v"
    and reached: "pp_t_eqv Prop v ?r p"
    using pp_t_pure_singleton_parameter_must_reach_fundamental[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        p singleton complement
        pp_t_probe_modal_boolean_dual_recurrent_seed_recombines]
    by blast
  show False using unreachable[OF wv] reached by blast
qed

lemma pp_t_dual_recurrent_necessity_singleton_component_nonuniversal:
  "\<not> (\<forall>q. Elem q (pp_t_domain Prop)
    \<longrightarrow>
    pp_t_holds
      ((pp_t_recurrent_modal_component pp_t_necessity_operator)
        \<acute> q) w)"
proof (rule notI)
  assume universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_holds
          ((pp_t_recurrent_modal_component pp_t_necessity_operator)
            \<acute> q) w"
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?q = "pp_t_complement ?r"
  let ?p = "pp_t_necessity_operator \<acute> ?q"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF pp_t_modal_operators_in_domain(1) q])
  have impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?p)"
  proof (rule pp_t_dual_recurrent_singleton_impure_if_unreachable[OF p])
    fix v
    assume "prefix w v"
    show "\<not> pp_t_eqv Prop v ?r ?p"
      by (rule pp_t_no_necessity_of_complement_fixed_point[OF r])
  qed
  have component:
      "pp_t_holds
        ((pp_t_recurrent_modal_component pp_t_necessity_operator)
          \<acute> ?q) w"
    using universal q by blast
  have singleton:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?p)"
    using pp_t_modal_singleton_operator_probe_apply_holds[
      OF pp_t_modal_operators_in_domain(1) q, of w]
      component by blast
  show False using impure singleton by blast
qed

lemma pp_t_dual_recurrent_possibility_singleton_component_nonuniversal:
  "\<not> (\<forall>q. Elem q (pp_t_domain Prop)
    \<longrightarrow>
    pp_t_holds
      ((pp_t_recurrent_modal_component pp_t_possibility_operator)
        \<acute> q) w)"
proof (rule notI)
  assume universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_holds
          ((pp_t_recurrent_modal_component pp_t_possibility_operator)
            \<acute> q) w"
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?q = "pp_t_complement ?r"
  let ?p = "pp_t_possibility_operator \<acute> ?q"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF pp_t_modal_operators_in_domain(2) q])
  have impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?p)"
  proof (rule pp_t_dual_recurrent_singleton_impure_if_unreachable[OF p])
    fix v
    assume "prefix w v"
    show "\<not> pp_t_eqv Prop v ?r ?p"
      by (rule pp_t_no_possibility_of_complement_fixed_point[OF r])
  qed
  have component:
      "pp_t_holds
        ((pp_t_recurrent_modal_component pp_t_possibility_operator)
          \<acute> ?q) w"
    using universal q by blast
  have singleton:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?p)"
    using pp_t_modal_singleton_operator_probe_apply_holds[
      OF pp_t_modal_operators_in_domain(2) q, of w]
      component by blast
  show False using impure singleton by blast
qed

section \<open>The guarded negation cone supplies modal anti-patching\<close>

lemma pp_t_dual_negation_guard_strict_complement:
  fixes w :: "bool list"
  assumes nonempty: "u \<noteq> []"
  defines
    "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop (v @ u)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_complement
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  have guarded:
      "\<forall>x.
        pp_t_holds ?r ([True, True] @ x)
          \<longleftrightarrow>
        (if x = [] then True else \<not> pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix (v @ u) z"
    obtain t where z: "z = (v @ u) @ t"
      using future unfolding prefix_def by blast
    have ut_nonempty: "u @ t \<noteq> []"
      using nonempty by auto
    show
      "pp_t_holds
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) z
        =
       pp_t_holds
          (pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)) z"
      using guarded[rule_format, of "u @ t"] ut_nonempty nonempty
      unfolding z v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc nonempty)
  qed
qed

lemma pp_t_dual_negation_guard_necessity_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_necessity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_necessity_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have root: "pp_t_holds ?r []"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have neg_guard:
      "\<forall>x.
        pp_t_holds ?r ([True, True] @ x)
          \<longleftrightarrow>
        (if x = [] then True else \<not> pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have root_TT: "pp_t_holds ?r [True, True]"
    using neg_guard[rule_format, of "[]"] by simp
  have left_false:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?Rw) v"
  proof -
    have witness:
        "\<not> pp_t_holds ?Rw (v @ [True, True])"
      using neg_guard[rule_format, of "[True, True]"] root_TT
      unfolding v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
    show ?thesis
      using pp_t_necessity_operator_apply_holds[OF Rw, of v]
        witness by auto
  qed
  have right_false:
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_complement ?Rv) v"
  proof -
    have not_argument:
        "\<not> pp_t_holds (pp_t_complement ?Rv) v"
      using root
      unfolding
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      using pp_t_necessity_operator_apply_holds[OF cRv, of v]
        not_argument by auto
  qed
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume vz: "prefix v z"
    obtain u where z: "z = v @ u"
      using vz unfolding prefix_def by blast
    show
      "pp_t_holds (pp_t_necessity_operator \<acute> ?Rw) z
        =
       pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_complement ?Rv) z"
    proof (cases "u = []")
      case True
      show ?thesis
        using left_false right_false unfolding z True by simp
    next
      case False
      have args:
          "pp_t_eqv Prop z ?Rw (pp_t_complement ?Rv)"
        using pp_t_dual_negation_guard_strict_complement[
          OF False, where w=w]
        unfolding z v_def .
      have applications:
          "pp_t_eqv Prop z
            (pp_t_necessity_operator \<acute> ?Rw)
            (pp_t_necessity_operator \<acute> pp_t_complement ?Rv)"
        by (rule pp_t_app_respects[
          OF pp_t_eqv_reflexive[
            OF pp_t_modal_operators_in_domain(1)]
            Rw cRv args])
      show ?thesis
        by (rule pp_t_prop_eqv_at[OF applications], simp)
    qed
  qed
qed

lemma pp_t_dual_negation_guard_possibility_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, True]"
  shows
    "pp_t_eqv Prop v
      (pp_t_possibility_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_possibility_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have neg_guard:
      "\<forall>x.
        pp_t_holds ?r ([True, True] @ x)
          \<longleftrightarrow>
        (if x = [] then True else \<not> pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have id_guard:
      "\<forall>x.
        pp_t_holds ?r ([True, False] @ x)
          \<longleftrightarrow>
        (if x = [] then False else pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have left_true:
      "pp_t_holds (pp_t_possibility_operator \<acute> ?Rw) v"
  proof -
    have argument:
        "pp_t_holds ?Rw v"
      using neg_guard[rule_format, of "[]"]
      unfolding v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      using pp_t_possibility_operator_apply_holds[OF Rw, of v]
        argument by auto
  qed
  have right_true:
      "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_complement ?Rv) v"
  proof -
    have witness:
        "pp_t_holds (pp_t_complement ?Rv)
          (v @ [True, False])"
      using id_guard[rule_format, of "[]"]
      unfolding
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      using pp_t_possibility_operator_apply_holds[OF cRv, of v]
        witness by auto
  qed
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume vz: "prefix v z"
    obtain u where z: "z = v @ u"
      using vz unfolding prefix_def by blast
    show
      "pp_t_holds (pp_t_possibility_operator \<acute> ?Rw) z
        =
       pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_complement ?Rv) z"
    proof (cases "u = []")
      case True
      show ?thesis
        using left_true right_true unfolding z True by simp
    next
      case False
      have args:
          "pp_t_eqv Prop z ?Rw (pp_t_complement ?Rv)"
        using pp_t_dual_negation_guard_strict_complement[
          OF False, where w=w]
        unfolding z v_def .
      have applications:
          "pp_t_eqv Prop z
            (pp_t_possibility_operator \<acute> ?Rw)
            (pp_t_possibility_operator \<acute> pp_t_complement ?Rv)"
        by (rule pp_t_app_respects[
          OF pp_t_eqv_reflexive[
            OF pp_t_modal_operators_in_domain(2)]
            Rw cRv args])
      show ?thesis
        by (rule pp_t_prop_eqv_at[OF applications], simp)
    qed
  qed
qed

lemma pp_t_dual_negation_guard_modal_antipatching:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and b: "Elem b (pp_t_domain Prop)"
    and target:
      "pp_t_eqv Prop v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        b"
    and no_fixed:
      "\<And>x. \<not> pp_t_eqv Prop x
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)
        b"
  shows
    "pp_t_operator_boundary_antipatching
      pp_t_probe_modal_boolean_dual_recurrent_seed_at F
      (pp_t_recurrent_modal_component F) w"
proof (unfold pp_t_operator_boundary_antipatching_def,
    intro impI)
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  let ?a = "F \<acute> ?Rw"
  let ?b = b
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have a: "Elem ?a (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F Rw])
  have b: "Elem ?b (pp_t_domain Prop)"
    by (rule b)
  have b_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at ?b)"
  proof (rule pp_t_dual_recurrent_singleton_impure_if_unreachable[
      OF b])
    fix x
    assume "prefix v x"
    show "\<not> pp_t_eqv Prop x ?Rv ?b"
      by (rule no_fixed)
  qed
  have families:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at ?a)
        (pp_t_singleton_family_at ?b)"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF a b, of v]
      target by blast
  have a_singleton_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at ?a)"
  proof
    assume a_pure:
        "pp_t_probe_modal_boolean_stock v
          (pp_t_singleton_family_at ?a)"
    have Sa:
        "Elem (pp_t_singleton_family_at ?a)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_singleton_family_at_in_domain[OF a])
    have Sb:
        "Elem (pp_t_singleton_family_at ?b)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_singleton_family_at_in_domain[OF b])
    have b_pure:
        "pp_t_probe_modal_boolean_stock v
          (pp_t_singleton_family_at ?b)"
      using pp_t_probe_modal_boolean_stock_admissible
        Sa Sb families a_pure
      unfolding pp_t_predicate_admissible_def
      by blast
    show False using b_impure b_pure by blast
  qed
  have component_false:
      "\<not> pp_t_holds
        ((pp_t_recurrent_modal_component F) \<acute> ?Rw) v"
    using pp_t_modal_singleton_operator_probe_apply_holds[
      OF F Rw, of v]
      a_singleton_impure by blast
  have not_boundary:
      "\<not> pp_t_fundamental_boundary ?Rv v ?a"
  proof
    assume boundary: "pp_t_fundamental_boundary ?Rv v ?a"
    obtain x where vx: "prefix v x"
      and reached: "pp_t_eqv Prop x ?Rv ?a"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have target_x: "pp_t_eqv Prop x ?a ?b"
      by (rule pp_t_eqv_persistent[OF target vx])
    have fixed: "pp_t_eqv Prop x ?Rv ?b"
      by (rule pp_t_eqv_transitive[
        OF Rv a b reached target_x])
    show False using no_fixed[of x] fixed by blast
  qed
  show "\<exists>u. prefix w u
      \<and> \<not> pp_t_holds
        ((pp_t_recurrent_modal_component F) \<acute> ?Rw) u
      \<and> \<not> pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at u) u
        (F \<acute> ?Rw)"
    using wv component_false not_boundary
    by (intro exI[of _ v]) blast
qed

theorem pp_t_dual_recurrent_necessity_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_necessity_operator
    (pp_t_recurrent_modal_component pp_t_necessity_operator) w"
  by (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, True]"
      and b="pp_t_necessity_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at
            (w @ [True, True]))",
    OF _ pp_t_modal_operators_in_domain(1)
      pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_complement_in_domain]
      pp_t_dual_negation_guard_necessity_target])
    (simp,
     rule pp_t_no_necessity_of_complement_fixed_point[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])

theorem pp_t_dual_recurrent_possibility_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_possibility_operator
    (pp_t_recurrent_modal_component pp_t_possibility_operator) w"
  by (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, True]"
      and b="pp_t_possibility_operator \<acute>
        pp_t_complement
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at
            (w @ [True, True]))",
    OF _ pp_t_modal_operators_in_domain(2)
      pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_complement_in_domain]
      pp_t_dual_negation_guard_possibility_target])
    (simp,
     rule pp_t_no_possibility_of_complement_fixed_point[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])

section \<open>The exact modal extension premises\<close>

definition pp_t_dual_modal_extension_obligations ::
    "bool list \<Rightarrow> bool"
where
  "pp_t_dual_modal_extension_obligations w
    \<longleftrightarrow>
    pp_t_operator_boundary_antipatching
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_necessity_operator
      (pp_t_recurrent_modal_component pp_t_necessity_operator) w
    \<and>
    pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_necessity_operator w
    \<and>
    pp_t_operator_boundary_antipatching
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_possibility_operator
      (pp_t_recurrent_modal_component pp_t_possibility_operator) w
    \<and>
    pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at
      pp_t_possibility_operator w"

theorem pp_t_dual_modal_extension_obligations:
  "pp_t_dual_modal_extension_obligations w"
  unfolding pp_t_dual_modal_extension_obligations_def
  using
    pp_t_dual_recurrent_necessity_boundary_antipatching[of w]
    pp_t_dual_recurrent_necessity_boundary_recurrence[of w]
    pp_t_dual_recurrent_possibility_boundary_antipatching[of w]
    pp_t_dual_recurrent_possibility_boundary_recurrence[of w]
  by blast

theorem pp_t_dual_modal_extension_obligations_suffice:
  assumes obligations: "pp_t_dual_modal_extension_obligations w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_necessity_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_necessity_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_possibility_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_possibility_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have N_anti:
      "pp_t_operator_boundary_antipatching
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
        pp_t_necessity_operator
        (pp_t_recurrent_modal_component pp_t_necessity_operator) w"
    and N_rec:
      "pp_t_operator_boundary_recurrence
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
        pp_t_necessity_operator w"
    and M_anti:
      "pp_t_operator_boundary_antipatching
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
        pp_t_possibility_operator
        (pp_t_recurrent_modal_component pp_t_possibility_operator) w"
    and M_rec:
      "pp_t_operator_boundary_recurrence
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
        pp_t_possibility_operator w"
    using obligations
    unfolding pp_t_dual_modal_extension_obligations_def
    by blast+
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_necessity_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_operators_in_domain(1)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_operators_in_domain(1)]
        N_anti])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_necessity_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_operators_in_domain(1)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_operators_in_domain(1)]
          N_rec])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section pp_t_possibility_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_modal_operators_in_domain(2)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_modal_operators_in_domain(2)]
        M_anti])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section pp_t_possibility_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_modal_operators_in_domain(2)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_modal_operators_in_domain(2)]
          M_rec])
qed

corollary pp_t_dual_modal_generated_sections_recombination_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section pp_t_necessity_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section pp_t_necessity_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section pp_t_possibility_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section pp_t_possibility_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule pp_t_dual_modal_extension_obligations_suffice[
      OF pp_t_dual_modal_extension_obligations])+

end
