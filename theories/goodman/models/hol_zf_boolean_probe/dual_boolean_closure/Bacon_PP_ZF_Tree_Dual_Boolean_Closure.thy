theory Bacon_PP_ZF_Tree_Dual_Boolean_Closure
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Normalization.Bacon_PP_ZF_Tree_Dual_Modal_Normalization
begin

section \<open>Conjunction preserves Recombination safety\<close>

abbreviation pp_t_unary_output_conjunction :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_unary_output_conjunction X Y \<equiv>
    (pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y"

lemma pp_t_recombination_safe_unary_conjunction:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and X_safe: "pp_t_recombination_safe_unary_operator X r w"
    and Y_safe: "pp_t_recombination_safe_unary_operator Y r w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_conjunction X Y) r w"
proof (unfold pp_t_recombination_safe_unary_operator_def,
    intro impI)
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds
          (pp_t_unary_output_conjunction X Y \<acute> r) v"
  have X_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> r) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have conjunction:
        "pp_t_holds
          (pp_t_unary_output_conjunction X Y \<acute> r) v"
      using necessary wv by blast
    show "pp_t_holds (X \<acute> r) v"
      using pp_t_unary_output_conjunction_apply_holds[
        OF X Y r, of v]
        conjunction by blast
  qed
  have Y_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (Y \<acute> r) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have conjunction:
        "pp_t_holds
          (pp_t_unary_output_conjunction X Y \<acute> r) v"
      using necessary wv by blast
    show "pp_t_holds (Y \<acute> r) v"
      using pp_t_unary_output_conjunction_apply_holds[
        OF X Y r, of v]
        conjunction by blast
  qed
  have X_universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w"
    using X_safe X_necessary
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
  have Y_universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (Y \<acute> q) w"
    using Y_safe Y_necessary
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
  show
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_holds
          (pp_t_unary_output_conjunction X Y \<acute> q) w"
  proof (intro allI impI)
    fix q
    assume q: "Elem q (pp_t_domain Prop)"
    show
        "pp_t_holds
          (pp_t_unary_output_conjunction X Y \<acute> q) w"
      using pp_t_unary_output_conjunction_apply_holds[
        OF X Y q, of w]
        X_universal Y_universal q
      by blast
  qed
qed

section \<open>The exact extra condition for disjunction\<close>

definition pp_t_joint_operator_antipatching ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_joint_operator_antipatching X Y r w
    \<longleftrightarrow>
    ((\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> \<not> pp_t_holds (X \<acute> q) w
        \<and> \<not> pp_t_holds (Y \<acute> q) w)
      \<longrightarrow>
     (\<exists>v.
        prefix w v
        \<and> \<not> pp_t_holds (X \<acute> r) v
        \<and> \<not> pp_t_holds (Y \<acute> r) v))"

theorem pp_t_disjunction_recombination_safe_iff_joint_antipatching:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction X Y) r w
      \<longleftrightarrow>
     pp_t_joint_operator_antipatching X Y r w"
proof
  assume safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction X Y) r w"
  show "pp_t_joint_operator_antipatching X Y r w"
    unfolding pp_t_joint_operator_antipatching_def
  proof (intro impI)
    assume counterexample:
        "\<exists>q.
          Elem q (pp_t_domain Prop)
          \<and> \<not> pp_t_holds (X \<acute> q) w
          \<and> \<not> pp_t_holds (Y \<acute> q) w"
    obtain q where q: "Elem q (pp_t_domain Prop)"
      and not_Xq: "\<not> pp_t_holds (X \<acute> q) w"
      and not_Yq: "\<not> pp_t_holds (Y \<acute> q) w"
      using counterexample by blast
    show
        "\<exists>v.
          prefix w v
          \<and> \<not> pp_t_holds (X \<acute> r) v
          \<and> \<not> pp_t_holds (Y \<acute> r) v"
    proof (rule ccontr)
      assume no_common:
          "\<not> (\<exists>v.
            prefix w v
            \<and> \<not> pp_t_holds (X \<acute> r) v
            \<and> \<not> pp_t_holds (Y \<acute> r) v)"
      have necessary:
          "\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds
              (pp_t_unary_output_disjunction X Y \<acute> r) v"
      proof (intro allI impI)
        fix v
        assume wv: "prefix w v"
        have alternatives:
            "pp_t_holds (X \<acute> r) v
              \<or> pp_t_holds (Y \<acute> r) v"
          using no_common wv by blast
        show
            "pp_t_holds
              (pp_t_unary_output_disjunction X Y \<acute> r) v"
          using pp_t_unary_output_disjunction_apply_holds[
            OF X Y r, of v]
            alternatives by blast
      qed
      have universal:
          "\<forall>p. Elem p (pp_t_domain Prop)
            \<longrightarrow>
            pp_t_holds
              (pp_t_unary_output_disjunction X Y \<acute> p) w"
        using safe necessary
        unfolding pp_t_recombination_safe_unary_operator_def
        by blast
      have disjunction_q:
          "pp_t_holds
            (pp_t_unary_output_disjunction X Y \<acute> q) w"
        using universal q by blast
      have "pp_t_holds (X \<acute> q) w
          \<or> pp_t_holds (Y \<acute> q) w"
        using pp_t_unary_output_disjunction_apply_holds[
          OF X Y q, of w]
          disjunction_q by blast
      then show False using not_Xq not_Yq by blast
    qed
  qed
next
  assume joint: "pp_t_joint_operator_antipatching X Y r w"
  show
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction X Y) r w"
    unfolding pp_t_recombination_safe_unary_operator_def
  proof (intro impI allI)
    fix q
    assume necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds
            (pp_t_unary_output_disjunction X Y \<acute> r) v"
      and q: "Elem q (pp_t_domain Prop)"
    show
        "pp_t_holds
          (pp_t_unary_output_disjunction X Y \<acute> q) w"
    proof (rule ccontr)
      assume not_disjunction:
          "\<not> pp_t_holds
            (pp_t_unary_output_disjunction X Y \<acute> q) w"
      have not_Xq: "\<not> pp_t_holds (X \<acute> q) w"
        and not_Yq: "\<not> pp_t_holds (Y \<acute> q) w"
        using pp_t_unary_output_disjunction_apply_holds[
          OF X Y q, of w]
          not_disjunction by blast+
      obtain v where wv: "prefix w v"
        and not_Xr: "\<not> pp_t_holds (X \<acute> r) v"
        and not_Yr: "\<not> pp_t_holds (Y \<acute> r) v"
        using joint q not_Xq not_Yq
        unfolding pp_t_joint_operator_antipatching_def
        by blast
      have disjunction_r:
          "pp_t_holds
            (pp_t_unary_output_disjunction X Y \<acute> r) v"
        using necessary wv by blast
      have "pp_t_holds (X \<acute> r) v
          \<or> pp_t_holds (Y \<acute> r) v"
        using pp_t_unary_output_disjunction_apply_holds[
          OF X Y r, of v]
          disjunction_r by blast
      then show False using not_Xr not_Yr by blast
    qed
  qed
qed

lemma pp_t_complement_pair_joint_antipatching:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_joint_operator_antipatching
      X (pp_t_pointwise_complement X) r w"
proof -
  have no_counterexample:
      "\<not> (\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> \<not> pp_t_holds (X \<acute> q) w
        \<and> \<not> pp_t_holds
          (pp_t_pointwise_complement X \<acute> q) w)"
  proof
    assume
        "\<exists>q.
          Elem q (pp_t_domain Prop)
          \<and> \<not> pp_t_holds (X \<acute> q) w
          \<and> \<not> pp_t_holds
            (pp_t_pointwise_complement X \<acute> q) w"
    then obtain q where q: "Elem q (pp_t_domain Prop)"
      and not_X: "\<not> pp_t_holds (X \<acute> q) w"
      and not_NX:
          "\<not> pp_t_holds
            (pp_t_pointwise_complement X \<acute> q) w"
      by blast
    have NX:
        "pp_t_holds
          (pp_t_pointwise_complement X \<acute> q) w
          \<longleftrightarrow>
         \<not> pp_t_holds (X \<acute> q) w"
      by (rule pp_t_pointwise_complement_holds[OF q])
    show False using not_X not_NX NX by blast
  qed
  show ?thesis
    using no_counterexample
    unfolding pp_t_joint_operator_antipatching_def
    by blast
qed

corollary pp_t_complement_pair_disjunction_recombination_safe:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        X (pp_t_pointwise_complement X)) r w"
proof -
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  show ?thesis
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
      OF X NX r]
      pp_t_complement_pair_joint_antipatching[OF X r]
    by blast
qed

section \<open>A common false guard for the six nonidentity modal sections\<close>

lemma pp_t_dual_negation_guard_full_section_false:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and b: "Elem b (pp_t_domain Prop)"
    and target:
      "pp_t_eqv Prop v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        b"
    and no_fixed:
      "\<And>x. prefix v x \<Longrightarrow>
        \<not> pp_t_eqv Prop x
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) b"
  shows
    "\<not> pp_t_holds
      (pp_t_dual_recurrent_full_section F
        \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
proof -
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  let ?a = "F \<acute> ?Rw"
  let ?B = "pp_t_moving_boundary_operator_probe
    pp_t_probe_modal_boolean_dual_recurrent_seed_at \<acute> F"
  let ?X = "pp_t_recurrent_modal_component F"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have a: "Elem ?a (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F Rw])
  have singleton_b_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at b)"
  proof (rule pp_t_dual_recurrent_singleton_impure_if_unreachable[
      OF b])
    fix x
    assume vx: "prefix v x"
    show "\<not> pp_t_eqv Prop x ?Rv b"
      by (rule no_fixed[OF vx])
  qed
  have families:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at ?a)
        (pp_t_singleton_family_at b)"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF a b, of v]
      target by blast
  have singleton_a_impure:
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
        "Elem (pp_t_singleton_family_at b)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_singleton_family_at_in_domain[OF b])
    have b_pure:
        "pp_t_probe_modal_boolean_stock v
          (pp_t_singleton_family_at b)"
      using pp_t_probe_modal_boolean_stock_admissible
        Sa Sb families a_pure
      unfolding pp_t_predicate_admissible_def
      by blast
    show False using singleton_b_impure b_pure by blast
  qed
  have X: "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_recurrent_modal_component_in_domain[OF F])
  have X_false: "\<not> pp_t_holds (?X \<acute> ?Rw) v"
    using pp_t_modal_singleton_operator_probe_apply_holds[
      OF F Rw, of v]
      singleton_a_impure by blast
  have not_boundary:
      "\<not> pp_t_fundamental_boundary ?Rv v ?a"
  proof
    assume boundary: "pp_t_fundamental_boundary ?Rv v ?a"
    obtain x where vx: "prefix v x"
      and reached: "pp_t_eqv Prop x ?Rv ?a"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have target_x: "pp_t_eqv Prop x ?a b"
      by (rule pp_t_eqv_persistent[OF target vx])
    have fixed: "pp_t_eqv Prop x ?Rv b"
      by (rule pp_t_eqv_transitive[
        OF Rv a b reached target_x])
    show False using no_fixed[OF vx] fixed by blast
  qed
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  have B_false: "\<not> pp_t_holds (?B \<acute> ?Rw) v"
    using pp_t_moving_boundary_operator_probe_apply_holds[
      where R=pp_t_probe_modal_boolean_dual_recurrent_seed_at
        and w=v and F=F and p="?Rw",
      OF Rv F Rw]
      not_boundary by blast
  show ?thesis
    using pp_t_unary_output_disjunction_apply_holds[
      OF X B Rw, of v]
      X_false B_false
    by blast
qed

definition pp_t_nonidentity_positive_modal_normal_form :: "ZF \<Rightarrow> bool"
where
  "pp_t_nonidentity_positive_modal_normal_form F
    \<longleftrightarrow>
    F = pp_t_necessity_operator
    \<or> F = pp_t_possibility_operator
    \<or> F = pp_t_box_diamond_operator
    \<or> F = pp_t_diamond_box_operator
    \<or> F = pp_t_box_diamond_box_operator
    \<or> F = pp_t_diamond_box_diamond_operator"

lemma pp_t_nonidentity_positive_modal_normal_form_in_domain:
  assumes "pp_t_nonidentity_positive_modal_normal_form F"
  shows "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  apply (rule pp_t_positive_modal_normal_form_in_domain)
  using assms
  unfolding pp_t_nonidentity_positive_modal_normal_form_def
    pp_t_positive_modal_normal_form_def
  by blast

theorem pp_t_nonidentity_positive_modal_section_false_at_negation_guard:
  assumes normal: "pp_t_nonidentity_positive_modal_normal_form F"
  shows
    "\<not> pp_t_holds
      (pp_t_dual_recurrent_full_section F
        \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (w @ [True, True])"
proof -
  from normal have cases:
      "F = pp_t_necessity_operator
      \<or> F = pp_t_possibility_operator
      \<or> F = pp_t_box_diamond_operator
      \<or> F = pp_t_diamond_box_operator
      \<or> F = pp_t_box_diamond_box_operator
      \<or> F = pp_t_diamond_box_diamond_operator"
    unfolding pp_t_nonidentity_positive_modal_normal_form_def .
  then show ?thesis
  proof (elim disjE)
    assume F0: "F = pp_t_necessity_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_necessity_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_operators_in_domain(1))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(1)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_necessity_target)
      apply (rule pp_t_no_necessity_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  next
    assume F0: "F = pp_t_possibility_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_possibility_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_operators_in_domain(2))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_operators_in_domain(2)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_possibility_target)
      apply (rule pp_t_no_possibility_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  next
    assume F0: "F = pp_t_box_diamond_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_box_diamond_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_depth_two_operators_in_domain(1))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_depth_two_operators_in_domain(1)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_box_diamond_target)
      apply (rule pp_t_no_box_diamond_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  next
    assume F0: "F = pp_t_diamond_box_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_diamond_box_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_depth_two_operators_in_domain(2))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_depth_two_operators_in_domain(2)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_diamond_box_target)
      apply (rule pp_t_no_diamond_box_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  next
    assume F0: "F = pp_t_box_diamond_box_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_box_diamond_box_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_depth_three_operators_in_domain(1))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_depth_three_operators_in_domain(1)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_box_diamond_box_target)
      apply (rule pp_t_no_box_diamond_box_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  next
    assume F0: "F = pp_t_diamond_box_diamond_operator"
    show ?thesis
      unfolding F0
      apply (rule pp_t_dual_negation_guard_full_section_false[
        where b="pp_t_diamond_box_diamond_operator \<acute>
          pp_t_complement
            (pp_t_probe_modal_boolean_dual_recurrent_seed_at
              (w @ [True, True]))"])
      apply simp
      apply (rule pp_t_modal_depth_three_operators_in_domain(2))
      apply (rule pp_t_app_closed[
        OF pp_t_modal_depth_three_operators_in_domain(2)
          pp_t_complement_in_domain])
      apply (rule pp_t_dual_negation_guard_diamond_box_diamond_target)
      apply (rule pp_t_no_diamond_box_diamond_of_complement_fixed_point[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
      done
  qed
qed

theorem pp_t_nonidentity_positive_modal_sections_joint_antipatching:
  assumes F: "pp_t_nonidentity_positive_modal_normal_form F"
    and G: "pp_t_nonidentity_positive_modal_normal_form G"
  shows
    "pp_t_joint_operator_antipatching
      (pp_t_dual_recurrent_full_section F)
      (pp_t_dual_recurrent_full_section G)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  let ?v = "w @ [True, True]"
  have wv: "prefix w ?v" by simp
  have F_false:
      "\<not> pp_t_holds
        (pp_t_dual_recurrent_full_section F
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) ?v"
    by (rule
      pp_t_nonidentity_positive_modal_section_false_at_negation_guard[
        OF F])
  have G_false:
      "\<not> pp_t_holds
        (pp_t_dual_recurrent_full_section G
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) ?v"
    by (rule
      pp_t_nonidentity_positive_modal_section_false_at_negation_guard[
        OF G])
  show ?thesis
    unfolding pp_t_joint_operator_antipatching_def
    using wv F_false G_false
    by blast
qed

corollary
    pp_t_nonidentity_positive_modal_sections_disjunction_recombination_safe:
  assumes F: "pp_t_nonidentity_positive_modal_normal_form F"
    and G: "pp_t_nonidentity_positive_modal_normal_form G"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_dual_recurrent_full_section F)
        (pp_t_dual_recurrent_full_section G))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have F_domain:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_nonidentity_positive_modal_normal_form_in_domain[OF F]])
  have G_domain:
      "Elem (pp_t_dual_recurrent_full_section G)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_nonidentity_positive_modal_normal_form_in_domain[OF G]])
  show ?thesis
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
      OF F_domain G_domain
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain]
      pp_t_nonidentity_positive_modal_sections_joint_antipatching[
        OF F G]
    by blast
qed

section \<open>A common true cone for all seven positive modal sections\<close>

lemma pp_t_identity_preserves_truth_cones:
  "pp_t_preserves_truth_cones (pp_t_closed_den prop_id)"
  unfolding pp_t_preserves_truth_cones_def
proof (intro allI impI)
  fix p w v
  assume p: "Elem p (pp_t_domain Prop)"
    and true:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds p v"
    and wv: "prefix w v"
  have identity:
      "pp_t_closed_den prop_id \<acute> p = p"
    by (rule pp_t_closed_identity_apply[OF p])
  show "pp_t_holds (pp_t_closed_den prop_id \<acute> p) v"
    using true wv identity by simp
qed

lemma pp_t_box_precompose_preserves_truth_cones:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and preserves: "pp_t_preserves_truth_cones F"
  shows
    "pp_t_preserves_truth_cones
      (pp_t_qd_precompose pp_t_necessity_operator F)"
  unfolding pp_t_preserves_truth_cones_def
proof (intro allI impI)
  fix p w v
  assume p: "Elem p (pp_t_domain Prop)"
    and true:
      "\<forall>u. prefix w u \<longrightarrow> pp_t_holds p u"
    and wv: "prefix w v"
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have F_true:
      "\<forall>u. prefix w u \<longrightarrow> pp_t_holds (F \<acute> p) u"
    using preserves p true
    unfolding pp_t_preserves_truth_cones_def by blast
  have necessary:
      "pp_t_holds (pp_t_necessity_operator \<acute> (F \<acute> p)) v"
    using pp_t_necessity_operator_apply_holds[OF Fp, of v]
      F_true prefix_order.trans[OF wv]
    by blast
  show
      "pp_t_holds
        (pp_t_qd_precompose pp_t_necessity_operator F \<acute> p) v"
    unfolding pp_t_qd_precompose_apply[OF p]
    using necessary .
qed

lemma pp_t_diamond_precompose_preserves_truth_cones:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and preserves: "pp_t_preserves_truth_cones F"
  shows
    "pp_t_preserves_truth_cones
      (pp_t_qd_precompose pp_t_possibility_operator F)"
  unfolding pp_t_preserves_truth_cones_def
proof (intro allI impI)
  fix p w v
  assume p: "Elem p (pp_t_domain Prop)"
    and true:
      "\<forall>u. prefix w u \<longrightarrow> pp_t_holds p u"
    and wv: "prefix w v"
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have F_true: "pp_t_holds (F \<acute> p) v"
    using preserves p true wv
    unfolding pp_t_preserves_truth_cones_def by blast
  have possible:
      "pp_t_holds (pp_t_possibility_operator \<acute> (F \<acute> p)) v"
    using pp_t_possibility_operator_apply_holds[OF Fp, of v]
      F_true
    by auto
  show
      "pp_t_holds
        (pp_t_qd_precompose pp_t_possibility_operator F \<acute> p) v"
    unfolding pp_t_qd_precompose_apply[OF p]
    using possible .
qed

lemma pp_t_positive_modal_word_preserves_truth_cones:
  assumes "pp_t_positive_modal_word F"
  shows "pp_t_preserves_truth_cones F"
  using assms
proof induction
  case identity
  show ?case by (rule pp_t_identity_preserves_truth_cones)
next
  case (box F)
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[
      OF pp_t_positive_modal_word_normalization[OF box.hyps]])
  show ?case
    by (rule pp_t_box_precompose_preserves_truth_cones[
      OF F_domain box.IH])
next
  case (diamond F)
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[
      OF pp_t_positive_modal_word_normalization[OF diamond.hyps]])
  show ?case
    by (rule pp_t_diamond_precompose_preserves_truth_cones[
      OF F_domain diamond.IH])
qed

lemma pp_t_positive_modal_normal_form_is_word:
  assumes normal: "pp_t_positive_modal_normal_form F"
  shows "pp_t_positive_modal_word F"
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
  then show ?thesis
  proof (elim disjE)
    assume F: "F = pp_t_closed_den prop_id"
    show ?thesis unfolding F
      by (rule pp_t_positive_modal_word.identity)
  next
    assume F: "F = pp_t_necessity_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_necessity_operator
            (pp_t_closed_den prop_id))"
      by (rule pp_t_positive_modal_word.box)
        (rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word pp_t_qd_precompose_identity_right[
        OF pp_t_modal_operators_in_domain(1)]
      unfolding F by simp
  next
    assume F: "F = pp_t_possibility_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_possibility_operator
            (pp_t_closed_den prop_id))"
      by (rule pp_t_positive_modal_word.diamond)
        (rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word pp_t_qd_precompose_identity_right[
        OF pp_t_modal_operators_in_domain(2)]
      unfolding F by simp
  next
    assume F: "F = pp_t_box_diamond_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_necessity_operator
            (pp_t_qd_precompose pp_t_possibility_operator
              (pp_t_closed_den prop_id)))"
      by (rule pp_t_positive_modal_word.box,
          rule pp_t_positive_modal_word.diamond,
          rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word
        pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(2)]
        pp_t_box_diamond_operator_precompose
      unfolding F by simp
  next
    assume F: "F = pp_t_diamond_box_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_possibility_operator
            (pp_t_qd_precompose pp_t_necessity_operator
              (pp_t_closed_den prop_id)))"
      by (rule pp_t_positive_modal_word.diamond,
          rule pp_t_positive_modal_word.box,
          rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word
        pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(1)]
        pp_t_diamond_box_operator_precompose
      unfolding F by simp
  next
    assume F: "F = pp_t_box_diamond_box_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_necessity_operator
            (pp_t_qd_precompose pp_t_possibility_operator
              (pp_t_qd_precompose pp_t_necessity_operator
                (pp_t_closed_den prop_id))))"
      by (rule pp_t_positive_modal_word.box,
          rule pp_t_positive_modal_word.diamond,
          rule pp_t_positive_modal_word.box,
          rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word
        pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(1)]
        pp_t_diamond_box_operator_precompose
        pp_t_box_diamond_box_operator_precompose
      unfolding F by simp
  next
    assume F: "F = pp_t_diamond_box_diamond_operator"
    have word:
        "pp_t_positive_modal_word
          (pp_t_qd_precompose pp_t_possibility_operator
            (pp_t_qd_precompose pp_t_necessity_operator
              (pp_t_qd_precompose pp_t_possibility_operator
                (pp_t_closed_den prop_id))))"
      by (rule pp_t_positive_modal_word.diamond,
          rule pp_t_positive_modal_word.box,
          rule pp_t_positive_modal_word.diamond,
          rule pp_t_positive_modal_word.identity)
    show ?thesis
      using word
        pp_t_qd_precompose_identity_right[
          OF pp_t_modal_operators_in_domain(2)]
        pp_t_box_diamond_operator_precompose
        pp_t_diamond_box_diamond_operator_precompose
      unfolding F by simp
  qed
qed

corollary pp_t_positive_modal_normal_form_preserves_truth_cones:
  assumes "pp_t_positive_modal_normal_form F"
  shows "pp_t_preserves_truth_cones F"
  by (rule pp_t_positive_modal_word_preserves_truth_cones[
    OF pp_t_positive_modal_normal_form_is_word[OF assms]])

theorem pp_t_truth_preserving_sections_have_common_true_future:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and F_preserves: "pp_t_preserves_truth_cones F"
    and G_preserves: "pp_t_preserves_truth_cones G"
  shows
    "\<exists>v.
      prefix w v
      \<and> pp_t_holds
        (pp_t_dual_recurrent_full_section F
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v
      \<and> pp_t_holds
        (pp_t_dual_recurrent_full_section G
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
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
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem (?R ?v) (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
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
  have truth_boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth True)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_truth_boundary[
      OF r true_cone false_cone])
  have section_true:
      "\<And>H.
        Elem H (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_preserves_truth_cones H
        \<Longrightarrow>
        pp_t_holds
          (pp_t_dual_recurrent_full_section H \<acute> ?R w) ?v"
  proof -
    fix H
    assume H: "Elem H (pp_t_domain pp_t_one_context_unary_type)"
      and H_preserves: "pp_t_preserves_truth_cones H"
    have H_true:
        "\<forall>z. prefix ?v z \<longrightarrow>
          pp_t_holds (H \<acute> ?R w) z"
      using H_preserves Rw all_true
      unfolding pp_t_preserves_truth_cones_def by blast
    have target:
        "pp_t_eqv Prop ?v (H \<acute> ?R w) (pp_zf_truth True)"
      using H_true unfolding pp_t_prop_eqv_truth_iff .
    have target_domain:
        "Elem (H \<acute> ?R w) (pp_t_domain Prop)"
      by (rule pp_t_app_closed[OF H Rw])
    have target_boundary:
        "pp_t_fundamental_boundary (?R ?v) ?v (H \<acute> ?R w)"
      by (rule
        pp_t_fundamental_boundary_respects_equivalent_parameter[
          OF Rv target_domain truth_boundary target])
    let ?B = "pp_t_moving_boundary_operator_probe ?R \<acute> H"
    let ?X = "pp_t_recurrent_modal_component H"
    have B:
        "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_moving_boundary_operator_probe_in_domain H])
    have X:
        "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_recurrent_modal_component_in_domain[OF H])
    have boundary_true: "pp_t_holds (?B \<acute> ?R w) ?v"
      using pp_t_moving_boundary_operator_probe_apply_holds[
        where R="?R" and w="?v" and F=H and p="?R w",
        OF Rv H Rw]
        target_boundary by blast
    show
        "pp_t_holds
          (pp_t_dual_recurrent_full_section H \<acute> ?R w) ?v"
      using pp_t_unary_output_disjunction_apply_holds[
        OF X B Rw, of ?v]
        boundary_true by blast
  qed
  show ?thesis
    using section_true[OF F F_preserves]
      section_true[OF G G_preserves]
    by (intro exI[of _ ?v]) simp
qed

theorem pp_t_positive_modal_complemented_sections_joint_antipatching:
  assumes F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
  shows
    "pp_t_joint_operator_antipatching
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section G))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF F])
  have G_domain:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF G])
  obtain v where wv: "prefix w v"
    and F_true:
      "pp_t_holds
        (pp_t_dual_recurrent_full_section F
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
    and G_true:
      "pp_t_holds
        (pp_t_dual_recurrent_full_section G
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
    using pp_t_truth_preserving_sections_have_common_true_future[
      OF F_domain G_domain
        pp_t_positive_modal_normal_form_preserves_truth_cones[OF F]
        pp_t_positive_modal_normal_form_preserves_truth_cones[OF G]]
    by blast
  have R:
      "Elem (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have NF_false:
      "\<not> pp_t_holds
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section F)
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
    using pp_t_pointwise_complement_holds[
      OF R, of "pp_t_dual_recurrent_full_section F" v]
      F_true by simp
  have NG_false:
      "\<not> pp_t_holds
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G)
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
    using pp_t_pointwise_complement_holds[
      OF R, of "pp_t_dual_recurrent_full_section G" v]
      G_true by simp
  show ?thesis
    unfolding pp_t_joint_operator_antipatching_def
    using wv NF_false NG_false by blast
qed

corollary
    pp_t_positive_modal_complemented_sections_disjunction_recombination_safe:
  assumes F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section F))
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G)))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have F_section:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_positive_modal_normal_form_in_domain[OF F]])
  have G_section:
      "Elem (pp_t_dual_recurrent_full_section G)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_positive_modal_normal_form_in_domain[OF G]])
  have NF:
      "Elem (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section F))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF F_section])
  have NG:
      "Elem (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section G))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF G_section])
  show ?thesis
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
      OF NF NG pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain]
      pp_t_positive_modal_complemented_sections_joint_antipatching[
        OF F G]
    by blast
qed

section \<open>Mixed signs are exactly distinction transport\<close>

theorem pp_t_dual_recurrent_full_section_holds_iff:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
        (pp_t_dual_recurrent_full_section F \<acute> p) w
      \<longleftrightarrow>
     pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))
      \<or>
     pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        w (F \<acute> p)"
proof -
  let ?X = "pp_t_recurrent_modal_component F"
  let ?B =
    "pp_t_moving_boundary_operator_probe
      pp_t_probe_modal_boolean_dual_recurrent_seed_at \<acute> F"
  have X:
      "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_recurrent_modal_component_in_domain[OF F])
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  have component:
      "pp_t_holds (?X \<acute> p) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))"
    by (rule pp_t_modal_singleton_operator_probe_apply_holds[OF F p])
  have boundary:
      "pp_t_holds (?B \<acute> p) w
        \<longleftrightarrow>
       pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        w (F \<acute> p)"
    by (rule pp_t_moving_boundary_operator_probe_apply_holds[
      where R=pp_t_probe_modal_boolean_dual_recurrent_seed_at,
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain F p])
  show ?thesis
    using pp_t_unary_output_disjunction_apply_holds[
      OF X B p, of w]
      component boundary by blast
qed

definition pp_t_operator_distinction_transport ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_operator_distinction_transport X Y r w
    \<longleftrightarrow>
    ((\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> \<not> pp_t_holds (X \<acute> q) w
        \<and> pp_t_holds (Y \<acute> q) w)
      \<longrightarrow>
     (\<exists>v.
        prefix w v
        \<and> \<not> pp_t_holds (X \<acute> r) v
        \<and> pp_t_holds (Y \<acute> r) v))"

lemma pp_t_mixed_joint_antipatching_iff_distinction_transport:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_joint_operator_antipatching
        X (pp_t_pointwise_complement Y) r w
      \<longleftrightarrow>
     pp_t_operator_distinction_transport X Y r w"
  unfolding pp_t_joint_operator_antipatching_def
    pp_t_operator_distinction_transport_def
  using pp_t_pointwise_complement_holds[OF r]
  by (smt (verit, best)
    pp_t_pointwise_complement_holds)

definition pp_t_modal_section_distinction_transport ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_modal_section_distinction_transport F G r w
    \<longleftrightarrow>
    pp_t_operator_distinction_transport
      (pp_t_dual_recurrent_full_section F)
      (pp_t_dual_recurrent_full_section G)
      r w"

theorem
    pp_t_mixed_positive_modal_sections_recombination_safe_iff_transport:
  assumes F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_dual_recurrent_full_section F)
          (pp_t_pointwise_complement
            (pp_t_dual_recurrent_full_section G)))
        r w
      \<longleftrightarrow>
     pp_t_modal_section_distinction_transport F G r w"
proof -
  have F_section:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_positive_modal_normal_form_in_domain[OF F]])
  have G_section:
      "Elem (pp_t_dual_recurrent_full_section G)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[
      OF pp_t_positive_modal_normal_form_in_domain[OF G]])
  have NG_section:
      "Elem
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF G_section])
  show ?thesis
    unfolding pp_t_modal_section_distinction_transport_def
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
        OF F_section NG_section r]
      pp_t_mixed_joint_antipatching_iff_distinction_transport[OF r,
        of "pp_t_dual_recurrent_full_section F"
           "pp_t_dual_recurrent_full_section G" w]
    by blast
qed

lemma pp_t_reflexive_distinction_transport:
  "pp_t_operator_distinction_transport X X r w"
  unfolding pp_t_operator_distinction_transport_def
  by blast

lemma pp_t_dual_recurrent_full_section_true_if_boundary:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and boundary:
      "pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)
        v (F \<acute> p)"
  shows
    "pp_t_holds
      (pp_t_dual_recurrent_full_section F \<acute> p) v"
proof -
  let ?B =
    "pp_t_moving_boundary_operator_probe
      pp_t_probe_modal_boolean_dual_recurrent_seed_at \<acute> F"
  let ?X = "pp_t_recurrent_modal_component F"
  have X:
      "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_recurrent_modal_component_in_domain[OF F])
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  have boundary_true: "pp_t_holds (?B \<acute> p) v"
    using pp_t_moving_boundary_operator_probe_apply_holds[
      where R=pp_t_probe_modal_boolean_dual_recurrent_seed_at
        and w=v and F=F and p=p,
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain F p]
      boundary by blast
  show ?thesis
    using pp_t_unary_output_disjunction_apply_holds[
      OF X B p, of v]
      boundary_true by blast
qed

definition pp_t_modal_section_pair_guard ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_modal_section_pair_guard F G r w
    \<longleftrightarrow>
    (\<exists>v.
      prefix w v
      \<and> \<not> pp_t_holds
        (pp_t_dual_recurrent_full_section F \<acute> r) v
      \<and> pp_t_holds
        (pp_t_dual_recurrent_full_section G \<acute> r) v)"

lemma pp_t_modal_section_pair_guard_if_pure_impure_boundary_pattern:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and F_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (F \<acute> r))"
    and F_not_boundary:
      "\<not> pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)
        v (F \<acute> r)"
    and G_pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (G \<acute> r))"
  shows "pp_t_modal_section_pair_guard F G r w"
proof -
  have F_false:
      "\<not> pp_t_holds
        (pp_t_dual_recurrent_full_section F \<acute> r) v"
    using pp_t_dual_recurrent_full_section_holds_iff[OF F r, of v]
      F_impure F_not_boundary by blast
  have G_true:
      "pp_t_holds
        (pp_t_dual_recurrent_full_section G \<acute> r) v"
    using pp_t_dual_recurrent_full_section_holds_iff[OF G r, of v]
      G_pure by blast
  show ?thesis
    unfolding pp_t_modal_section_pair_guard_def
    using wv F_false G_true by blast
qed

lemma pp_t_dual_recurrent_fundamental_singleton_impure:
  "\<not> pp_t_probe_modal_boolean_stock v
    (pp_t_singleton_family_at
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at v))"
proof
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  assume pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at ?Rv)"
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have not_reflexive: "\<not> pp_t_eqv Prop v ?Rv ?Rv"
    by (rule
      pp_t_pure_singleton_parameter_not_currently_fundamental[
        where Pure=pp_t_probe_modal_boolean_stock,
        OF Rv Rv pure
          pp_t_probe_modal_boolean_dual_recurrent_seed_recombines])
  show False
    using not_reflexive pp_t_eqv_reflexive[OF Rv, of v]
    by blast
qed

theorem pp_t_modal_section_pair_guard_if_fixed_and_constant:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and fixed:
      "pp_t_eqv Prop v (F \<acute> r)
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)"
    and G_constant:
      "pp_t_eqv Prop v (G \<acute> r) (pp_zf_truth b)"
  shows "pp_t_modal_section_pair_guard F G r w"
proof -
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  let ?Fr = "F \<acute> r"
  let ?Gr = "G \<acute> r"
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Fr: "Elem ?Fr (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F r])
  have Gr: "Elem ?Gr (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF G r])
  have truth: "Elem (pp_zf_truth b) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have SFr:
      "Elem (pp_t_singleton_family_at ?Fr)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF Fr])
  have SRv:
      "Elem (pp_t_singleton_family_at ?Rv)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF Rv])
  have F_families:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at ?Fr)
        (pp_t_singleton_family_at ?Rv)"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF Fr Rv, of v]
      fixed by blast
  have F_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at ?Fr)"
  proof
    assume F_pure:
        "pp_t_probe_modal_boolean_stock v
          (pp_t_singleton_family_at ?Fr)"
    have Rv_pure:
        "pp_t_probe_modal_boolean_stock v
          (pp_t_singleton_family_at ?Rv)"
      using pp_t_probe_modal_boolean_stock_admissible
        SFr SRv F_families F_pure
      unfolding pp_t_predicate_admissible_def
      by blast
    show False
      using pp_t_dual_recurrent_fundamental_singleton_impure[of v]
        Rv_pure by blast
  qed
  have fixed_reverse: "pp_t_eqv Prop v ?Rv ?Fr"
    by (rule pp_t_eqv_symmetric[OF Fr Rv fixed])
  have F_not_boundary:
      "\<not> pp_t_fundamental_boundary ?Rv v ?Fr"
    using fixed_reverse
    unfolding pp_t_fundamental_boundary_def
    by blast
  have SGr:
      "Elem (pp_t_singleton_family_at ?Gr)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF Gr])
  have ST:
      "Elem (pp_t_singleton_family_at (pp_zf_truth b))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF truth])
  have G_families:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at ?Gr)
        (pp_t_singleton_family_at (pp_zf_truth b))"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF Gr truth, of v]
      G_constant by blast
  have truth_pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (pp_zf_truth b))"
    by (rule pp_t_modal_stock_contains_truth_singleton)
  have G_pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at ?Gr)"
  proof -
    have reverse:
      "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_singleton_family_at (pp_zf_truth b))
          (pp_t_singleton_family_at ?Gr)"
      by (rule pp_t_eqv_symmetric[OF SGr ST G_families])
    show ?thesis
      using pp_t_probe_modal_boolean_stock_admissible
        ST SGr reverse truth_pure
      unfolding pp_t_predicate_admissible_def
      by blast
  qed
  show ?thesis
    by (rule pp_t_modal_section_pair_guard_if_pure_impure_boundary_pattern[
      OF wv F G r F_impure F_not_boundary G_pure])
qed

lemma pp_t_modal_stock_contains_singleton_if_constant:
  assumes p: "Elem p (pp_t_domain Prop)"
    and p_constant:
      "pp_t_eqv Prop v p (pp_zf_truth b)"
  shows
    "pp_t_probe_modal_boolean_stock v
      (pp_t_singleton_family_at p)"
proof -
  have truth: "Elem (pp_zf_truth b) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have Sp:
      "Elem (pp_t_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  have ST:
      "Elem (pp_t_singleton_family_at (pp_zf_truth b))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF truth])
  have families:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at (pp_zf_truth b))"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF p truth, of v]
      p_constant by blast
  have truth_pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (pp_zf_truth b))"
    by (rule pp_t_modal_stock_contains_truth_singleton)
  have reverse:
      "pp_t_eqv pp_t_one_context_unary_type v
        (pp_t_singleton_family_at (pp_zf_truth b))
        (pp_t_singleton_family_at p)"
    by (rule pp_t_eqv_symmetric[OF Sp ST families])
  show ?thesis
    using pp_t_probe_modal_boolean_stock_admissible
      ST Sp reverse truth_pure
    unfolding pp_t_predicate_admissible_def
    by blast
qed

theorem pp_t_modal_section_pair_guard_if_unreachable_and_constant:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and b_domain: "Elem b (pp_t_domain Prop)"
    and F_target:
      "pp_t_eqv Prop v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) b"
    and unreachable:
      "\<And>x. prefix v x \<Longrightarrow>
        \<not> pp_t_eqv Prop x
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) b"
    and G_constant:
      "pp_t_eqv Prop v
        (G \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        (pp_zf_truth c)"
  shows
    "pp_t_modal_section_pair_guard F G
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have F_false:
      "\<not> pp_t_holds
        (pp_t_dual_recurrent_full_section F \<acute> ?r) v"
    by (rule pp_t_dual_negation_guard_full_section_false[
      OF wv F b_domain F_target unreachable])
  have Gr: "Elem (G \<acute> ?r) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF G r])
  have G_pure:
      "pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (G \<acute> ?r))"
    by (rule pp_t_modal_stock_contains_singleton_if_constant[
      OF Gr G_constant])
  have G_true:
      "pp_t_holds
        (pp_t_dual_recurrent_full_section G \<acute> ?r) v"
    using pp_t_dual_recurrent_full_section_holds_iff[OF G r, of v]
      G_pure by blast
  show ?thesis
    unfolding pp_t_modal_section_pair_guard_def
    using wv F_false G_true by blast
qed

corollary
    pp_t_mixed_positive_modal_sections_safe_if_unreachable_and_constant:
  assumes F_normal: "pp_t_positive_modal_normal_form F"
    and G_normal: "pp_t_positive_modal_normal_form G"
    and wv: "prefix w v"
    and b_domain: "Elem b (pp_t_domain Prop)"
    and F_target:
      "pp_t_eqv Prop v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) b"
    and unreachable:
      "\<And>x. prefix v x \<Longrightarrow>
        \<not> pp_t_eqv Prop x
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) b"
    and G_constant:
      "pp_t_eqv Prop v
        (G \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        (pp_zf_truth c)"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_dual_recurrent_full_section F)
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G)))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF F_normal])
  have G:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF G_normal])
  have guard:
      "pp_t_modal_section_pair_guard F G
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_modal_section_pair_guard_if_unreachable_and_constant[
      OF wv F G b_domain F_target unreachable G_constant])
  have transport:
      "pp_t_modal_section_distinction_transport F G
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    using guard
    unfolding pp_t_modal_section_pair_guard_def
      pp_t_modal_section_distinction_transport_def
      pp_t_operator_distinction_transport_def
    by blast
  show ?thesis
    using
      pp_t_mixed_positive_modal_sections_recombination_safe_iff_transport[
        OF F_normal G_normal
          pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain]
      transport by blast
qed

lemma pp_t_dual_negation_boundary_at_guard:
  "pp_t_fundamental_boundary
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at
      (w @ [True, True]))
    (w @ [True, True])
    (pp_t_complement
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w))"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?R = "pp_t_probe_modal_boolean_dual_recurrent_seed_at"
  let ?v = "w @ [True, True]"
  let ?u = "?v @ [True]"
  have root: "pp_t_holds ?r []"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have negation:
      "\<And>x.
        pp_t_holds ?r ([True, True] @ x)
          \<longleftrightarrow>
        (if x = [] then True else \<not> pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have complement_domain:
      "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have not_equivalent:
      "\<not> pp_t_eqv Prop ?v (?R ?v) (pp_t_complement (?R w))"
  proof
    assume equivalent:
        "pp_t_eqv Prop ?v (?R ?v) (pp_t_complement (?R w))"
    have at_v:
        "pp_t_holds (?R ?v) ?v
          \<longleftrightarrow>
         pp_t_holds (pp_t_complement (?R w)) ?v"
      by (rule pp_t_prop_eqv_at[OF equivalent], simp)
    show False
      using at_v root negation[of "[]"]
      unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
  qed
  have recovered:
      "pp_t_eqv Prop ?u (?R ?v) (pp_t_complement (?R w))"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume uz: "prefix ?u z"
    obtain t where z: "z = ?u @ t"
      using uz unfolding prefix_def by blast
    show "pp_t_holds (?R ?v) z
        =
      pp_t_holds (pp_t_complement (?R w)) z"
      using negation[of "[True] @ t"]
      unfolding z
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show
        "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
      by (rule complement_domain)
    show
        "\<not> pp_t_eqv Prop ?v
          (?R ?v) (pp_t_complement (?R w))"
      by (rule not_equivalent)
    show
        "\<exists>x. prefix ?v x
          \<and> pp_t_eqv Prop x
            (?R ?v) (pp_t_complement (?R w))"
      by (intro exI[of _ ?u]) (use recovered in simp)
  qed
qed

lemma pp_t_dual_negation_section_true_at_guard:
  "pp_t_holds
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_negation_operator)
      \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
    (w @ [True, True])"
proof -
  have Rw:
      "Elem (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have negation:
      "Elem (pp_t_closed_den pp_negation_operator)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed])
  have boundary:
      "pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, True]))
        (w @ [True, True])
        (pp_t_closed_den pp_negation_operator
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)"
    unfolding pp_t_closed_negation_apply[OF Rw]
    by (rule pp_t_dual_negation_boundary_at_guard)
  show ?thesis
    by (rule pp_t_dual_recurrent_full_section_true_if_boundary[
      OF negation Rw boundary])
qed

theorem pp_t_nonidentity_positive_modal_to_negation_pair_guard:
  assumes F: "pp_t_nonidentity_positive_modal_normal_form F"
  shows
    "pp_t_modal_section_pair_guard F
      (pp_t_closed_den pp_negation_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  let ?v = "w @ [True, True]"
  have wv: "prefix w ?v" by simp
  have F_false:
      "\<not> pp_t_holds
        (pp_t_dual_recurrent_full_section F
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) ?v"
    by (rule
      pp_t_nonidentity_positive_modal_section_false_at_negation_guard[
        OF F])
  have negation_true:
      "pp_t_holds
        (pp_t_dual_recurrent_full_section
          (pp_t_closed_den pp_negation_operator)
          \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) ?v"
    by (rule pp_t_dual_negation_section_true_at_guard)
  show ?thesis
    unfolding pp_t_modal_section_pair_guard_def
    using wv F_false negation_true by blast
qed

lemma pp_t_modal_section_pair_guard_imp_distinction_transport:
  assumes guard: "pp_t_modal_section_pair_guard F G r w"
  shows "pp_t_modal_section_distinction_transport F G r w"
  using guard
  unfolding pp_t_modal_section_pair_guard_def
    pp_t_modal_section_distinction_transport_def
    pp_t_operator_distinction_transport_def
  by blast

theorem pp_t_mixed_generated_sections_recombination_safe_iff_transport:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_dual_recurrent_full_section F)
          (pp_t_pointwise_complement
            (pp_t_dual_recurrent_full_section G)))
        r w
      \<longleftrightarrow>
     pp_t_modal_section_distinction_transport F G r w"
proof -
  have SF:
      "Elem (pp_t_dual_recurrent_full_section F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[OF F])
  have SG:
      "Elem (pp_t_dual_recurrent_full_section G)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_dual_recurrent_full_section_in_domain[OF G])
  have NSG:
      "Elem
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF SG])
  show ?thesis
    unfolding pp_t_modal_section_distinction_transport_def
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
        OF SF NSG r]
      pp_t_mixed_joint_antipatching_iff_distinction_transport[
        OF r,
        of "pp_t_dual_recurrent_full_section F"
           "pp_t_dual_recurrent_full_section G" w]
    by blast
qed

corollary
    pp_t_nonidentity_positive_modal_to_negation_mixed_disjunction_safe:
  assumes F: "pp_t_nonidentity_positive_modal_normal_form F"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_dual_recurrent_full_section F)
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section
            (pp_t_closed_den pp_negation_operator))))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_nonidentity_positive_modal_normal_form_in_domain[OF F])
  have negation:
      "Elem (pp_t_closed_den pp_negation_operator)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed])
  have guard:
      "pp_t_modal_section_pair_guard F
        (pp_t_closed_den pp_negation_operator)
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_nonidentity_positive_modal_to_negation_pair_guard[OF F])
  have transport:
      "pp_t_modal_section_distinction_transport F
        (pp_t_closed_den pp_negation_operator)
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_modal_section_pair_guard_imp_distinction_transport[OF guard])
  show ?thesis
    using
      pp_t_mixed_generated_sections_recombination_safe_iff_transport[
        OF F_domain negation
          pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain]
      transport by blast
qed

corollary
    pp_t_mixed_positive_modal_sections_recombination_safe_if_pair_guard:
  assumes F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
    and r: "Elem r (pp_t_domain Prop)"
    and guard: "pp_t_modal_section_pair_guard F G r w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_dual_recurrent_full_section F)
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section G)))
      r w"
  using
    pp_t_mixed_positive_modal_sections_recombination_safe_iff_transport[
      OF F G r]
    pp_t_modal_section_pair_guard_imp_distinction_transport[OF guard]
  by blast

corollary pp_t_same_modal_section_mixed_disjunction_recombination_safe:
  assumes F: "pp_t_positive_modal_normal_form F"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_dual_recurrent_full_section F)
        (pp_t_pointwise_complement
          (pp_t_dual_recurrent_full_section F)))
      r w"
  using
    pp_t_mixed_positive_modal_sections_recombination_safe_iff_transport[
      OF F F r]
    pp_t_reflexive_distinction_transport[
      of "pp_t_dual_recurrent_full_section F" r w]
  unfolding pp_t_modal_section_distinction_transport_def
  by blast

end
