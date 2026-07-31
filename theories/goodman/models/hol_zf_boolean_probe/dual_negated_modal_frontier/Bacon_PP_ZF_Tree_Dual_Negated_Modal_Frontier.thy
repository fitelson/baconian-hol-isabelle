theory Bacon_PP_ZF_Tree_Dual_Negated_Modal_Frontier
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Modal_Stock.Bacon_PP_ZF_Tree_Dual_Modal_Stock
begin

section \<open>The two negated modal indices\<close>

definition pp_t_necessary_falsity_unary :: oterm where
  "pp_t_necessary_falsity_unary =
    Lam Prop (\<box>\<^sub>o (Neg (Var 0)))"

definition pp_t_possible_falsity_unary :: oterm where
  "pp_t_possible_falsity_unary =
    Lam Prop (\<diamond>\<^sub>o (Neg (Var 0)))"

abbreviation pp_t_necessary_falsity_operator :: ZF where
  "pp_t_necessary_falsity_operator \<equiv>
    pp_t_closed_den pp_t_necessary_falsity_unary"

abbreviation pp_t_possible_falsity_operator :: ZF where
  "pp_t_possible_falsity_operator \<equiv>
    pp_t_closed_den pp_t_possible_falsity_unary"

lemma pp_t_negated_modal_terms_typed:
  "[] \<turnstile> pp_t_necessary_falsity_unary :
    pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_possible_falsity_unary :
    pp_t_one_context_unary_type"
  by (rule infer_type_sound;
      simp add: pp_t_necessary_falsity_unary_def
        pp_t_possible_falsity_unary_def
        ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)+

lemma pp_t_negated_modal_terms_logical:
  "pp_logical_vocabulary pp_t_necessary_falsity_unary"
  "pp_logical_vocabulary pp_t_possible_falsity_unary"
  by (simp_all add: pp_t_necessary_falsity_unary_def
      pp_t_possible_falsity_unary_def
      pp_logical_vocabulary_def
      ObjDiamond_def ObjBox_def ObjTrue_def)

lemma pp_t_negated_modal_operators_in_domain:
  "Elem pp_t_necessary_falsity_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  "Elem pp_t_possible_falsity_operator
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_closed_den_in_domain,
      rule pp_t_negated_modal_terms_typed)+

lemma pp_t_necessary_falsity_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_necessary_falsity_operator \<acute> p
      =
     pp_t_necessity_operator \<acute> pp_t_complement p"
proof (rule pp_t_prop_ext)
  have cp: "Elem (pp_t_complement p) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  show "Elem (pp_t_necessary_falsity_operator \<acute> p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negated_modal_operators_in_domain(1) p])
  show "Elem (pp_t_necessity_operator \<acute> pp_t_complement p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(1)
        cp])
  fix w
  have left:
      "pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) w
        \<longleftrightarrow>
       (\<forall>v. prefix w v \<longrightarrow> \<not> pp_t_holds p v)"
    unfolding pp_t_closed_den_def
      pp_t_necessary_falsity_unary_def
    using p
    by (simp add: Lambda_app pp_t_eval_ObjBox_holds)
  have right:
      "pp_t_holds
          (pp_t_necessity_operator \<acute> pp_t_complement p) w
        \<longleftrightarrow>
       (\<forall>v. prefix w v \<longrightarrow> \<not> pp_t_holds p v)"
    using pp_t_necessity_operator_apply_holds[
      OF cp, of w]
    by simp
  show "pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) w
      =
    pp_t_holds
      (pp_t_necessity_operator \<acute> pp_t_complement p) w"
    using left right by blast
qed

lemma pp_t_possible_falsity_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_possible_falsity_operator \<acute> p
      =
     pp_t_possibility_operator \<acute> pp_t_complement p"
proof (rule pp_t_prop_ext)
  have cp: "Elem (pp_t_complement p) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  show "Elem (pp_t_possible_falsity_operator \<acute> p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negated_modal_operators_in_domain(2) p])
  show "Elem (pp_t_possibility_operator \<acute> pp_t_complement p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_operators_in_domain(2)
        cp])
  fix w
  have left:
      "pp_t_holds (pp_t_possible_falsity_operator \<acute> p) w
        \<longleftrightarrow>
       (\<exists>v. prefix w v \<and> \<not> pp_t_holds p v)"
    unfolding pp_t_closed_den_def
      pp_t_possible_falsity_unary_def
    using p
    by (simp add: Lambda_app pp_t_eval_ObjDiamond_holds)
  have right:
      "pp_t_holds
          (pp_t_possibility_operator \<acute> pp_t_complement p) w
        \<longleftrightarrow>
       (\<exists>v. prefix w v \<and> \<not> pp_t_holds p v)"
    using pp_t_possibility_operator_apply_holds[
      OF cp, of w]
    by simp
  show "pp_t_holds (pp_t_possible_falsity_operator \<acute> p) w
      =
    pp_t_holds
      (pp_t_possibility_operator \<acute> pp_t_complement p) w"
    using left right by blast
qed

section \<open>The guarded identity cone\<close>

lemma pp_t_dual_identity_guard_strict_identity:
  fixes w :: "bool list"
  assumes nonempty: "u \<noteq> []"
  defines "v \<equiv> w @ [True, False]"
  shows
    "pp_t_eqv Prop (v @ u)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at v)"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  have guarded:
      "\<forall>x.
        pp_t_holds ?r ([True, False] @ x)
          \<longleftrightarrow>
        (if x = [] then False else pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix (v @ u) z"
    obtain t where z: "z = (v @ u) @ t"
      using future unfolding prefix_def by blast
    have ut: "u @ t \<noteq> []"
      using nonempty by auto
    show
      "pp_t_holds
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) z
        =
       pp_t_holds
          (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) z"
      using guarded[rule_format, of "u @ t"] ut nonempty
      unfolding z v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc nonempty)
  qed
qed

lemma pp_t_dual_identity_guard_necessary_falsity_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, False]"
  shows
    "pp_t_eqv Prop v
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at v)"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRw: "Elem (pp_t_complement ?Rw) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have root: "pp_t_holds ?r []"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have id_guard:
      "\<forall>x.
        pp_t_holds ?r ([True, False] @ x)
          \<longleftrightarrow>
        (if x = [] then False else pp_t_holds ?r x)"
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
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?Rw) v"
  proof -
    have Rw_true:
        "pp_t_holds ?Rw (v @ [True, True])"
      using id_guard[rule_format, of "[True, True]"] root_TT
      unfolding v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
    have not_all:
        "\<not> (\<forall>z. prefix v z
          \<longrightarrow> pp_t_holds (pp_t_complement ?Rw) z)"
    proof
      assume all:
          "\<forall>z. prefix v z
            \<longrightarrow> pp_t_holds (pp_t_complement ?Rw) z"
      have complement_true:
          "pp_t_holds (pp_t_complement ?Rw)
            (v @ [True, True])"
        using all by simp
      show False using Rw_true complement_true by simp
    qed
    show ?thesis
      unfolding pp_t_necessary_falsity_operator_apply[OF Rw]
      using pp_t_necessity_operator_apply_holds[
        OF cRw, of v]
        not_all by blast
  qed
  have right_false:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?Rv) v"
  proof -
    have not_current:
        "\<not> pp_t_holds (pp_t_complement ?Rv) v"
      using root
      unfolding
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      unfolding pp_t_necessary_falsity_operator_apply[OF Rv]
      using pp_t_necessity_operator_apply_holds[
        OF cRv, of v]
        not_current by auto
  qed
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume vz: "prefix v z"
    obtain u where z: "z = v @ u"
      using vz unfolding prefix_def by blast
    show "pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?Rw) z
      =
      pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?Rv) z"
    proof (cases "u = []")
      case True
      show ?thesis
        using left_false right_false unfolding z True by simp
    next
      case False
      have args: "pp_t_eqv Prop z ?Rw ?Rv"
        using pp_t_dual_identity_guard_strict_identity[
          OF False, where w=w]
        unfolding z v_def .
      have apps:
          "pp_t_eqv Prop z
            (pp_t_necessary_falsity_operator \<acute> ?Rw)
            (pp_t_necessary_falsity_operator \<acute> ?Rv)"
        by (rule pp_t_app_respects[
          OF pp_t_eqv_reflexive[
            OF pp_t_negated_modal_operators_in_domain(1)]
            Rw Rv args])
      show ?thesis
        by (rule pp_t_prop_eqv_at[OF apps], simp)
    qed
  qed
qed

lemma pp_t_dual_identity_guard_possible_falsity_target:
  fixes w :: "bool list"
  defines "v \<equiv> w @ [True, False]"
  shows
    "pp_t_eqv Prop v
      (pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at v)"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  let ?Rw = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?Rv = "pp_t_probe_modal_boolean_dual_recurrent_seed_at v"
  have Rw: "Elem ?Rw (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have Rv: "Elem ?Rv (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRw: "Elem (pp_t_complement ?Rw) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have cRv: "Elem (pp_t_complement ?Rv) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have id_guard:
      "\<forall>x.
        pp_t_holds ?r ([True, False] @ x)
          \<longleftrightarrow>
        (if x = [] then False else pp_t_holds ?r x)"
    using pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded
    unfolding pp_t_dual_guarded_cones_def by blast
  have left_true:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?Rw) v"
  proof -
    have not_Rw: "\<not> pp_t_holds ?Rw v"
      using id_guard[rule_format, of "[]"]
      unfolding v_def
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      unfolding pp_t_possible_falsity_operator_apply[OF Rw]
      using pp_t_possibility_operator_apply_holds[
        OF cRw, of v]
        not_Rw by auto
  qed
  have right_true:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?Rv) v"
  proof -
    obtain f where false_cone:
        "pp_t_eqv Prop f ?r (pp_zf_truth False)"
      using pp_t_dual_recurrent_root_seed_has_false_cone by blast
    have not_Rv: "\<not> pp_t_holds ?Rv (v @ f)"
      using pp_t_prop_eqv_at[OF false_cone, of f]
      unfolding
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds)
    show ?thesis
      unfolding pp_t_possible_falsity_operator_apply[OF Rv]
      using pp_t_possibility_operator_apply_holds[
        OF cRv, of v]
        not_Rv by auto
  qed
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume vz: "prefix v z"
    obtain u where z: "z = v @ u"
      using vz unfolding prefix_def by blast
    show "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?Rw) z
      =
      pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?Rv) z"
    proof (cases "u = []")
      case True
      show ?thesis
        using left_true right_true unfolding z True by simp
    next
      case False
      have args: "pp_t_eqv Prop z ?Rw ?Rv"
        using pp_t_dual_identity_guard_strict_identity[
          OF False, where w=w]
        unfolding z v_def .
      have apps:
          "pp_t_eqv Prop z
            (pp_t_possible_falsity_operator \<acute> ?Rw)
            (pp_t_possible_falsity_operator \<acute> ?Rv)"
        by (rule pp_t_app_respects[
          OF pp_t_eqv_reflexive[
            OF pp_t_negated_modal_operators_in_domain(2)]
            Rw Rv args])
      show ?thesis
        by (rule pp_t_prop_eqv_at[OF apps], simp)
    qed
  qed
qed

section \<open>Anti-patching for the negated modal indices\<close>

theorem pp_t_dual_recurrent_necessary_falsity_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_necessary_falsity_operator
    (pp_t_recurrent_modal_component
      pp_t_necessary_falsity_operator) w"
proof (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, False]"
      and b="pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False])"])
  show "prefix w (w @ [True, False])" by simp
  show "Elem pp_t_necessary_falsity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_negated_modal_operators_in_domain(1))
  show "Elem
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False]))
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negated_modal_operators_in_domain(1)
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  show "pp_t_eqv Prop (w @ [True, False])
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False]))"
    by (rule pp_t_dual_identity_guard_necessary_falsity_target)
  fix x
  let ?r =
    "pp_t_probe_modal_boolean_dual_recurrent_seed_at
      (w @ [True, False])"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  show "\<not> pp_t_eqv Prop x ?r
      (pp_t_necessary_falsity_operator \<acute> ?r)"
    unfolding pp_t_necessary_falsity_operator_apply[OF r]
    by (rule pp_t_no_necessity_of_complement_fixed_point[OF r])
qed

theorem pp_t_dual_recurrent_possible_falsity_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_possible_falsity_operator
    (pp_t_recurrent_modal_component
      pp_t_possible_falsity_operator) w"
proof (rule pp_t_dual_negation_guard_modal_antipatching[
    where v="w @ [True, False]"
      and b="pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False])"])
  show "prefix w (w @ [True, False])" by simp
  show "Elem pp_t_possible_falsity_operator
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_negated_modal_operators_in_domain(2))
  show "Elem
      (pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False]))
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negated_modal_operators_in_domain(2)
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  show "pp_t_eqv Prop (w @ [True, False])
      (pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
      (pp_t_possible_falsity_operator \<acute>
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
          (w @ [True, False]))"
    by (rule pp_t_dual_identity_guard_possible_falsity_target)
  fix x
  let ?r =
    "pp_t_probe_modal_boolean_dual_recurrent_seed_at
      (w @ [True, False])"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  show "\<not> pp_t_eqv Prop x ?r
      (pp_t_possible_falsity_operator \<acute> ?r)"
    unfolding pp_t_possible_falsity_operator_apply[OF r]
    by (rule pp_t_no_possibility_of_complement_fixed_point[OF r])
qed

lemma pp_t_dual_operator_recurrence_from_boundary:
  assumes wv: "prefix w v"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and boundary:
      "pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) v b"
    and b: "Elem b (pp_t_domain Prop)"
    and target:
      "pp_t_eqv Prop v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) b"
  shows
    "pp_t_operator_boundary_recurrence
      pp_t_probe_modal_boolean_dual_recurrent_seed_at F w"
proof -
  have target_domain:
      "Elem
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF F pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain])
  have target_boundary:
      "pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) v
        (F \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w)"
    by (rule
      pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          target_domain boundary target])
  show ?thesis
    unfolding pp_t_operator_boundary_recurrence_def
    using wv target_boundary by blast
qed

theorem pp_t_dual_recurrent_necessary_falsity_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_necessary_falsity_operator w"
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
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have cRw: "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have all_false:
      "\<forall>z. prefix ?v z \<longrightarrow> \<not> pp_t_holds (?R w) z"
  proof (intro allI impI)
    fix z
    assume future: "prefix ?v z"
    obtain u where z: "z = (w @ f) @ u"
      using future unfolding prefix_def by blast
    have root_false: "\<not> pp_t_holds ?r (f @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF false_cone, of "f @ u"],
        of "f @ u"]
      by simp
    show "\<not> pp_t_holds (?R w) z"
      using root_false
      unfolding z pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_necessary_falsity_operator \<acute> ?R w)
        (pp_zf_truth True)"
  proof -
    have necessary:
        "\<forall>z. prefix ?v z \<longrightarrow>
          pp_t_holds (pp_t_necessary_falsity_operator \<acute> ?R w) z"
    proof (intro allI impI)
      fix z
      assume vz: "prefix ?v z"
      have complement_after:
          "\<forall>u. prefix z u
            \<longrightarrow> pp_t_holds (pp_t_complement (?R w)) u"
        using all_false prefix_order.trans[OF vz] by auto
      show "pp_t_holds
          (pp_t_necessary_falsity_operator \<acute> ?R w) z"
        unfolding pp_t_necessary_falsity_operator_apply[OF Rw]
        using pp_t_necessity_operator_apply_holds[
          OF cRw, of z]
          complement_after by blast
    qed
    show ?thesis
      using necessary unfolding pp_t_prop_eqv_truth_iff .
  qed
  have boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth True)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_truth_boundary[
      OF r true_cone false_cone])
  show ?thesis
    by (rule pp_t_dual_operator_recurrence_from_boundary[
      OF _ pp_t_negated_modal_operators_in_domain(1)
        boundary pp_t_truth_in_domain target])
      simp
qed

theorem pp_t_dual_recurrent_possible_falsity_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    pp_t_possible_falsity_operator w"
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
  have cRw: "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have all_true:
      "\<forall>z. prefix ?v z \<longrightarrow> pp_t_holds (?R w) z"
  proof (intro allI impI)
    fix z
    assume future: "prefix ?v z"
    obtain u where z: "z = (w @ t) @ u"
      using future unfolding prefix_def by blast
    have root_true: "pp_t_holds ?r (t @ u)"
      using pp_t_prop_eqv_at[
        OF pp_t_eqv_persistent[OF true_cone, of "t @ u"],
        of "t @ u"]
      by simp
    show "pp_t_holds (?R w) z"
      using root_true
      unfolding z pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
  have target:
      "pp_t_eqv Prop ?v
        (pp_t_possible_falsity_operator \<acute> ?R w)
        (pp_zf_truth False)"
  proof -
    have impossible:
        "\<forall>z. prefix ?v z \<longrightarrow>
          \<not> pp_t_holds (pp_t_possible_falsity_operator \<acute> ?R w) z"
    proof (intro allI impI)
      fix z
      assume vz: "prefix ?v z"
      show "\<not> pp_t_holds
          (pp_t_possible_falsity_operator \<acute> ?R w) z"
      proof
        assume possible:
            "pp_t_holds
              (pp_t_possible_falsity_operator \<acute> ?R w) z"
        have possible_complement:
            "pp_t_holds
              (pp_t_possibility_operator \<acute>
                pp_t_complement (?R w)) z"
          using possible
          unfolding pp_t_possible_falsity_operator_apply[OF Rw] .
        obtain u where zu: "prefix z u"
          and complement_true:
            "pp_t_holds (pp_t_complement (?R w)) u"
          using pp_t_possibility_operator_apply_holds[
            OF cRw, of z]
            possible_complement by blast
        have vu: "prefix ?v u"
          by (rule prefix_order.trans[OF vz zu])
        show False using all_true[rule_format, OF vu]
          complement_true by simp
      qed
    qed
    show ?thesis
      unfolding pp_t_eqv.simps using impossible by simp
  qed
  have boundary:
      "pp_t_fundamental_boundary (?R ?v) ?v (pp_zf_truth False)"
    unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
    by (rule pp_t_reset_seed_on_falsity_boundary[
      OF r true_cone false_cone])
  show ?thesis
    by (rule pp_t_dual_operator_recurrence_from_boundary[
      OF _ pp_t_negated_modal_operators_in_domain(2)
        boundary pp_t_truth_in_domain target])
      simp
qed

corollary pp_t_dual_negated_modal_positive_sections_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section
      pp_t_necessary_falsity_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section
      pp_t_possible_falsity_operator)
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section
        pp_t_necessary_falsity_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_negated_modal_operators_in_domain(1)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_negated_modal_operators_in_domain(1)]
        pp_t_dual_recurrent_necessary_falsity_antipatching])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section
        pp_t_possible_falsity_operator)
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_negated_modal_operators_in_domain(2)
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_negated_modal_operators_in_domain(2)]
        pp_t_dual_recurrent_possible_falsity_antipatching])
qed

corollary pp_t_dual_negated_modal_complemented_sections_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        pp_t_necessary_falsity_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        pp_t_possible_falsity_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          pp_t_necessary_falsity_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_negated_modal_operators_in_domain(1)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_negated_modal_operators_in_domain(1)]
          pp_t_dual_recurrent_necessary_falsity_recurrence])
  show "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_dual_recurrent_full_section
          pp_t_possible_falsity_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
          pp_t_negated_modal_operators_in_domain(2)
          pp_t_recurrent_modal_component_in_domain[
            OF pp_t_negated_modal_operators_in_domain(2)]
          pp_t_dual_recurrent_possible_falsity_recurrence])
qed

end
