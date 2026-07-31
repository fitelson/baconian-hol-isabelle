theory Bacon_PP_ZF_Tree_Singleton_Symmetrized_Pair
  imports
    Higher_Order_Metaphysics_PP_ZF_Symmetrized_Singleton_Cross_Collision.Bacon_PP_ZF_Tree_Symmetrized_Singleton_Cross_Collision
begin

section \<open>Simultaneous stabilization of singleton and symmetrized families\<close>

definition pp_t_singleton_symmetrized_pair_builder :: "bool \<Rightarrow> oterm"
where
  "pp_t_singleton_symmetrized_pair_builder singleton =
    (if singleton
      then pp_t_singleton_family_builder
      else pp_t_symmetrized_singleton_family_builder)"

lemma pp_t_singleton_symmetrized_pair_builder_typed:
  "[] \<turnstile> pp_t_singleton_symmetrized_pair_builder singleton :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (cases singleton)
    (simp_all add: pp_t_singleton_symmetrized_pair_builder_def
      pp_t_singleton_family_builder_typed
      pp_t_symmetrized_singleton_family_builder_typed)

lemma pp_t_singleton_family_probe_for_closed_stock_eq_settled_now:
  "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_singleton_family_builder
    = pp_t_closed_den pp_t_settled_now_operator"
proof -
  have family_probe:
      "pp_t_family_probe pp_t_singleton_family_builder =
        pp_t_closed_den pp_t_settled_now_operator"
    by (rule pp_t_singleton_test_elimination_is_an_instance)
  show ?thesis
    using family_probe
    unfolding pp_t_family_probe_for_stock_def
      pp_t_family_probe_def
      pp_t_old_unary_stock_classifier_def
    by simp
qed

lemma pp_t_singleton_family_probe_for_closed_stock_in_stock:
  "pp_t_closed_logical_stock pp_t_one_context_unary_type w
    (pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_singleton_family_builder)"
  unfolding
    pp_t_singleton_family_probe_for_closed_stock_eq_settled_now
  using pp_t_settled_now_operator_typed
    pp_t_settled_now_operator_logical
  by (rule pp_t_closed_logical_stockI)

lemma pp_t_singleton_family_diagonal:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
    (pp_t_singleton_family_at p \<acute> p) w"
  using pp_t_singleton_family_at_apply_holds[OF p p, of w]
    pp_t_eqv_reflexive[OF p]
  by blast

lemma pp_t_closed_logical_stock_transfers_across_equivalence:
  assumes X: "Elem X
      (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y
      (pp_t_domain pp_t_one_context_unary_type)"
    and equivalent:
      "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and X_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w X"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w Y"
  using pp_t_closed_logical_stock_admissible
    X Y equivalent X_stock
  unfolding pp_t_predicate_admissible_def
  by simp

lemma pp_t_singleton_symmetrized_off_diagonal_collisions_absorbed:
  assumes i: "i \<in> UNIV"
    and j: "j \<in> UNIV"
    and different: "j \<noteq> i"
    and p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_singleton_symmetrized_pair_builder j))
        (pp_t_closed_den
          (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_closed_den
      (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)"
proof (cases i)
  case False
  have j_true: "j = True"
    using different False by auto
  have transferred:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at p)"
  proof (rule pp_t_closed_logical_stock_transfers_across_equivalence)
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_singleton_family_builder)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_family_probe_for_stock_in_domain[
        OF pp_t_singleton_family_builder_typed
          pp_t_closed_logical_stock_admissible] .
    show "Elem (pp_t_symmetrized_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_symmetrized_singleton_family_at_in_domain[OF p] .
    show "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_singleton_family_builder)
        (pp_t_symmetrized_singleton_family_at p)"
      using collision False j_true
      by (simp add: pp_t_singleton_symmetrized_pair_builder_def)
    show "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_singleton_family_builder)"
      by (rule
        pp_t_singleton_family_probe_for_closed_stock_in_stock)
  qed
  show ?thesis
    using transferred False
    by (simp add: pp_t_singleton_symmetrized_pair_builder_def)
next
  case True
  have j_false: "j = False"
    using different True by auto
  have forbidden:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_symmetrized_closed_stock_probe
        (pp_t_singleton_family_at p)"
    using collision True j_false
    unfolding pp_t_symmetrized_closed_stock_probe_def
    by (simp add: pp_t_singleton_symmetrized_pair_builder_def)
  show ?thesis
    using pp_t_symmetrized_probe_has_no_singleton_family_collision[
      OF p, of w]
      forbidden
    by contradiction
qed

theorem pp_t_singleton_symmetrized_pair_probes_stabilize_simultaneously:
  "\<forall>i \<in> UNIV.
    pp_t_family_probe_for_stock
      (pp_t_multi_family_probe_stock_enlargement
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_singleton_symmetrized_pair_builder UNIV)
      (pp_t_singleton_symmetrized_pair_builder i)
    =
    pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      (pp_t_singleton_symmetrized_pair_builder i)"
proof -
  have diagonal:
      "\<And>i p w.
        i \<in> UNIV \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds
          ((pp_t_closed_den
              (pp_t_singleton_symmetrized_pair_builder i)
              \<acute> p) \<acute> p) w"
  proof -
    fix i p w
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_holds
        ((pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i)
            \<acute> p) \<acute> p) w"
    proof (cases i)
      case False
      show ?thesis
        using pp_t_symmetrized_singleton_family_diagonal[
          OF p, of w]
          False
        by (simp add:
          pp_t_singleton_symmetrized_pair_builder_def)
    next
      case True
      show ?thesis
        using pp_t_singleton_family_diagonal[OF p, of w]
          True
        by (simp add:
          pp_t_singleton_symmetrized_pair_builder_def)
    qed
  qed
  have criterion:
      "(\<forall>i \<in> UNIV.
        pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_singleton_symmetrized_pair_builder UNIV)
          (pp_t_singleton_symmetrized_pair_builder i)
        =
        pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_singleton_symmetrized_pair_builder i))
      \<longleftrightarrow>
      (\<forall>i \<in> UNIV. \<forall>j \<in> UNIV. \<forall>p w.
        j \<noteq> i
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            (pp_t_singleton_symmetrized_pair_builder j))
          (pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i) \<acute> p))"
    using pp_t_diagonally_reflexive_multi_family_probes_stabilize_iff_off_diagonal_collisions_absorbed[
      OF pp_t_singleton_symmetrized_pair_builder_typed
        pp_t_closed_logical_stock_admissible diagonal] .
  show ?thesis
  proof (rule iffD2[OF criterion])
    show "\<forall>i \<in> UNIV. \<forall>j \<in> UNIV. \<forall>p w.
        j \<noteq> i
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            (pp_t_singleton_symmetrized_pair_builder j))
          (pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)"
    proof (intro ballI allI impI)
      fix i j p w
      assume i: "i \<in> UNIV"
        and j: "j \<in> UNIV"
        and different: "j \<noteq> i"
        and p: "Elem p (pp_t_domain Prop)"
        and collision:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock
              (pp_t_closed_logical_stock
                pp_t_one_context_unary_type)
              (pp_t_singleton_symmetrized_pair_builder j))
            (pp_t_closed_den
              (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)"
      show "pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den
            (pp_t_singleton_symmetrized_pair_builder i) \<acute> p)"
        using
          pp_t_singleton_symmetrized_off_diagonal_collisions_absorbed[
            OF i j different p collision] .
    qed
  qed
qed

end
