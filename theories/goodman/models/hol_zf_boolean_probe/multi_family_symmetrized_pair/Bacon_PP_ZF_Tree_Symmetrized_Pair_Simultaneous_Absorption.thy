theory Bacon_PP_ZF_Tree_Symmetrized_Pair_Simultaneous_Absorption
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Family_Off_Diagonal.Bacon_PP_ZF_Tree_Multi_Family_Off_Diagonal
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Complemented_Symmetrized_Singleton
begin

section \<open>Simultaneous absorption of the symmetrized family and its complement\<close>

definition pp_t_symmetrized_pair_family_builder :: "bool \<Rightarrow> oterm"
where
  "pp_t_symmetrized_pair_family_builder complemented =
    (if complemented
      then pp_t_complemented_symmetrized_singleton_family_builder
      else pp_t_symmetrized_singleton_family_builder)"

lemma pp_t_symmetrized_pair_family_builder_typed:
  "[] \<turnstile> pp_t_symmetrized_pair_family_builder complemented :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (cases complemented)
    (simp_all add: pp_t_symmetrized_pair_family_builder_def
      pp_t_symmetrized_singleton_family_builder_typed
      pp_t_complemented_symmetrized_singleton_family_builder_typed)

lemma pp_t_symmetrized_pair_probe_eq:
  "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      (pp_t_symmetrized_pair_family_builder complemented)
    = pp_t_symmetrized_closed_stock_probe"
proof (cases complemented)
  case False
  then show ?thesis
    unfolding pp_t_symmetrized_pair_family_builder_def
      pp_t_symmetrized_closed_stock_probe_def
    by simp
next
  case True
  then show ?thesis
    unfolding pp_t_symmetrized_pair_family_builder_def
    using pp_t_complemented_closed_stock_probe_eq
    by simp
qed

lemma pp_t_symmetrized_pair_cross_collisions_absorbed:
  assumes p: "Elem p (pp_t_domain Prop)"
    and collision:
      "\<exists>j \<in> UNIV.
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            (pp_t_symmetrized_pair_family_builder j))
          (pp_t_closed_den
            (pp_t_symmetrized_pair_family_builder i) \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_closed_den
      (pp_t_symmetrized_pair_family_builder i) \<acute> p)"
proof (cases i)
  case False
  obtain j where raw_at_i:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_symmetrized_pair_family_builder j))
        (pp_t_closed_den
          (pp_t_symmetrized_pair_family_builder i) \<acute> p)"
    using collision by auto
  have raw_collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_symmetrized_pair_family_builder j))
        (pp_t_closed_den
          (pp_t_symmetrized_pair_family_builder False) \<acute> p)"
    using raw_at_i False by simp
  have symmetrized_collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_symmetrized_closed_stock_probe
        (pp_t_symmetrized_singleton_family_at p)"
    using raw_collision pp_t_symmetrized_pair_probe_eq[of j]
    unfolding pp_t_symmetrized_pair_family_builder_def
    by simp
  have absorbed:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at p)"
    using pp_t_symmetrized_closed_stock_probe_collision_absorbed[
      OF p symmetrized_collision] .
  show ?thesis
    using absorbed False
    by (simp add: pp_t_symmetrized_pair_family_builder_def)
next
  case True
  obtain j where raw_at_i:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_symmetrized_pair_family_builder j))
        (pp_t_closed_den
          (pp_t_symmetrized_pair_family_builder i) \<acute> p)"
    using collision by auto
  have raw_collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_symmetrized_pair_family_builder j))
        (pp_t_closed_den
          (pp_t_symmetrized_pair_family_builder True) \<acute> p)"
    using raw_at_i True by simp
  have complemented_collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_complemented_symmetrized_singleton_family_builder)
        (pp_t_complemented_symmetrized_singleton_family_at p)"
    using raw_collision pp_t_symmetrized_pair_probe_eq[of j]
      pp_t_complemented_closed_stock_probe_eq
    unfolding pp_t_symmetrized_pair_family_builder_def
    by simp
  show ?thesis
    using pp_t_complemented_symmetrized_probe_has_no_collision[
      OF p, of w]
      complemented_collision
    by contradiction
qed

theorem pp_t_symmetrized_pair_probes_stabilize_simultaneously:
  "\<forall>i \<in> UNIV.
    pp_t_family_probe_for_stock
      (pp_t_multi_family_probe_stock_enlargement
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_symmetrized_pair_family_builder UNIV)
      (pp_t_symmetrized_pair_family_builder i)
    =
    pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      (pp_t_symmetrized_pair_family_builder i)"
proof -
  have criterion:
      "(\<forall>i \<in> UNIV.
        pp_t_family_probe_for_stock
          (pp_t_multi_family_probe_stock_enlargement
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_symmetrized_pair_family_builder UNIV)
          (pp_t_symmetrized_pair_family_builder i)
        =
        pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_symmetrized_pair_family_builder i))
      \<longleftrightarrow>
      (\<forall>i \<in> UNIV. \<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> UNIV.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock
              (pp_t_closed_logical_stock
                pp_t_one_context_unary_type)
              (pp_t_symmetrized_pair_family_builder j))
            (pp_t_closed_den
              (pp_t_symmetrized_pair_family_builder i) \<acute> p))
        \<longrightarrow>
        pp_t_closed_logical_stock pp_t_one_context_unary_type w
          (pp_t_closed_den
            (pp_t_symmetrized_pair_family_builder i) \<acute> p))"
    using pp_t_multi_family_probes_stabilize_iff_cross_collision_matrix_absorbed[
      OF pp_t_symmetrized_pair_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  show ?thesis
  proof (rule iffD2[OF criterion])
    show "\<forall>i \<in> UNIV. \<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> UNIV.
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_family_probe_for_stock
              (pp_t_closed_logical_stock
                pp_t_one_context_unary_type)
              (pp_t_symmetrized_pair_family_builder j))
            (pp_t_closed_den
              (pp_t_symmetrized_pair_family_builder i) \<acute> p))
        \<longrightarrow>
        pp_t_closed_logical_stock pp_t_one_context_unary_type w
          (pp_t_closed_den
            (pp_t_symmetrized_pair_family_builder i) \<acute> p)"
      using pp_t_symmetrized_pair_cross_collisions_absorbed
      by blast
  qed
qed

end
