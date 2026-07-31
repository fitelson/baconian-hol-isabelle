theory Bacon_PP_ZF_Tree_Iterated_Stabilization
  imports
    Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Collision.Bacon_PP_ZF_Tree_Operator_Indexed_Collision
begin

section \<open>A generic two-stage stabilization theorem\<close>

text \<open>
  A first probe-section enlargement need not be a fixed point.  It nevertheless
  becomes one at the next stage whenever the old probe sections already cover
  every generated family value.  The theorem is purely semantic and does not
  depend on the particular mechanism establishing coverage.
\<close>

lemma pp_t_indexed_family_values_enter_first_enlargement_from_coverage:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type S"
    and coverage:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        \<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_indexed_family_section_stock_enlargement \<alpha> S B w
      ((pp_t_closed_den B \<acute> a) \<acute> p)"
  unfolding pp_t_indexed_family_section_stock_enlargement_def
  using coverage[OF a p, of w] by blast

theorem pp_t_indexed_family_stabilizes_at_second_stage_from_coverage:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type S"
    and coverage:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        \<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p)"
  shows
    "pp_t_indexed_family_probe_for_stock \<alpha>
        (pp_t_indexed_family_section_stock_enlargement \<alpha>
          (pp_t_indexed_family_section_stock_enlargement \<alpha> S B)
          B)
        B
      =
    pp_t_indexed_family_probe_for_stock \<alpha>
      (pp_t_indexed_family_section_stock_enlargement \<alpha> S B)
      B"
proof -
  let ?S1 =
    "pp_t_indexed_family_section_stock_enlargement \<alpha> S B"
  have S1_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type ?S1"
    by (rule pp_t_indexed_family_section_stock_enlargement_admissible[
      OF B_typed S_admissible])
  have absorbed:
      "\<forall>a p w.
        Elem a (pp_t_domain \<alpha>)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>b.
          Elem b (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock \<alpha> ?S1 B \<acute> b)
            ((pp_t_closed_den B \<acute> a) \<acute> p))
        \<longrightarrow>
        ?S1 w ((pp_t_closed_den B \<acute> a) \<acute> p)"
    using
      pp_t_indexed_family_values_enter_first_enlargement_from_coverage[
        OF B_typed S_admissible coverage]
    by blast
  show ?thesis
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF B_typed S1_admissible]
      absorbed
    by (rule iffD2)
qed

section \<open>Simultaneous two-stage stabilization of a finite component\<close>

lemma pp_t_multi_indexed_family_values_enter_first_enlargement_from_coverage:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          \<alpha> i \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type S"
    and coverage:
      "\<And>i a p w.
        i \<in> I \<Longrightarrow>
        Elem a (pp_t_domain (\<alpha> i)) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        \<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock
              (\<alpha> j) S (B j) \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    and i: "i \<in> I"
    and a: "Elem a (pp_t_domain (\<alpha> i))"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_multi_indexed_family_section_stock_enlargement
      S \<alpha> B I w
      ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
  unfolding pp_t_multi_indexed_family_section_stock_enlargement_def
  using coverage[OF i a p, of w] by blast

theorem
  pp_t_multi_indexed_family_stabilizes_at_second_stage_from_coverage:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          \<alpha> i \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type S"
    and coverage:
      "\<And>i a p w.
        i \<in> I \<Longrightarrow>
        Elem a (pp_t_domain (\<alpha> i)) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        \<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock
              (\<alpha> j) S (B j) \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
  shows
    "\<forall>i \<in> I.
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
          (pp_t_multi_indexed_family_section_stock_enlargement
            (pp_t_multi_indexed_family_section_stock_enlargement
              S \<alpha> B I)
            \<alpha> B I)
          (B i)
        =
      pp_t_indexed_family_probe_for_stock (\<alpha> i)
        (pp_t_multi_indexed_family_section_stock_enlargement
          S \<alpha> B I)
        (B i)"
proof -
  let ?S1 =
    "pp_t_multi_indexed_family_section_stock_enlargement S \<alpha> B I"
  have S1_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type ?S1"
    by (rule
      pp_t_multi_indexed_family_section_stock_enlargement_admissible[
        OF B_typed S_admissible])
  have absorbed:
      "\<forall>i \<in> I. \<forall>a p w.
        Elem a (pp_t_domain (\<alpha> i))
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> I. \<exists>b.
          Elem b (pp_t_domain (\<alpha> j))
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock
              (\<alpha> j) ?S1 (B j) \<acute> b)
            ((pp_t_closed_den (B i) \<acute> a) \<acute> p))
        \<longrightarrow>
        ?S1 w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)"
    using
      pp_t_multi_indexed_family_values_enter_first_enlargement_from_coverage[
        OF B_typed S_admissible coverage]
    by blast
  show ?thesis
    using
      pp_t_multi_indexed_family_probes_stabilize_iff_collision_matrix_absorbed[
        OF B_typed S1_admissible]
      absorbed
    by (rule iffD2)
qed

end
