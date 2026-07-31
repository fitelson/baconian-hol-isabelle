theory Bacon_PP_ZF_Tree_Multi_Indexed_Conjunctive_Equivalence
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Family_Off_Diagonal.Bacon_PP_ZF_Tree_Multi_Indexed_Family_Off_Diagonal
begin

section \<open>Simultaneous stabilization of two proposition-indexed families\<close>

definition pp_t_conjunctive_equivalence_indexed_builder ::
    "bool \<Rightarrow> oterm"
where
  "pp_t_conjunctive_equivalence_indexed_builder equivalence =
    (if equivalence
     then pp_t_indexed_equivalence_singleton_family_builder
     else pp_t_indexed_conjunctive_singleton_family_builder)"

lemma pp_t_conjunctive_equivalence_indexed_builder_typed:
  "[] \<turnstile> pp_t_conjunctive_equivalence_indexed_builder i :
    Prop \<rightarrow>\<^sub>o Prop
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  unfolding pp_t_conjunctive_equivalence_indexed_builder_def
  using pp_t_indexed_equivalence_singleton_family_builder_typed
    pp_t_indexed_conjunctive_singleton_terms_typed(1)
  by (cases i) simp_all

lemma pp_t_equivalence_probe_has_no_conjunctive_target_collision:
  assumes a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_indexed_family_probe_for_stock Prop
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_indexed_equivalence_singleton_family_builder \<acute> b)
    ((pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
      \<acute> p)"
  unfolding
    pp_t_indexed_equivalence_probe_section_eq_symmetrized_singleton[
      OF b]
    pp_t_indexed_conjunctive_singleton_family_value[OF a p]
  using pp_t_symmetrized_singleton_value_has_no_singleton_family_collision[
    OF b pp_t_indexed_conjunctive_parameter_in_domain, of w] .

lemma pp_t_equivalence_singleton_false_reflects_stock:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and target_false_true:
      "pp_t_holds
        (((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p) \<acute> pp_zf_truth False) w"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    ((pp_t_closed_den
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
      \<acute> p)"
proof -
  let ?false = "pp_zf_truth False"
  let ?r = "pp_t_indexed_equivalence_parameter a p"
  have false: "Elem ?false (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_indexed_equivalence_parameter_in_domain)
  have false_r: "pp_t_eqv Prop w ?false ?r"
    using target_false_true
    unfolding pp_t_indexed_equivalence_singleton_family_value[
      OF a p]
    using pp_t_singleton_family_at_apply_holds[
      OF r false, of w]
    by blast
  have r_false: "pp_t_eqv Prop w ?r ?false"
    using pp_t_eqv_symmetric[OF false r false_r] .
  show ?thesis
    unfolding pp_t_indexed_equivalence_singleton_family_value[
      OF a p]
    using pp_t_singleton_family_in_closed_stock_iff_settled[
      OF r, of w]
      r_false by blast
qed

lemma pp_t_conjunctive_probe_equivalence_target_collision_absorbed:
  assumes a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock Prop
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
        ((pp_t_closed_den
            pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
          \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    ((pp_t_closed_den
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
      \<acute> p)"
proof -
  let ?false = "pp_zf_truth False"
  have false: "Elem ?false (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have ff: "pp_t_eqv Prop w ?false ?false"
    by (rule pp_t_eqv_reflexive[OF false])
  have applications:
      "pp_t_eqv Prop w
        ((pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
          \<acute> ?false)
        (((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p) \<acute> ?false)"
    using pp_t_app_respects[OF collision false false ff] .
  have probe_true:
      "pp_t_holds
        ((pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
          \<acute> ?false) w"
    by (rule pp_t_indexed_conjunctive_singleton_probe_false[OF b])
  have target_false_true:
      "pp_t_holds
        (((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p) \<acute> ?false) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      probe_true by simp
  show ?thesis
    using pp_t_equivalence_singleton_false_reflects_stock[
      OF a p target_false_true] .
qed

lemma pp_t_conjunctive_equivalence_indexed_collision_absorbed:
  assumes i: "i \<in> (UNIV :: bool set)"
    and j: "j \<in> (UNIV :: bool set)"
    and a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock Prop
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (pp_t_conjunctive_equivalence_indexed_builder j) \<acute> b)
        ((pp_t_closed_den
            (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
          \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    ((pp_t_closed_den
        (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
      \<acute> p)"
proof (cases i)
  case False
  then have target:
      "pp_t_conjunctive_equivalence_indexed_builder i =
        pp_t_indexed_conjunctive_singleton_family_builder"
    by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
  show ?thesis
  proof (cases j)
    case False
    then have probe:
        "pp_t_conjunctive_equivalence_indexed_builder j =
          pp_t_indexed_conjunctive_singleton_family_builder"
      by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
    have collision':
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
          ((pp_t_closed_den
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p)"
      using collision unfolding target probe .
    show ?thesis
      unfolding target
      using
        pp_t_indexed_conjunctive_singleton_all_collisions_absorbed[
          OF a b p collision'] .
  next
    case True
    then have probe:
        "pp_t_conjunctive_equivalence_indexed_builder j =
          pp_t_indexed_equivalence_singleton_family_builder"
      by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
    have impossible:
        "\<not> pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_equivalence_singleton_family_builder \<acute> b)
          ((pp_t_closed_den
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p)"
      by (rule
        pp_t_equivalence_probe_has_no_conjunctive_target_collision[
          OF a b p])
    show ?thesis
      using collision impossible
      unfolding target probe by blast
  qed
next
  case True
  then have target:
      "pp_t_conjunctive_equivalence_indexed_builder i =
        pp_t_indexed_equivalence_singleton_family_builder"
    by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
  show ?thesis
  proof (cases j)
    case False
    then have probe:
        "pp_t_conjunctive_equivalence_indexed_builder j =
          pp_t_indexed_conjunctive_singleton_family_builder"
      by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
    have collision':
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
          ((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p)"
      using collision unfolding target probe .
    show ?thesis
      unfolding target
      using
        pp_t_conjunctive_probe_equivalence_target_collision_absorbed[
          OF a b p collision'] .
  next
    case True
    then have probe:
        "pp_t_conjunctive_equivalence_indexed_builder j =
          pp_t_indexed_equivalence_singleton_family_builder"
      by (simp add: pp_t_conjunctive_equivalence_indexed_builder_def)
    have impossible:
        "\<not> pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_equivalence_singleton_family_builder \<acute> b)
          ((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p)"
      by (rule
        pp_t_indexed_equivalence_singleton_has_no_collisions[
          OF a b p])
    show ?thesis
      using collision impossible
      unfolding target probe by blast
  qed
qed

theorem
  pp_t_conjunctive_equivalence_indexed_probes_stabilize_simultaneously:
  "\<forall>i \<in> (UNIV :: bool set).
    pp_t_indexed_family_probe_for_stock Prop
        (pp_t_multi_indexed_family_section_stock_enlargement
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          (\<lambda>_. Prop)
          pp_t_conjunctive_equivalence_indexed_builder
          UNIV)
        (pp_t_conjunctive_equivalence_indexed_builder i)
      =
      pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        (pp_t_conjunctive_equivalence_indexed_builder i)"
proof -
  have all_collisions:
      "\<forall>i \<in> (UNIV :: bool set). \<forall>a p w.
        Elem a (pp_t_domain Prop)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>j \<in> (UNIV :: bool set). \<exists>b.
          Elem b (pp_t_domain Prop)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              (pp_t_conjunctive_equivalence_indexed_builder j) \<acute> b)
            ((pp_t_closed_den
                (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
              \<acute> p))
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          ((pp_t_closed_den
              (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
            \<acute> p)"
  proof (intro ballI allI impI)
    fix i a p w
    assume i: "i \<in> (UNIV :: bool set)"
      and a: "Elem a (pp_t_domain Prop)"
      and p: "Elem p (pp_t_domain Prop)"
      and some_collision:
        "\<exists>j \<in> (UNIV :: bool set). \<exists>b.
          Elem b (pp_t_domain Prop)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              (pp_t_conjunctive_equivalence_indexed_builder j) \<acute> b)
            ((pp_t_closed_den
                (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
              \<acute> p)"
    then obtain j b where j: "j \<in> (UNIV :: bool set)"
      and b: "Elem b (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            (pp_t_conjunctive_equivalence_indexed_builder j) \<acute> b)
          ((pp_t_closed_den
              (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
            \<acute> p)"
      by blast
    show "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        ((pp_t_closed_den
            (pp_t_conjunctive_equivalence_indexed_builder i) \<acute> a)
          \<acute> p)"
      using
        pp_t_conjunctive_equivalence_indexed_collision_absorbed[
          OF i j a b p collision] .
  qed
  show ?thesis
    using
      pp_t_multi_indexed_family_probes_stabilize_iff_collision_matrix_absorbed[
        where I="UNIV :: bool set" and \<alpha>="\<lambda>_. Prop"
          and B=pp_t_conjunctive_equivalence_indexed_builder
          and S="pp_t_closed_logical_stock
            pp_t_one_context_unary_type",
        OF pp_t_conjunctive_equivalence_indexed_builder_typed
          pp_t_closed_logical_stock_admissible]
      all_collisions
    by (rule iffD2)
qed

end
