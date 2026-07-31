theory Bacon_PP_ZF_Tree_Indexed_Conjunctive_Singleton
  imports
    Higher_Order_Metaphysics_PP_ZF_Indexed_Family_Anchor.Bacon_PP_ZF_Tree_Indexed_Family_Anchor
begin

section \<open>A proposition-indexed singleton family\<close>

text \<open>
  The family below is uniform in an arbitrary quantified proposition \<open>a\<close>:

    B(a,p)(q) = box(q iff (a and p)).

  Thus one finite object-language term generates infinitely many semantic
  sections.  The associated indexed probe asks, for each \<open>a\<close> and \<open>p\<close>,
  whether the singleton family at \<open>a and p\<close> belongs to the old unary
  stock.
\<close>

definition pp_t_indexed_conjunctive_singleton_family_builder :: oterm where
  "pp_t_indexed_conjunctive_singleton_family_builder =
    Lam Prop
      (Lam Prop
        (App
          (shift (shift pp_t_singleton_family_builder))
          (Conj (Var 1) (Var 0))))"

definition pp_t_indexed_conjunctive_singleton_probe_definition :: oterm where
  "pp_t_indexed_conjunctive_singleton_probe_definition =
    Lam Prop
      (Lam Prop
        (App
          (shift (shift pp_t_settled_now_operator))
          (Conj (Var 1) (Var 0))))"

lemma pp_t_indexed_conjunctive_singleton_terms_typed:
  "[] \<turnstile> pp_t_indexed_conjunctive_singleton_family_builder :
    Prop \<rightarrow>\<^sub>o Prop
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_indexed_conjunctive_singleton_probe_definition :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (rule infer_type_sound;
      simp add:
        pp_t_indexed_conjunctive_singleton_family_builder_def
        pp_t_indexed_conjunctive_singleton_probe_definition_def
        pp_t_singleton_family_builder_def
        pp_t_settled_now_operator_def
        ObjBox_def ObjTrue_def lookup_def shift_def)+

lemma pp_t_indexed_conjunctive_singleton_terms_logical:
  "pp_logical_vocabulary
    pp_t_indexed_conjunctive_singleton_family_builder"
  "pp_logical_vocabulary
    pp_t_indexed_conjunctive_singleton_probe_definition"
  by (simp_all add:
      pp_t_indexed_conjunctive_singleton_family_builder_def
      pp_t_indexed_conjunctive_singleton_probe_definition_def
      pp_t_singleton_family_builder_def
      pp_t_settled_now_operator_def
      pp_logical_vocabulary_def ObjBox_def ObjTrue_def shift_def)

definition pp_t_indexed_conjunctive_parameter ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_indexed_conjunctive_parameter a p =
    pp_t_prop (\<lambda>w. pp_t_holds a w \<and> pp_t_holds p w)"

lemma pp_t_indexed_conjunctive_parameter_in_domain:
  "Elem (pp_t_indexed_conjunctive_parameter a p)
    (pp_t_domain Prop)"
  unfolding pp_t_indexed_conjunctive_parameter_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_indexed_conjunctive_parameter_false[simp]:
  assumes a: "Elem a (pp_t_domain Prop)"
  shows "pp_t_indexed_conjunctive_parameter a
      (pp_zf_truth False)
    = pp_zf_truth False"
proof (rule pp_t_prop_ext)
  show "Elem
      (pp_t_indexed_conjunctive_parameter a (pp_zf_truth False))
      (pp_t_domain Prop)"
    by (rule pp_t_indexed_conjunctive_parameter_in_domain)
  show "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  fix w
  show "pp_t_holds
      (pp_t_indexed_conjunctive_parameter a (pp_zf_truth False)) w
      \<longleftrightarrow>
      pp_t_holds (pp_zf_truth False) w"
    by (simp add: pp_t_indexed_conjunctive_parameter_def)
qed

lemma pp_t_indexed_conjunctive_singleton_family_value:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a) \<acute> p
      =
    pp_t_singleton_family_at
      (pp_t_indexed_conjunctive_parameter a p)"
  unfolding
    pp_t_indexed_conjunctive_singleton_family_builder_def
    pp_t_indexed_conjunctive_parameter_def
    pp_t_closed_den_def
  using a p
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_indexed_conjunctive_singleton_probe_definition_apply:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
        \<acute> p
      =
    pp_t_closed_den pp_t_settled_now_operator
      \<acute> pp_t_indexed_conjunctive_parameter a p"
  unfolding
    pp_t_indexed_conjunctive_singleton_probe_definition_def
    pp_t_indexed_conjunctive_parameter_def
    pp_t_closed_den_def
  using a p
  by (simp add: Lambda_app pp_t_eval_shift)

theorem pp_t_indexed_conjunctive_singleton_probe_eliminates_classifier:
  "pp_t_indexed_family_probe_for_stock Prop
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_indexed_conjunctive_singleton_family_builder
    =
    pp_t_closed_den
      pp_t_indexed_conjunctive_singleton_probe_definition"
proof (rule pp_t_indexed_unary_function_ext)
  show "Elem
      (pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_conjunctive_singleton_family_builder)
      (pp_t_domain
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_indexed_family_probe_for_stock_in_domain[
      OF pp_t_indexed_conjunctive_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible] .
  show "Elem
      (pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_probe_definition)
      (pp_t_domain
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_t_indexed_conjunctive_singleton_terms_typed(2)] .
  fix a
  assume a: "Elem a (pp_t_domain Prop)"
  show "pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a
      =
      pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a"
  proof (rule pp_t_unary_function_ext)
    show "Elem
        (pp_t_indexed_family_probe_for_stock Prop
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_indexed_family_probe_section_in_domain[
        OF pp_t_indexed_conjunctive_singleton_terms_typed(1)
          pp_t_closed_logical_stock_admissible a] .
    show "Elem
        (pp_t_closed_den
          pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_indexed_conjunctive_singleton_terms_typed(2)]
        a] .
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "(pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p
        =
        (pp_t_closed_den
          pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
          \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          ((pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_indexed_family_probe_section_in_domain[
            OF pp_t_indexed_conjunctive_singleton_terms_typed(1)
              pp_t_closed_logical_stock_admissible a]
          p] .
      show "Elem
          ((pp_t_closed_den
              pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
            \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_closed_den_in_domain[
              OF pp_t_indexed_conjunctive_singleton_terms_typed(2)]
            a]
          p] .
      fix w
      let ?r = "pp_t_indexed_conjunctive_parameter a p"
      have r: "Elem ?r (pp_t_domain Prop)"
        by (rule pp_t_indexed_conjunctive_parameter_in_domain)
      have probe:
          "pp_t_holds
            ((pp_t_indexed_family_probe_for_stock Prop
                (pp_t_closed_logical_stock pp_t_one_context_unary_type)
                pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
              \<acute> p) w
          \<longleftrightarrow>
          pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            ((pp_t_closed_den
                pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
              \<acute> p)"
        using pp_t_indexed_family_probe_for_stock_apply_holds[
          OF pp_t_indexed_conjunctive_singleton_terms_typed(1)
            pp_t_closed_logical_stock_admissible a p,
          of w] .
      have stock:
          "pp_t_closed_logical_stock
              pp_t_one_context_unary_type w
              ((pp_t_closed_den
                  pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
                \<acute> p)
          \<longleftrightarrow>
          (pp_t_eqv Prop w ?r (pp_zf_truth True)
            \<or> pp_t_eqv Prop w ?r (pp_zf_truth False))"
        unfolding
          pp_t_indexed_conjunctive_singleton_family_value[OF a p]
        using pp_t_singleton_family_in_closed_stock_iff_settled[
          OF r, of w] .
      have definition_holds:
          "pp_t_holds
            ((pp_t_closed_den
                pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
              \<acute> p) w
          \<longleftrightarrow>
          (pp_t_eqv Prop w ?r (pp_zf_truth True)
            \<or> pp_t_eqv Prop w ?r (pp_zf_truth False))"
        unfolding
          pp_t_indexed_conjunctive_singleton_probe_definition_apply[
            OF a p]
        using pp_t_settled_now_apply_holds[OF r, of w] .
      show "pp_t_holds
            ((pp_t_indexed_family_probe_for_stock Prop
                (pp_t_closed_logical_stock pp_t_one_context_unary_type)
                pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
              \<acute> p) w
          \<longleftrightarrow>
          pp_t_holds
            ((pp_t_closed_den
                pp_t_indexed_conjunctive_singleton_probe_definition \<acute> a)
              \<acute> p) w"
        using probe stock definition_holds by blast
    qed
  qed
qed

lemma pp_t_indexed_conjunctive_singleton_probe_false:
  assumes a: "Elem a (pp_t_domain Prop)"
  shows "pp_t_holds
    ((pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
      \<acute> pp_zf_truth False) w"
proof -
  have false: "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have parameter:
      "pp_t_indexed_conjunctive_parameter a (pp_zf_truth False)
        = pp_zf_truth False"
    by (rule pp_t_indexed_conjunctive_parameter_false[OF a])
  have settled:
      "pp_t_holds
        (pp_t_closed_den pp_t_settled_now_operator
          \<acute> pp_t_indexed_conjunctive_parameter a
            (pp_zf_truth False)) w"
    unfolding parameter
    using pp_t_settled_now_apply_holds[OF false, of w]
    by simp
  show ?thesis
    using settled
    unfolding
      pp_t_indexed_conjunctive_singleton_probe_eliminates_classifier
      pp_t_indexed_conjunctive_singleton_probe_definition_apply[
        OF a false] .
qed

lemma pp_t_indexed_conjunctive_singleton_false_reflects_stock:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and target_false_true:
      "pp_t_holds
        (((pp_t_closed_den
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p) \<acute> pp_zf_truth False) w"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    ((pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
      \<acute> p)"
proof -
  let ?false = "pp_zf_truth False"
  let ?r = "pp_t_indexed_conjunctive_parameter a p"
  have false: "Elem ?false (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_indexed_conjunctive_parameter_in_domain)
  have false_r: "pp_t_eqv Prop w ?false ?r"
    using target_false_true
    unfolding pp_t_indexed_conjunctive_singleton_family_value[OF a p]
    using pp_t_singleton_family_at_apply_holds[
      OF r false, of w]
    by blast
  have r_false: "pp_t_eqv Prop w ?r ?false"
    using pp_t_eqv_symmetric[OF false r false_r] .
  show ?thesis
    unfolding pp_t_indexed_conjunctive_singleton_family_value[OF a p]
    using pp_t_singleton_family_in_closed_stock_iff_settled[
      OF r, of w]
      r_false by blast
qed

lemma pp_t_indexed_conjunctive_singleton_all_collisions_absorbed:
  assumes a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock Prop
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_indexed_conjunctive_singleton_family_builder \<acute> b)
        ((pp_t_closed_den
            pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
          \<acute> p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    ((pp_t_closed_den
        pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
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
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
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
              pp_t_indexed_conjunctive_singleton_family_builder \<acute> a)
            \<acute> p) \<acute> ?false) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      probe_true by simp
  show ?thesis
    using
      pp_t_indexed_conjunctive_singleton_false_reflects_stock[
        OF a p target_false_true] .
qed

theorem
  pp_t_indexed_conjunctive_singleton_probe_stabilizes_after_all_sections_adjoined:
  "pp_t_indexed_family_probe_for_stock Prop
      (pp_t_indexed_family_section_stock_enlargement Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_conjunctive_singleton_family_builder)
      pp_t_indexed_conjunctive_singleton_family_builder
    =
    pp_t_indexed_family_probe_for_stock Prop
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_indexed_conjunctive_singleton_family_builder"
proof -
  show ?thesis
    apply (rule pp_t_indexed_family_probe_stabilizes_from_true_anchor[
      OF pp_t_indexed_conjunctive_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible
        pp_t_truth_in_domain[of False]])
    subgoal for b w
      by (rule pp_t_indexed_conjunctive_singleton_probe_false)
    subgoal for a p w
      by (rule
        pp_t_indexed_conjunctive_singleton_false_reflects_stock)
    done
qed

end
