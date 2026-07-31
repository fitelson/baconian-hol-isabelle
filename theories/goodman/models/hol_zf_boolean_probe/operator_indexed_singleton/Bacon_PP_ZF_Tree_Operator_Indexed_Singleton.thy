theory Bacon_PP_ZF_Tree_Operator_Indexed_Singleton
  imports
    Higher_Order_Metaphysics_PP_ZF_Multi_Indexed_Conjunctive_Equivalence.Bacon_PP_ZF_Tree_Multi_Indexed_Conjunctive_Equivalence
begin

section \<open>A unary-operator-indexed singleton family\<close>

text \<open>
  This is the first indexed family in which the index itself is a unary
  operator:

    B(F,p)(q) = box(q iff F(p)).

  Its probe section at F maps p to the claim that F(p) is settled.  Unlike the
  preceding proposition-indexed examples, these sections have no common
  truth-value anchor, and complement symmetry does not identify arbitrary
  indices.
\<close>

definition pp_t_operator_indexed_singleton_family_builder :: oterm where
  "pp_t_operator_indexed_singleton_family_builder =
    Lam pp_t_one_context_unary_type
      (Lam Prop
        (App
          (shift (shift pp_t_singleton_family_builder))
          (App (Var 1) (Var 0))))"

definition pp_t_operator_indexed_singleton_probe_definition :: oterm where
  "pp_t_operator_indexed_singleton_probe_definition =
    Lam pp_t_one_context_unary_type
      (Lam Prop
        (App
          (shift (shift pp_t_settled_now_operator))
          (App (Var 1) (Var 0))))"

lemma pp_t_operator_indexed_singleton_terms_typed:
  "[] \<turnstile> pp_t_operator_indexed_singleton_family_builder :
    pp_t_one_context_unary_type
      \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  "[] \<turnstile> pp_t_operator_indexed_singleton_probe_definition :
    pp_t_one_context_unary_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (rule infer_type_sound;
      simp add:
        pp_t_operator_indexed_singleton_family_builder_def
        pp_t_operator_indexed_singleton_probe_definition_def
        pp_t_singleton_family_builder_def
        pp_t_settled_now_operator_def
        ObjBox_def ObjTrue_def lookup_def shift_def)+

lemma pp_t_operator_indexed_singleton_terms_logical:
  "pp_logical_vocabulary pp_t_operator_indexed_singleton_family_builder"
  "pp_logical_vocabulary pp_t_operator_indexed_singleton_probe_definition"
  by (simp_all add:
      pp_t_operator_indexed_singleton_family_builder_def
      pp_t_operator_indexed_singleton_probe_definition_def
      pp_t_singleton_family_builder_def
      pp_t_settled_now_operator_def
      pp_logical_vocabulary_def ObjBox_def ObjTrue_def shift_def)

lemma pp_t_operator_indexed_singleton_family_value:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(pp_t_closed_den
        pp_t_operator_indexed_singleton_family_builder \<acute> F) \<acute> p
      =
    pp_t_singleton_family_at (F \<acute> p)"
  unfolding
    pp_t_operator_indexed_singleton_family_builder_def
    pp_t_closed_den_def
  using F p
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_operator_indexed_singleton_probe_definition_apply:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(pp_t_closed_den
        pp_t_operator_indexed_singleton_probe_definition \<acute> F) \<acute> p
      =
    pp_t_closed_den pp_t_settled_now_operator \<acute> (F \<acute> p)"
  unfolding
    pp_t_operator_indexed_singleton_probe_definition_def
    pp_t_closed_den_def
  using F p
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_operator_indexed_singleton_probe_apply_holds:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        \<acute> p) w
      \<longleftrightarrow>
    (pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth True)
      \<or> pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth False))"
proof -
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have probe:
      "pp_t_holds
        ((pp_t_indexed_family_probe_for_stock
            pp_t_one_context_unary_type
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p) w
        \<longleftrightarrow>
      pp_t_closed_logical_stock pp_t_one_context_unary_type w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    using pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible F p,
      of w] .
  have stock:
      "pp_t_closed_logical_stock pp_t_one_context_unary_type w
          ((pp_t_closed_den
              pp_t_operator_indexed_singleton_family_builder \<acute> F)
            \<acute> p)
        \<longleftrightarrow>
      (pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth True)
        \<or> pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth False))"
    unfolding pp_t_operator_indexed_singleton_family_value[OF F p]
    using pp_t_singleton_family_in_closed_stock_iff_settled[
      OF Fp, of w] .
  show ?thesis
    using probe stock by blast
qed

theorem pp_t_operator_indexed_singleton_probe_eliminates_classifier:
  "pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder
    =
    pp_t_closed_den pp_t_operator_indexed_singleton_probe_definition"
proof (rule pp_t_indexed_unary_function_ext)
  show "Elem
      (pp_t_indexed_family_probe_for_stock
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder)
      (pp_t_domain
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_indexed_family_probe_for_stock_in_domain[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible] .
  show "Elem
      (pp_t_closed_den pp_t_operator_indexed_singleton_probe_definition)
      (pp_t_domain
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_t_operator_indexed_singleton_terms_typed(2)] .
  fix F
  assume F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  show "pp_t_indexed_family_probe_for_stock
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder \<acute> F
      =
      pp_t_closed_den
        pp_t_operator_indexed_singleton_probe_definition \<acute> F"
  proof (rule pp_t_unary_function_ext)
    show "Elem
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_indexed_family_probe_section_in_domain[
        OF pp_t_operator_indexed_singleton_terms_typed(1)
          pp_t_closed_logical_stock_admissible F] .
    show "Elem
        (pp_t_closed_den
          pp_t_operator_indexed_singleton_probe_definition \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_operator_indexed_singleton_terms_typed(2)]
        F] .
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "(pp_t_indexed_family_probe_for_stock
            pp_t_one_context_unary_type
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
            \<acute> p
        =
        (pp_t_closed_den
          pp_t_operator_indexed_singleton_probe_definition \<acute> F)
          \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          ((pp_t_indexed_family_probe_for_stock
              pp_t_one_context_unary_type
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_operator_indexed_singleton_family_builder \<acute> F)
            \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_indexed_family_probe_section_in_domain[
            OF pp_t_operator_indexed_singleton_terms_typed(1)
              pp_t_closed_logical_stock_admissible F]
          p] .
      show "Elem
          ((pp_t_closed_den
              pp_t_operator_indexed_singleton_probe_definition \<acute> F)
            \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_closed_den_in_domain[
              OF pp_t_operator_indexed_singleton_terms_typed(2)]
            F]
          p] .
      fix w
      have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
        by (rule pp_t_app_closed[OF F p])
      have probe:
          "pp_t_holds
            ((pp_t_indexed_family_probe_for_stock
                pp_t_one_context_unary_type
                (pp_t_closed_logical_stock pp_t_one_context_unary_type)
                pp_t_operator_indexed_singleton_family_builder \<acute> F)
              \<acute> p) w
          \<longleftrightarrow>
          (pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth True)
            \<or> pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth False))"
        by (rule pp_t_operator_indexed_singleton_probe_apply_holds[OF F p])
      have definition_holds:
          "pp_t_holds
            ((pp_t_closed_den
                pp_t_operator_indexed_singleton_probe_definition \<acute> F)
              \<acute> p) w
          \<longleftrightarrow>
          (pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth True)
            \<or> pp_t_eqv Prop w (F \<acute> p) (pp_zf_truth False))"
        unfolding
          pp_t_operator_indexed_singleton_probe_definition_apply[OF F p]
        using pp_t_settled_now_apply_holds[OF Fp, of w] .
      show "pp_t_holds
            ((pp_t_indexed_family_probe_for_stock
                pp_t_one_context_unary_type
                (pp_t_closed_logical_stock pp_t_one_context_unary_type)
                pp_t_operator_indexed_singleton_family_builder \<acute> F)
              \<acute> p) w
          \<longleftrightarrow>
          pp_t_holds
            ((pp_t_closed_den
                pp_t_operator_indexed_singleton_probe_definition \<acute> F)
              \<acute> p) w"
        using probe definition_holds by blast
    qed
  qed
qed

corollary pp_t_operator_indexed_singleton_probe_is_closed_logical:
  "pp_t_closed_logical_stock
    (pp_t_one_context_unary_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type) w
    (pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder)"
  unfolding pp_t_operator_indexed_singleton_probe_eliminates_classifier
  using pp_t_operator_indexed_singleton_terms_typed(2)
    pp_t_operator_indexed_singleton_terms_logical(2)
  by (rule pp_t_closed_logical_stockI)

end
