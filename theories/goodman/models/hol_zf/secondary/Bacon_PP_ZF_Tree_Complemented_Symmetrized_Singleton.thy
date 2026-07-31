theory Bacon_PP_ZF_Tree_Complemented_Symmetrized_Singleton
  imports
    Bacon_PP_ZF_Tree_Symmetrized_Singleton
    Bacon_PP_ZF_Tree_Family_Probe_Absorption
begin

section \<open>The complemented symmetrized-singleton family\<close>

definition pp_t_unary_complement :: "ZF \<Rightarrow> ZF" where
  "pp_t_unary_complement F =
    Lambda (pp_t_domain Prop)
      (\<lambda>p. pp_t_complement (F \<acute> p))"

lemma pp_t_unary_complement_in_domain:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows "Elem (pp_t_unary_complement F)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_unary_complement_def
proof (rule pp_t_lambda_closed)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "Elem (pp_t_complement (F \<acute> p))
      (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
next
  fix w p q
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_eqv Prop w p q"
  have images: "pp_t_eqv Prop w (F \<acute> p) (F \<acute> q)"
    using pp_t_arrow_member_respects[OF F p q pq] .
  show "pp_t_eqv Prop w
      (pp_t_complement (F \<acute> p))
      (pp_t_complement (F \<acute> q))"
    using images
    by (simp add: pp_t_eqv.simps)
qed

lemma pp_t_unary_complement_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_unary_complement F \<acute> p =
    pp_t_complement (F \<acute> p)"
  using p
  by (simp add: pp_t_unary_complement_def Lambda_app)

lemma pp_t_unary_complement_involution:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows "pp_t_unary_complement (pp_t_unary_complement F) = F"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_unary_complement (pp_t_unary_complement F))
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_unary_complement_in_domain[
      OF pp_t_unary_complement_in_domain[OF F]] .
  show "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule F)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_unary_complement (pp_t_unary_complement F) \<acute> p =
      F \<acute> p"
    unfolding pp_t_unary_complement_apply[OF p]
      pp_t_unary_complement_apply[OF p]
    using pp_t_complement_involution[
      OF pp_t_app_closed[OF F p]] .
qed

definition pp_t_unary_output_negator :: oterm where
  "pp_t_unary_output_negator =
    Lam pp_t_one_context_unary_type
      (Lam Prop (Neg (App (Var 1) (Var 0))))"

lemma pp_t_unary_output_negator_typed:
  "[] \<turnstile> pp_t_unary_output_negator :
    pp_t_one_context_unary_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  unfolding pp_t_unary_output_negator_def
  by (intro has_type.Lam has_type.Neg has_type.App
      has_type.Var) simp_all

lemma pp_t_unary_output_negator_logical:
  "pp_logical_vocabulary pp_t_unary_output_negator"
  by (simp add: pp_t_unary_output_negator_def
      pp_logical_vocabulary_def)

lemma pp_t_unary_output_negator_apply:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows "pp_t_closed_den pp_t_unary_output_negator \<acute> F =
    pp_t_unary_complement F"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_closed_den pp_t_unary_output_negator \<acute> F)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[
        OF pp_t_unary_output_negator_typed]
        F] .
  show "Elem (pp_t_unary_complement F)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_unary_complement_in_domain[OF F] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "(pp_t_closed_den pp_t_unary_output_negator \<acute> F)
        \<acute> p
      = pp_t_unary_complement F \<acute> p"
    unfolding pp_t_closed_den_def
      pp_t_unary_output_negator_def
      pp_t_unary_complement_apply[OF p]
      pp_t_complement_def
    using F p
    by (simp add: Lambda_app)
qed

lemma pp_t_unary_complement_congruence:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and FG:
      "pp_t_eqv pp_t_one_context_unary_type w F G"
  shows "pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_unary_complement F) (pp_t_unary_complement G)"
proof -
  let ?N = "pp_t_closed_den pp_t_unary_output_negator"
  have N:
      "Elem ?N
        (pp_t_domain
          (pp_t_one_context_unary_type
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_t_unary_output_negator_typed] .
  have NN:
      "pp_t_eqv
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type)
        w ?N ?N"
    using pp_t_eqv_reflexive[OF N] .
  have applications:
      "pp_t_eqv pp_t_one_context_unary_type w
        (?N \<acute> F) (?N \<acute> G)"
    using pp_t_app_respects[OF NN F G FG] .
  show ?thesis
    using applications
    by (simp only:
        pp_t_unary_output_negator_apply[OF F]
        pp_t_unary_output_negator_apply[OF G])
qed

lemma pp_t_closed_logical_unary_stock_complement:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w F"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_unary_complement F)"
proof -
  have negator_stock:
      "pp_t_closed_logical_stock
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type) w
        (pp_t_closed_den pp_t_unary_output_negator)"
    using pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical
    by (rule pp_t_closed_logical_stockI)
  have applied:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_closed_den pp_t_unary_output_negator \<acute> F)"
    using pp_t_closed_logical_stock_application_closed[
      OF negator_stock stock] .
  show ?thesis
    using applied
    by (simp only: pp_t_unary_output_negator_apply[OF F])
qed

theorem pp_t_closed_logical_unary_stock_complement_iff:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_unary_complement F)
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      pp_t_one_context_unary_type w F"
proof
  assume complement:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_unary_complement F)"
  have twice:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_unary_complement (pp_t_unary_complement F))"
    using pp_t_closed_logical_unary_stock_complement[
      OF pp_t_unary_complement_in_domain[OF F] complement] .
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w F"
    using twice
    unfolding pp_t_unary_complement_involution[OF F] .
next
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w F"
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_unary_complement F)"
    using pp_t_closed_logical_unary_stock_complement[
      OF F stock] .
qed

definition
  pp_t_complemented_symmetrized_singleton_family_builder :: oterm
where
  "pp_t_complemented_symmetrized_singleton_family_builder =
    Lam Prop
      (Lam Prop
        (Neg
          (Disj
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
            (\<box>\<^sub>o
              ((Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 1))))))"

lemma pp_t_complemented_symmetrized_singleton_family_builder_typed:
  "[] \<turnstile>
    pp_t_complemented_symmetrized_singleton_family_builder :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  unfolding
    pp_t_complemented_symmetrized_singleton_family_builder_def
  apply (rule has_type.Lam)
  apply (rule has_type.Lam)
  apply (rule has_type.Neg)
  apply (rule has_type.Disj)
   apply (rule typed_ObjBox)
   apply (rule has_type.Conj)
    apply (rule has_type.Imp)
     apply (rule has_type.Var)
     apply simp
    apply (rule has_type.Var)
    apply simp
   apply (rule has_type.Imp)
    apply (rule has_type.Var)
    apply simp
   apply (rule has_type.Var)
   apply simp
  apply (rule typed_ObjBox)
  apply (rule has_type.Conj)
   apply (rule has_type.Imp)
    apply (rule has_type.Var)
    apply simp
   apply (rule has_type.Neg)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Imp)
   apply (rule has_type.Neg)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Var)
  apply simp
  done

lemma pp_t_complemented_symmetrized_singleton_family_builder_logical:
  "pp_logical_vocabulary
    pp_t_complemented_symmetrized_singleton_family_builder"
  by (simp add:
      pp_t_complemented_symmetrized_singleton_family_builder_def
      pp_logical_vocabulary_def)

abbreviation
  pp_t_complemented_symmetrized_singleton_family_at ::
    "ZF \<Rightarrow> ZF"
where
  "pp_t_complemented_symmetrized_singleton_family_at p \<equiv>
    pp_t_closed_den
      pp_t_complemented_symmetrized_singleton_family_builder
      \<acute> p"

lemma pp_t_complemented_symmetrized_singleton_family_at_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem
    (pp_t_complemented_symmetrized_singleton_family_at p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed]
      p] .

lemma pp_t_complemented_symmetrized_singleton_family_at_eq:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_complemented_symmetrized_singleton_family_at p =
    pp_t_unary_complement
      (pp_t_symmetrized_singleton_family_at p)"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_complemented_symmetrized_singleton_family_at p)
      (pp_t_domain pp_t_one_context_unary_type)"
    using
      pp_t_complemented_symmetrized_singleton_family_at_in_domain[
        OF p] .
  show "Elem
      (pp_t_unary_complement
        (pp_t_symmetrized_singleton_family_at p))
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_unary_complement_in_domain[
      OF pp_t_symmetrized_singleton_family_at_in_domain[OF p]] .
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  show "pp_t_complemented_symmetrized_singleton_family_at p \<acute> q =
      pp_t_unary_complement
        (pp_t_symmetrized_singleton_family_at p) \<acute> q"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_complemented_symmetrized_singleton_family_at p \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF
          pp_t_complemented_symmetrized_singleton_family_at_in_domain[
            OF p]
          q] .
    show "Elem
        (pp_t_unary_complement
          (pp_t_symmetrized_singleton_family_at p) \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_unary_complement_in_domain[
          OF pp_t_symmetrized_singleton_family_at_in_domain[OF p]]
          q] .
    fix w
    have complemented:
        "pp_t_holds
          (pp_t_complemented_symmetrized_singleton_family_at p
            \<acute> q) w
        \<longleftrightarrow>
        \<not> (pp_t_eqv Prop w q p
          \<or> pp_t_eqv Prop w q (pp_t_complement p))"
      unfolding
        pp_t_complemented_symmetrized_singleton_family_builder_def
        pp_t_closed_den_def
      using p q
      by (simp add: Lambda_app pp_t_eval_ObjBox_holds
          pp_t_prop_eqv_truth_iff pp_t_complement_def
          prefix_def; blast)
    have symmetrized:
        "pp_t_holds
          (pp_t_unary_complement
            (pp_t_symmetrized_singleton_family_at p) \<acute> q) w
        \<longleftrightarrow>
        \<not> (pp_t_eqv Prop w q p
          \<or> pp_t_eqv Prop w q (pp_t_complement p))"
      unfolding pp_t_unary_complement_apply[OF q]
      using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF p q, of w]
      by simp
    show "pp_t_holds
          (pp_t_complemented_symmetrized_singleton_family_at p
            \<acute> q) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_unary_complement
            (pp_t_symmetrized_singleton_family_at p) \<acute> q) w"
      using complemented symmetrized by blast
  qed
qed

lemma
  pp_t_complemented_symmetrized_singleton_family_at_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_complemented_symmetrized_singleton_family_at p
        \<acute> q) w
    \<longleftrightarrow>
    \<not> (pp_t_eqv Prop w q p
      \<or> pp_t_eqv Prop w q (pp_t_complement p))"
  unfolding
    pp_t_complemented_symmetrized_singleton_family_at_eq[OF p]
    pp_t_unary_complement_apply[OF q]
  using pp_t_symmetrized_singleton_family_at_apply_holds[
    OF p q, of w]
  by simp

lemma
  pp_t_complemented_symmetrized_singleton_family_stock_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_complemented_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_symmetrized_singleton_family_at p)"
  unfolding
    pp_t_complemented_symmetrized_singleton_family_at_eq[OF p]
  using pp_t_closed_logical_unary_stock_complement_iff[
    OF pp_t_symmetrized_singleton_family_at_in_domain[OF p],
    of w] .

lemma pp_t_complemented_symmetrized_probe_eq_symmetrized_probe:
  "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_symmetrized_singleton_family_builder"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_complemented_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  show "Elem
      (pp_t_family_probe_for_stock
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_complemented_symmetrized_singleton_family_builder
        \<acute> p
      =
      pp_t_family_probe_for_stock
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_symmetrized_singleton_family_builder
        \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_complemented_symmetrized_singleton_family_builder
          \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible]
          p] .
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_symmetrized_singleton_family_builder
          \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible]
          p] .
    fix w
    show "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_complemented_symmetrized_singleton_family_builder
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_symmetrized_singleton_family_builder
            \<acute> p) w"
      using pp_t_family_probe_for_stock_apply_holds[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible p,
          of w]
        pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible p,
          of w]
        pp_t_complemented_symmetrized_singleton_family_stock_iff[
          OF p, of w]
      by blast
  qed
qed

section \<open>Absence of complemented-family collisions\<close>

lemma
  pp_t_symmetrized_singleton_aut_even_false_parity_not_in_stock:
  "\<not> pp_t_closed_logical_stock
    pp_t_one_context_unary_type []
    (pp_t_symmetrized_singleton_family_at
      (pp_t_aut Prop pp_t_even_false_parity))"
proof
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity))"
  obtain M where M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and family_M:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity))
        (pp_t_closed_den M)"
    using stock
    unfolding pp_t_closed_logical_stock_def
    by blast
  have aut_parity:
      "Elem (pp_t_aut Prop pp_t_even_false_parity)
        (pp_t_domain Prop)"
    using pp_t_aut_in_domain[
      OF pp_t_even_false_parity_in_domain] .
  have family_domain:
      "Elem
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity))
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_symmetrized_singleton_family_at_in_domain[
      OF aut_parity] .
  have M_domain:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have family_eq_M:
      "pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)
        = pp_t_closed_den M"
    using pp_t_root_eqv_imp_eq[
      OF family_domain M_domain family_M] .
  have family_fixed:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_symmetrized_singleton_family_at
            (pp_t_aut Prop pp_t_even_false_parity))
        =
        pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)"
    unfolding family_eq_M
    using pp_t_closed_logical_den_aut_fixed[
      OF M_typed M_logical] .
  have aut_twice:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_symmetrized_singleton_family_at
            (pp_t_aut Prop pp_t_even_false_parity))
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
  proof -
    have first:
        "pp_t_aut pp_t_one_context_unary_type
            (pp_t_symmetrized_singleton_family_at
              pp_t_even_false_parity)
          =
          pp_t_symmetrized_singleton_family_at
            (pp_t_aut Prop pp_t_even_false_parity)"
      by (rule pp_t_aut_symmetrized_singleton_at)
    have twice:
        "pp_t_aut pp_t_one_context_unary_type
            (pp_t_aut pp_t_one_context_unary_type
              (pp_t_symmetrized_singleton_family_at
                pp_t_even_false_parity))
          =
          pp_t_symmetrized_singleton_family_at
            pp_t_even_false_parity"
      using pp_t_aut_involution[
        OF pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_even_false_parity_in_domain]] .
    show ?thesis
      using arg_cong[
        OF first,
        of "pp_t_aut pp_t_one_context_unary_type"]
        twice by simp
  qed
  have equality:
      "pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity
        =
        pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)"
    using aut_twice family_fixed by simp
  have fixed:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_symmetrized_singleton_family_at
            pp_t_even_false_parity)
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
    unfolding pp_t_aut_symmetrized_singleton_at
    using equality by simp
  show False
    using
      pp_t_symmetrized_singleton_even_false_parity_not_fixed
      fixed by contradiction
qed

lemma
  pp_t_complemented_symmetrized_probe_has_no_root_collision:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type []
    (pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder)
    (pp_t_complemented_symmetrized_singleton_family_at p)"
proof
  let ?q = "pp_t_even_false_parity"
  let ?r = "pp_t_aut Prop pp_t_even_false_parity"
  let ?P =
    "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder"
  assume collision:
      "pp_t_eqv pp_t_one_context_unary_type []
        ?P
        (pp_t_complemented_symmetrized_singleton_family_at p)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_even_false_parity_in_domain)
  have r: "Elem ?r (pp_t_domain Prop)"
    using pp_t_aut_in_domain[OF q] .
  have P_domain:
      "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  have Bp_domain:
      "Elem
        (pp_t_complemented_symmetrized_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using
      pp_t_complemented_symmetrized_singleton_family_at_in_domain[
        OF p] .
  have equality:
      "?P =
        pp_t_complemented_symmetrized_singleton_family_at p"
    using pp_t_root_eqv_imp_eq[
      OF P_domain Bp_domain collision] .
  have Pq_false: "\<not> pp_t_holds (?P \<acute> ?q) []"
  proof -
    have probe_eq:
        "?P =
        pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_symmetrized_singleton_family_builder"
      by (rule
        pp_t_complemented_symmetrized_probe_eq_symmetrized_probe)
    show ?thesis
      unfolding probe_eq
      using pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible q,
          of "[]"]
        pp_t_symmetrized_singleton_even_false_parity_not_in_stock
      by blast
  qed
  have Pr_false: "\<not> pp_t_holds (?P \<acute> ?r) []"
  proof -
    have probe_eq:
        "?P =
        pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_symmetrized_singleton_family_builder"
      by (rule
        pp_t_complemented_symmetrized_probe_eq_symmetrized_probe)
    show ?thesis
      unfolding probe_eq
      using pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible r,
          of "[]"]
        pp_t_symmetrized_singleton_aut_even_false_parity_not_in_stock
      by blast
  qed
  have q_pair:
      "pp_t_eqv Prop [] ?q p
        \<or> pp_t_eqv Prop [] ?q (pp_t_complement p)"
    using Pq_false
      pp_t_complemented_symmetrized_singleton_family_at_apply_holds[
        OF p q, of "[]"]
    unfolding equality
    by blast
  have r_pair:
      "pp_t_eqv Prop [] ?r p
        \<or> pp_t_eqv Prop [] ?r (pp_t_complement p)"
    using Pr_false
      pp_t_complemented_symmetrized_singleton_family_at_apply_holds[
        OF p r, of "[]"]
    unfolding equality
    by blast
  have q_eq:
      "?q = p \<or> ?q = pp_t_complement p"
    using q_pair
      pp_t_root_eqv_iff_eq[OF q p]
      pp_t_root_eqv_iff_eq[
        OF q pp_t_complement_in_domain]
    by blast
  have r_eq:
      "?r = p \<or> ?r = pp_t_complement p"
    using r_pair
      pp_t_root_eqv_iff_eq[OF r p]
      pp_t_root_eqv_iff_eq[
        OF r pp_t_complement_in_domain]
    by blast
  from q_eq show False
  proof
    assume q_p: "?q = p"
    from r_eq show False
    proof
      assume r_p: "?r = p"
      have "?r = ?q" using q_p r_p by simp
      then show False
        using pp_t_aut_even_false_parity_ne by contradiction
    next
      assume r_cp: "?r = pp_t_complement p"
      have "?r = pp_t_complement ?q"
        using q_p r_cp by simp
      then show False
        using pp_t_aut_even_false_parity_ne_complement
        by contradiction
    qed
  next
    assume q_cp: "?q = pp_t_complement p"
    from r_eq show False
    proof
      assume r_p: "?r = p"
      have "?r = pp_t_complement ?q"
        using pp_t_complement_involution[OF p]
          q_cp r_p by simp
      then show False
        using pp_t_aut_even_false_parity_ne_complement
        by contradiction
    next
      assume r_cp: "?r = pp_t_complement p"
      have "?r = ?q" using q_cp r_cp by simp
      then show False
        using pp_t_aut_even_false_parity_ne by contradiction
    qed
  qed
qed

lemma pp_t_complemented_symmetrized_probe_cone_natural:
  "pp_t_cone_rel pp_t_one_context_unary_type s
    (pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder)
    (pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder)"
proof -
  have builder:
      "pp_t_cone_rel
        (pp_t_one_context_classifier_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type) s
        (pp_t_closed_den
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder))
        (pp_t_closed_den
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder))"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF pp_t_family_probe_builder_typed[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed]
        pp_t_family_probe_builder_logical[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_logical]]
      .
  have classifier:
      "pp_t_cone_rel pp_t_one_context_classifier_type s
        pp_t_old_unary_stock_classifier
        pp_t_old_unary_stock_classifier"
    by (rule pp_t_old_unary_stock_classifier_cone_natural)
  have applied:
      "pp_t_cone_rel pp_t_one_context_unary_type s
        (pp_t_closed_den
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder)
          \<acute> pp_t_old_unary_stock_classifier)
        (pp_t_closed_den
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder)
          \<acute> pp_t_old_unary_stock_classifier)"
    using builder classifier
      pp_t_old_unary_stock_classifier_in_domain by auto
  show ?thesis
    using applied
    by (simp only: pp_t_family_probe_for_stock_def
        pp_t_old_unary_stock_classifier_def)
qed

theorem
  pp_t_complemented_symmetrized_probe_has_no_collision:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder)
    (pp_t_complemented_symmetrized_singleton_family_at p)"
proof
  let ?P =
    "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder"
  let ?v = "pp_t_cone_view w p"
  assume collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        ?P
        (pp_t_complemented_symmetrized_singleton_family_at p)"
  have v: "Elem ?v (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have P_domain:
      "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  have Bp_domain:
      "Elem
        (pp_t_complemented_symmetrized_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using
      pp_t_complemented_symmetrized_singleton_family_at_in_domain[
        OF p] .
  have Bv_domain:
      "Elem
        (pp_t_complemented_symmetrized_singleton_family_at ?v)
        (pp_t_domain pp_t_one_context_unary_type)"
    using
      pp_t_complemented_symmetrized_singleton_family_at_in_domain[
        OF v] .
  have P_cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w ?P ?P"
    by (rule pp_t_complemented_symmetrized_probe_cone_natural)
  have B_cone:
      "pp_t_cone_rel pp_t_one_context_unary_type w
        (pp_t_complemented_symmetrized_singleton_family_at p)
        (pp_t_complemented_symmetrized_singleton_family_at ?v)"
    using pp_t_logical_family_at_cone_related[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_complemented_symmetrized_singleton_family_builder_logical
        p] .
  have collision_root:
      "pp_t_eqv pp_t_one_context_unary_type []
        ?P
        (pp_t_complemented_symmetrized_singleton_family_at ?v)"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF P_domain P_domain Bp_domain Bv_domain P_cone B_cone,
      of "[]"]
      collision by simp
  show False
    using
      pp_t_complemented_symmetrized_probe_has_no_root_collision[
        OF v]
      collision_root by contradiction
qed

theorem
  pp_t_complemented_symmetrized_probe_stabilizes_after_one_enlargement:
  "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_complemented_symmetrized_singleton_family_builder)
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder"
proof -
  have exact:
      "pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_complemented_symmetrized_singleton_family_builder)
          pp_t_complemented_symmetrized_singleton_family_builder
        =
        pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_complemented_symmetrized_singleton_family_builder
      \<longleftrightarrow>
      (\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_complemented_symmetrized_singleton_family_builder)
          (pp_t_closed_den
            pp_t_complemented_symmetrized_singleton_family_builder
            \<acute> p)
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den
            pp_t_complemented_symmetrized_singleton_family_builder
            \<acute> p))"
    using pp_t_family_probe_stabilizes_iff_collisions_absorbed[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible] .
  show ?thesis
    using exact
      pp_t_complemented_symmetrized_probe_has_no_collision
    by blast
qed

section \<open>Closure under negation of the forced probe\<close>

definition pp_t_symmetrized_closed_stock_probe :: ZF where
  "pp_t_symmetrized_closed_stock_probe =
    pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_symmetrized_closed_stock_probe_in_domain:
  "Elem pp_t_symmetrized_closed_stock_probe
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_symmetrized_closed_stock_probe_def
  using pp_t_family_probe_for_stock_in_domain[
    OF pp_t_symmetrized_singleton_family_builder_typed
      pp_t_closed_logical_stock_admissible] .

definition pp_t_symmetrized_negation_closed_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_symmetrized_negation_closed_stock w X \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w X
    \<or>
    pp_t_eqv pp_t_one_context_unary_type w
      pp_t_symmetrized_closed_stock_probe X
    \<or>
    pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_unary_complement
        pp_t_symmetrized_closed_stock_probe) X"

lemma pp_t_symmetrized_negation_closed_stock_complement:
  assumes X:
      "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock:
      "pp_t_symmetrized_negation_closed_stock w X"
  shows "pp_t_symmetrized_negation_closed_stock w
    (pp_t_unary_complement X)"
proof -
  let ?P = "pp_t_symmetrized_closed_stock_probe"
  have P:
      "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  from stock consider
      (old) "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w X"
    | (probe)
        "pp_t_eqv pp_t_one_context_unary_type w ?P X"
    | (complement)
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement ?P) X"
    unfolding pp_t_symmetrized_negation_closed_stock_def
    by blast
  then show ?thesis
  proof cases
    case old
    have "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_unary_complement X)"
      by (rule pp_t_closed_logical_unary_stock_complement[
        OF X old])
    then show ?thesis
      unfolding pp_t_symmetrized_negation_closed_stock_def
      by blast
  next
    case probe
    have "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_unary_complement ?P)
        (pp_t_unary_complement X)"
      by (rule pp_t_unary_complement_congruence[
        OF P X probe])
    then show ?thesis
      unfolding pp_t_symmetrized_negation_closed_stock_def
      by blast
  next
    case complement
    have transformed:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement
            (pp_t_unary_complement ?P))
          (pp_t_unary_complement X)"
      by (rule pp_t_unary_complement_congruence[
        OF pp_t_unary_complement_in_domain[OF P]
          X complement])
    have "pp_t_eqv pp_t_one_context_unary_type w
        ?P (pp_t_unary_complement X)"
      using transformed
      by (simp only: pp_t_unary_complement_involution[OF P])
    then show ?thesis
      unfolding pp_t_symmetrized_negation_closed_stock_def
      by blast
  qed
qed

lemma pp_t_symmetrized_negation_closed_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_symmetrized_negation_closed_stock"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)"
    by (rule pp_t_closed_logical_stock_admissible)
  have probe:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_one_context_unary_type w
          pp_t_symmetrized_closed_stock_probe X)"
    by (rule pp_t_eqv_class_predicate_admissible[
      OF pp_t_symmetrized_closed_stock_probe_in_domain])
  have complement:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe) X)"
    by (rule pp_t_eqv_class_predicate_admissible[
      OF pp_t_unary_complement_in_domain[
        OF pp_t_symmetrized_closed_stock_probe_in_domain]])
  show ?thesis
    using old probe complement
    unfolding pp_t_predicate_admissible_def
      pp_t_symmetrized_negation_closed_stock_def
    by blast
qed

lemma pp_t_symmetrized_singleton_family_diagonal:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
    (pp_t_symmetrized_singleton_family_at p \<acute> p) w"
  using pp_t_symmetrized_singleton_family_at_apply_holds[
      OF p p, of w]
    pp_t_eqv_reflexive[OF p]
  by blast

lemma pp_t_symmetrized_closed_stock_probe_collision_absorbed:
  assumes p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_symmetrized_closed_stock_probe
        (pp_t_symmetrized_singleton_family_at p)"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_symmetrized_singleton_family_at p)"
proof -
  have raw:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock
            pp_t_one_context_unary_type)
          pp_t_symmetrized_singleton_family_builder)
        (pp_t_closed_den
          pp_t_symmetrized_singleton_family_builder \<acute> p)"
    using collision
    unfolding pp_t_symmetrized_closed_stock_probe_def .
  show ?thesis
    by (rule pp_t_family_probe_collision_absorbed[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible
        pp_t_symmetrized_singleton_family_diagonal
        p raw])
qed

lemma pp_t_complemented_closed_stock_probe_eq:
  "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_symmetrized_closed_stock_probe"
  unfolding pp_t_symmetrized_closed_stock_probe_def
  using
    pp_t_complemented_symmetrized_probe_eq_symmetrized_probe
  by simp

lemma
  pp_t_symmetrized_family_in_negation_closed_stock_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_symmetrized_negation_closed_stock w
      (pp_t_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w
      (pp_t_symmetrized_singleton_family_at p)"
proof
  let ?P = "pp_t_symmetrized_closed_stock_probe"
  let ?Bp = "pp_t_symmetrized_singleton_family_at p"
  assume enlarged:
      "pp_t_symmetrized_negation_closed_stock w ?Bp"
  have P:
      "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  have Bp:
      "Elem ?Bp (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[
      OF p])
  from enlarged consider
      (old) "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w ?Bp"
    | (probe) "pp_t_eqv pp_t_one_context_unary_type w ?P ?Bp"
    | (complement)
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement ?P) ?Bp"
    unfolding pp_t_symmetrized_negation_closed_stock_def
    by blast
  then show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w ?Bp"
  proof cases
    case old
    then show ?thesis .
  next
    case probe
    show ?thesis
      by (rule
        pp_t_symmetrized_closed_stock_probe_collision_absorbed[
          OF p probe])
  next
    case complement
    have transformed:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement
            (pp_t_unary_complement ?P))
          (pp_t_unary_complement ?Bp)"
      using pp_t_unary_complement_congruence[
        OF pp_t_unary_complement_in_domain[OF P]
          Bp complement] .
    have forbidden:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock
              pp_t_one_context_unary_type)
            pp_t_complemented_symmetrized_singleton_family_builder)
          (pp_t_complemented_symmetrized_singleton_family_at p)"
    proof -
      have left:
          "pp_t_family_probe_for_stock
              (pp_t_closed_logical_stock
                pp_t_one_context_unary_type)
              pp_t_complemented_symmetrized_singleton_family_builder
            = ?P"
        unfolding pp_t_symmetrized_closed_stock_probe_def
        using
          pp_t_complemented_symmetrized_probe_eq_symmetrized_probe
        by simp
      show ?thesis
        unfolding left
          pp_t_complemented_symmetrized_singleton_family_at_eq[
            OF p]
        using transformed
        by (simp only: pp_t_unary_complement_involution[OF P])
    qed
    show ?thesis
      using pp_t_complemented_symmetrized_probe_has_no_collision[
        OF p, of w]
        forbidden by contradiction
  qed
next
  assume old:
      "pp_t_closed_logical_stock pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at p)"
  show "pp_t_symmetrized_negation_closed_stock w
      (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_symmetrized_negation_closed_stock_def
    using old by blast
qed

lemma
  pp_t_complemented_family_in_negation_closed_stock_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_symmetrized_negation_closed_stock w
      (pp_t_complemented_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w
      (pp_t_complemented_symmetrized_singleton_family_at p)"
proof
  let ?P = "pp_t_symmetrized_closed_stock_probe"
  let ?Bp = "pp_t_symmetrized_singleton_family_at p"
  let ?Cp =
    "pp_t_complemented_symmetrized_singleton_family_at p"
  assume enlarged:
      "pp_t_symmetrized_negation_closed_stock w ?Cp"
  have P:
      "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  have Bp:
      "Elem ?Bp (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[
      OF p])
  have Cp:
      "Elem ?Cp (pp_t_domain pp_t_one_context_unary_type)"
    by (rule
      pp_t_complemented_symmetrized_singleton_family_at_in_domain[
        OF p])
  from enlarged consider
      (old) "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w ?Cp"
    | (probe) "pp_t_eqv pp_t_one_context_unary_type w ?P ?Cp"
    | (complement)
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement ?P) ?Cp"
    unfolding pp_t_symmetrized_negation_closed_stock_def
    by blast
  then show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w ?Cp"
  proof cases
    case old
    then show ?thesis .
  next
    case probe
    have forbidden:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock
            (pp_t_closed_logical_stock
              pp_t_one_context_unary_type)
            pp_t_complemented_symmetrized_singleton_family_builder)
          ?Cp"
      using probe
      unfolding pp_t_complemented_closed_stock_probe_eq .
    show ?thesis
      using pp_t_complemented_symmetrized_probe_has_no_collision[
        OF p, of w]
        forbidden by contradiction
  next
    case complement
    have transformed:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_unary_complement
            (pp_t_unary_complement ?P))
          (pp_t_unary_complement ?Cp)"
      using pp_t_unary_complement_congruence[
        OF pp_t_unary_complement_in_domain[OF P]
          Cp complement] .
    have complement_Cp:
        "pp_t_unary_complement ?Cp = ?Bp"
      unfolding
        pp_t_complemented_symmetrized_singleton_family_at_eq[
          OF p]
      using pp_t_unary_complement_involution[OF Bp] by simp
    have collision:
        "pp_t_eqv pp_t_one_context_unary_type w ?P ?Bp"
      using transformed
        pp_t_unary_complement_involution[OF P]
        complement_Cp
      by simp
    have Bp_old:
        "pp_t_closed_logical_stock
          pp_t_one_context_unary_type w ?Bp"
      by (rule
        pp_t_symmetrized_closed_stock_probe_collision_absorbed[
          OF p collision])
    show ?thesis
      unfolding
        pp_t_complemented_symmetrized_singleton_family_at_eq[
          OF p]
      using pp_t_closed_logical_unary_stock_complement[
        OF Bp Bp_old] .
  qed
next
  assume old:
      "pp_t_closed_logical_stock pp_t_one_context_unary_type w
        (pp_t_complemented_symmetrized_singleton_family_at p)"
  show "pp_t_symmetrized_negation_closed_stock w
      (pp_t_complemented_symmetrized_singleton_family_at p)"
    unfolding pp_t_symmetrized_negation_closed_stock_def
    using old by blast
qed

theorem
  pp_t_symmetrized_probe_stable_under_negation_closure:
  "pp_t_family_probe_for_stock
      pp_t_symmetrized_negation_closed_stock
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_symmetrized_closed_stock_probe"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock
        pp_t_symmetrized_negation_closed_stock
        pp_t_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_negation_closed_stock_admissible] .
  show "Elem pp_t_symmetrized_closed_stock_probe
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock
        pp_t_symmetrized_negation_closed_stock
        pp_t_symmetrized_singleton_family_builder \<acute> p
      =
      pp_t_symmetrized_closed_stock_probe \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          pp_t_symmetrized_negation_closed_stock
          pp_t_symmetrized_singleton_family_builder \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_negation_closed_stock_admissible]
          p] .
    show "Elem (pp_t_symmetrized_closed_stock_probe \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_closed_stock_probe_in_domain p] .
    fix w
    show "pp_t_holds
          (pp_t_family_probe_for_stock
            pp_t_symmetrized_negation_closed_stock
            pp_t_symmetrized_singleton_family_builder \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_symmetrized_closed_stock_probe \<acute> p) w"
      unfolding pp_t_symmetrized_closed_stock_probe_def
      using pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_negation_closed_stock_admissible p,
          of w]
        pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible p,
          of w]
        pp_t_symmetrized_family_in_negation_closed_stock_iff[
          OF p, of w]
      by blast
  qed
qed

theorem
  pp_t_complemented_probe_stable_under_negation_closure:
  "pp_t_family_probe_for_stock
      pp_t_symmetrized_negation_closed_stock
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_symmetrized_closed_stock_probe"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock
        pp_t_symmetrized_negation_closed_stock
        pp_t_complemented_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_negation_closed_stock_admissible] .
  show "Elem pp_t_symmetrized_closed_stock_probe
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock
        pp_t_symmetrized_negation_closed_stock
        pp_t_complemented_symmetrized_singleton_family_builder
        \<acute> p
      =
      pp_t_symmetrized_closed_stock_probe \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          pp_t_symmetrized_negation_closed_stock
          pp_t_complemented_symmetrized_singleton_family_builder
          \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_negation_closed_stock_admissible]
          p] .
    show "Elem (pp_t_symmetrized_closed_stock_probe \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_closed_stock_probe_in_domain p] .
    fix w
    show "pp_t_holds
          (pp_t_family_probe_for_stock
            pp_t_symmetrized_negation_closed_stock
            pp_t_complemented_symmetrized_singleton_family_builder
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_symmetrized_closed_stock_probe \<acute> p) w"
      unfolding pp_t_symmetrized_closed_stock_probe_def
      using pp_t_family_probe_for_stock_apply_holds[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_negation_closed_stock_admissible p,
          of w]
        pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible p,
          of w]
        pp_t_complemented_family_in_negation_closed_stock_iff[
          OF p, of w]
        pp_t_complemented_symmetrized_singleton_family_stock_iff[
          OF p, of w]
      by blast
  qed
qed

end
