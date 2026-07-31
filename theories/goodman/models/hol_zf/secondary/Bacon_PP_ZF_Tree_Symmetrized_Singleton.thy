theory Bacon_PP_ZF_Tree_Symmetrized_Singleton
  imports
    Bacon_PP_ZF_Tree_Automorphism_Equivariance
    Bacon_PP_ZF_Tree_Family_View_Definability
begin

section \<open>A view-stable family value outside the closed logical stock\<close>

definition pp_t_complement :: "ZF \<Rightarrow> ZF" where
  "pp_t_complement p =
    pp_t_prop (\<lambda>w. \<not> pp_t_holds p w)"

lemma pp_t_complement_in_domain:
  "Elem (pp_t_complement p) (pp_t_domain Prop)"
  unfolding pp_t_complement_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_complement_holds[simp]:
  "pp_t_holds (pp_t_complement p) w
    \<longleftrightarrow> \<not> pp_t_holds p w"
  by (simp add: pp_t_complement_def)

lemma pp_t_complement_involution:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_complement (pp_t_complement p) = p"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_complement (pp_t_complement p))
      (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  show "Elem p (pp_t_domain Prop)" by (rule p)
  fix w
  show "pp_t_holds (pp_t_complement (pp_t_complement p)) w
      \<longleftrightarrow> pp_t_holds p w"
    by simp
qed

lemma pp_t_cone_view_complement:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_cone_view s (pp_t_complement p) =
    pp_t_complement (pp_t_cone_view s p)"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_cone_view s (pp_t_complement p))
      (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  show "Elem (pp_t_complement (pp_t_cone_view s p))
      (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  fix w
  show "pp_t_holds (pp_t_cone_view s (pp_t_complement p)) w
      \<longleftrightarrow>
      pp_t_holds (pp_t_complement (pp_t_cone_view s p)) w"
    by simp
qed

definition pp_t_symmetrized_singleton_family_builder :: oterm where
  "pp_t_symmetrized_singleton_family_builder =
    Lam Prop
      (Lam Prop
        (Disj
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 1)))))"

lemma pp_t_symmetrized_singleton_family_builder_typed:
  "[] \<turnstile> pp_t_symmetrized_singleton_family_builder :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  unfolding pp_t_symmetrized_singleton_family_builder_def
  apply (rule has_type.Lam)
  apply (rule has_type.Lam)
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

lemma pp_t_symmetrized_singleton_family_builder_logical:
  "pp_logical_vocabulary
    pp_t_symmetrized_singleton_family_builder"
  by (simp add: pp_t_symmetrized_singleton_family_builder_def
      pp_logical_vocabulary_def)

abbreviation pp_t_symmetrized_singleton_family_at ::
    "ZF \<Rightarrow> ZF"
where
  "pp_t_symmetrized_singleton_family_at p \<equiv>
    pp_t_closed_den pp_t_symmetrized_singleton_family_builder \<acute> p"

lemma pp_t_symmetrized_singleton_family_at_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_symmetrized_singleton_family_at p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed] p] .

lemma pp_t_symmetrized_singleton_family_at_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_symmetrized_singleton_family_at p) \<acute> q) w
    \<longleftrightarrow>
    pp_t_eqv Prop w q p
      \<or> pp_t_eqv Prop w q (pp_t_complement p)"
proof -
  have beta:
      "(pp_t_symmetrized_singleton_family_at p) \<acute> q =
        pp_t_eval pp_t_default_constants
          (extend_env q (extend_env p pp_t_closed_env))
          (Disj
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
            (\<box>\<^sub>o
              ((Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 1))))"
    unfolding pp_t_closed_den_def
      pp_t_symmetrized_singleton_family_builder_def
    using p q by (simp add: Lambda_app)
  show ?thesis
    unfolding beta
    by (simp add: pp_t_eval_ObjBox_holds
        pp_t_prop_eqv_truth_iff pp_t_complement_def
        prefix_def; blast)
qed

lemma pp_t_symmetrized_singleton_family_at_complement:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_symmetrized_singleton_family_at (pp_t_complement p) =
    pp_t_symmetrized_singleton_family_at p"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_symmetrized_singleton_family_at (pp_t_complement p))
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_symmetrized_singleton_family_at_in_domain[
      OF pp_t_complement_in_domain] .
  show "Elem (pp_t_symmetrized_singleton_family_at p)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_symmetrized_singleton_family_at_in_domain[OF p] .
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  show "(pp_t_symmetrized_singleton_family_at
          (pp_t_complement p)) \<acute> q
      =
      pp_t_symmetrized_singleton_family_at p \<acute> q"
  proof (rule pp_t_prop_ext)
    show "Elem
        ((pp_t_symmetrized_singleton_family_at
            (pp_t_complement p)) \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_complement_in_domain] q] .
    show "Elem
        (pp_t_symmetrized_singleton_family_at p \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_singleton_family_at_in_domain[OF p] q] .
    fix w
    have left:
        "pp_t_holds
          ((pp_t_symmetrized_singleton_family_at
              (pp_t_complement p)) \<acute> q) w
        =
        (pp_t_eqv Prop w q (pp_t_complement p)
          \<or> pp_t_eqv Prop w q p)"
      using pp_t_symmetrized_singleton_family_at_apply_holds[
          OF pp_t_complement_in_domain[of p] q, of w]
        pp_t_complement_involution[OF p]
      by simp
    have right:
        "pp_t_holds
          (pp_t_symmetrized_singleton_family_at p \<acute> q) w
        =
        (pp_t_eqv Prop w q p
          \<or> pp_t_eqv Prop w q (pp_t_complement p))"
      using pp_t_symmetrized_singleton_family_at_apply_holds[
          OF p q, of w] .
    show "pp_t_holds
          ((pp_t_symmetrized_singleton_family_at
              (pp_t_complement p)) \<acute> q) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_symmetrized_singleton_family_at p \<acute> q) w"
      using left right by blast
  qed
qed

definition pp_t_even_false_parity :: ZF where
  "pp_t_even_false_parity =
    pp_t_prop
      (\<lambda>w. even (length (filter (\<lambda>b. \<not> b) w)))"

lemma pp_t_even_false_parity_in_domain:
  "Elem pp_t_even_false_parity (pp_t_domain Prop)"
  unfolding pp_t_even_false_parity_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_even_false_parity_holds[simp]:
  "pp_t_holds pp_t_even_false_parity w
    \<longleftrightarrow>
    even (length (filter (\<lambda>b. \<not> b) w))"
  by (simp add: pp_t_even_false_parity_def)

lemma pp_t_even_false_parity_view:
  "pp_t_cone_view s pp_t_even_false_parity =
    (if even (length (filter (\<lambda>b. \<not> b) s))
     then pp_t_even_false_parity
     else pp_t_complement pp_t_even_false_parity)"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_cone_view s pp_t_even_false_parity)
      (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  show "Elem
      (if even (length (filter (\<lambda>b. \<not> b) s))
       then pp_t_even_false_parity
       else pp_t_complement pp_t_even_false_parity)
      (pp_t_domain Prop)"
    using pp_t_even_false_parity_in_domain
      pp_t_complement_in_domain by simp
  fix w
  show "pp_t_holds
        (pp_t_cone_view s pp_t_even_false_parity) w
      \<longleftrightarrow>
      pp_t_holds
        (if even (length (filter (\<lambda>b. \<not> b) s))
         then pp_t_even_false_parity
         else pp_t_complement pp_t_even_false_parity) w"
    by (simp add: filter_append even_add)
qed

lemma pp_t_symmetrized_singleton_even_false_parity_stable:
  "pp_t_family_same_value_on_relative_views
    pp_t_symmetrized_singleton_family_builder []
    pp_t_even_false_parity"
  unfolding pp_t_family_same_value_on_relative_views_def
proof (intro allI)
  fix s
  have root_view:
      "pp_t_cone_view [] pp_t_even_false_parity =
        pp_t_even_false_parity"
    using pp_t_cone_view_empty[
      OF pp_t_even_false_parity_in_domain] .
  have complement_value:
      "pp_t_symmetrized_singleton_family_at
          (pp_t_complement pp_t_even_false_parity)
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
    using pp_t_symmetrized_singleton_family_at_complement[
      OF pp_t_even_false_parity_in_domain] .
  show "pp_t_closed_den
          pp_t_symmetrized_singleton_family_builder
        \<acute> pp_t_cone_view s
          (pp_t_cone_view [] pp_t_even_false_parity)
      =
      pp_t_closed_den
          pp_t_symmetrized_singleton_family_builder
        \<acute> pp_t_cone_view [] pp_t_even_false_parity"
    using root_view pp_t_even_false_parity_view[of s]
      complement_value
    by (cases "even (length (filter (\<lambda>b. \<not> b) s))")
      simp_all
qed

lemma pp_t_aut_even_false_parity_ne:
  "pp_t_aut Prop pp_t_even_false_parity
    \<noteq> pp_t_even_false_parity"
proof
  assume equality:
      "pp_t_aut Prop pp_t_even_false_parity =
        pp_t_even_false_parity"
  have at_true:
      "pp_t_holds
          (pp_t_aut Prop pp_t_even_false_parity) [True]
        =
        pp_t_holds pp_t_even_false_parity [True]"
    using arg_cong[OF equality,
      of "\<lambda>P. pp_t_holds P [True]"] .
  show False
    using at_true
    by (simp add: pp_t_even_false_parity_def)
qed

lemma pp_t_aut_even_false_parity_ne_complement:
  "pp_t_aut Prop pp_t_even_false_parity
    \<noteq> pp_t_complement pp_t_even_false_parity"
proof
  assume equality:
      "pp_t_aut Prop pp_t_even_false_parity =
        pp_t_complement pp_t_even_false_parity"
  have at_root:
      "pp_t_holds
          (pp_t_aut Prop pp_t_even_false_parity) []
        =
        pp_t_holds
          (pp_t_complement pp_t_even_false_parity) []"
    using arg_cong[OF equality,
      of "\<lambda>P. pp_t_holds P []"] .
  show False
    using at_root
    by (simp add: pp_t_even_false_parity_def)
qed

lemma pp_t_even_false_parity_ne_complement_aut:
  "pp_t_even_false_parity
    \<noteq> pp_t_complement
      (pp_t_aut Prop pp_t_even_false_parity)"
proof
  assume equality:
      "pp_t_even_false_parity =
        pp_t_complement
          (pp_t_aut Prop pp_t_even_false_parity)"
  have at_root:
      "pp_t_holds pp_t_even_false_parity []
        =
        pp_t_holds
          (pp_t_complement
            (pp_t_aut Prop pp_t_even_false_parity)) []"
    using arg_cong[OF equality,
      of "\<lambda>P. pp_t_holds P []"] .
  show False
    using at_root
    by (simp add: pp_t_even_false_parity_def)
qed

lemma pp_t_aut_symmetrized_singleton_at:
  "pp_t_aut pp_t_one_context_unary_type
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_false_parity)
    =
    pp_t_symmetrized_singleton_family_at
      (pp_t_aut Prop pp_t_even_false_parity)"
proof -
  let ?B = "pp_t_closed_den
    pp_t_symmetrized_singleton_family_builder"
  let ?p = "pp_t_even_false_parity"
  have ap: "Elem (pp_t_aut Prop ?p) (pp_t_domain Prop)"
    using pp_t_aut_in_domain[
      OF pp_t_even_false_parity_in_domain] .
  have application:
      "pp_t_aut
          (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) ?B
          \<acute> pp_t_aut Prop ?p
        =
        pp_t_aut pp_t_one_context_unary_type
          (?B \<acute> pp_t_aut Prop (pp_t_aut Prop ?p))"
    using pp_t_aut_apply[OF ap] .
  have B_fixed:
      "pp_t_aut
          (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) ?B
        = ?B"
    using pp_t_closed_logical_den_aut_fixed[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical] .
  have p_involution:
      "pp_t_aut Prop (pp_t_aut Prop ?p) = ?p"
    using pp_t_aut_involution[
      OF pp_t_even_false_parity_in_domain] .
  show ?thesis
    using application B_fixed p_involution by simp
qed

lemma pp_t_symmetrized_singleton_at_parity_root:
  "pp_t_holds
    (pp_t_symmetrized_singleton_family_at
      pp_t_even_false_parity
      \<acute> pp_t_even_false_parity) []"
proof -
  have semantic:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity
          \<acute> pp_t_even_false_parity) []
      \<longleftrightarrow>
      pp_t_eqv Prop []
        pp_t_even_false_parity pp_t_even_false_parity
      \<or>
      pp_t_eqv Prop []
        pp_t_even_false_parity
        (pp_t_complement pp_t_even_false_parity)"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
      OF pp_t_even_false_parity_in_domain
        pp_t_even_false_parity_in_domain, of "[]"] .
  have reflexive:
      "pp_t_eqv Prop []
        pp_t_even_false_parity pp_t_even_false_parity"
    using pp_t_eqv_reflexive[
      OF pp_t_even_false_parity_in_domain] .
  show ?thesis
    using semantic reflexive by blast
qed

lemma pp_t_symmetrized_singleton_at_aut_parity_root:
  "\<not> pp_t_holds
    (pp_t_symmetrized_singleton_family_at
      (pp_t_aut Prop pp_t_even_false_parity)
      \<acute> pp_t_even_false_parity) []"
proof -
  have ap:
      "Elem (pp_t_aut Prop pp_t_even_false_parity)
        (pp_t_domain Prop)"
    using pp_t_aut_in_domain[
      OF pp_t_even_false_parity_in_domain] .
  have cap:
      "Elem
        (pp_t_complement
          (pp_t_aut Prop pp_t_even_false_parity))
        (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have parity_ne_aut:
      "pp_t_even_false_parity
        \<noteq> pp_t_aut Prop pp_t_even_false_parity"
  proof
    assume "pp_t_even_false_parity =
      pp_t_aut Prop pp_t_even_false_parity"
    then have "pp_t_aut Prop pp_t_even_false_parity =
      pp_t_even_false_parity"
      by simp
    show False
      using pp_t_aut_even_false_parity_ne
        \<open>pp_t_aut Prop pp_t_even_false_parity =
          pp_t_even_false_parity\<close>
      by contradiction
  qed
  have not_first:
      "\<not> pp_t_eqv Prop []
        pp_t_even_false_parity
        (pp_t_aut Prop pp_t_even_false_parity)"
    using pp_t_root_eqv_iff_eq[
      OF pp_t_even_false_parity_in_domain ap]
      parity_ne_aut
    by blast
  have not_second:
      "\<not> pp_t_eqv Prop []
        pp_t_even_false_parity
        (pp_t_complement
          (pp_t_aut Prop pp_t_even_false_parity))"
    using pp_t_root_eqv_iff_eq[
      OF pp_t_even_false_parity_in_domain cap]
      pp_t_even_false_parity_ne_complement_aut
    by blast
  have semantic:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)
          \<acute> pp_t_even_false_parity) []
      \<longleftrightarrow>
      pp_t_eqv Prop []
        pp_t_even_false_parity
        (pp_t_aut Prop pp_t_even_false_parity)
      \<or>
      pp_t_eqv Prop []
        pp_t_even_false_parity
        (pp_t_complement
          (pp_t_aut Prop pp_t_even_false_parity))"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
      OF ap pp_t_even_false_parity_in_domain, of "[]"] .
  show ?thesis
    using semantic not_first not_second by blast
qed

lemma pp_t_symmetrized_singleton_even_false_parity_not_fixed:
  "pp_t_aut pp_t_one_context_unary_type
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_false_parity)
    \<noteq>
    pp_t_symmetrized_singleton_family_at
      pp_t_even_false_parity"
proof
  assume fixed:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_symmetrized_singleton_family_at
            pp_t_even_false_parity)
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
  have family_eq:
      "pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
    using fixed pp_t_aut_symmetrized_singleton_at by simp
  have application_eq:
      "pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)
          \<acute> pp_t_even_false_parity
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity
          \<acute> pp_t_even_false_parity"
    using arg_cong[OF family_eq,
      of "\<lambda>F. F \<acute> pp_t_even_false_parity"] .
  have at_root:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop pp_t_even_false_parity)
          \<acute> pp_t_even_false_parity) []
      =
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity
          \<acute> pp_t_even_false_parity) []"
    using arg_cong[OF application_eq,
      of "\<lambda>P. pp_t_holds P []"] .
  show False
    using at_root
      pp_t_symmetrized_singleton_at_aut_parity_root
      pp_t_symmetrized_singleton_at_parity_root
    by blast
qed

lemma pp_t_symmetrized_singleton_even_false_parity_not_in_stock:
  "\<not> pp_t_closed_logical_stock
    pp_t_one_context_unary_type []
    (pp_t_symmetrized_singleton_family_at
      pp_t_even_false_parity)"
proof
  assume stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity)"
  obtain M where M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and family_M:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity)
        (pp_t_closed_den M)"
    using stock
    unfolding pp_t_closed_logical_stock_def
    by blast
  have family_domain:
      "Elem
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_symmetrized_singleton_family_at_in_domain[
      OF pp_t_even_false_parity_in_domain] .
  have M_domain:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have family_eq_M:
      "pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity
        =
        pp_t_closed_den M"
    using pp_t_root_eqv_imp_eq[
      OF family_domain M_domain family_M] .
  have M_fixed:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_closed_den M)
        =
        pp_t_closed_den M"
    using pp_t_closed_logical_den_aut_fixed[
      OF M_typed M_logical] .
  have family_fixed:
      "pp_t_aut pp_t_one_context_unary_type
          (pp_t_symmetrized_singleton_family_at
            pp_t_even_false_parity)
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_false_parity"
    using M_fixed unfolding family_eq_M .
  show False
    using
      pp_t_symmetrized_singleton_even_false_parity_not_fixed
      family_fixed by blast
qed

theorem pp_t_symmetrized_singleton_not_view_complete:
  "\<not> pp_t_family_view_complete
      pp_t_symmetrized_singleton_family_builder"
  unfolding pp_t_family_view_complete_def
  using pp_t_even_false_parity_in_domain
    pp_t_symmetrized_singleton_even_false_parity_stable
    pp_t_symmetrized_singleton_even_false_parity_not_in_stock
  by blast

end
