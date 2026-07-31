theory Bacon_PP_ZF_Tree_Boolean_Probe_Canonical_Cases
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Collision.Bacon_PP_ZF_Tree_Boolean_Probe_Collision
begin

section \<open>Automorphism invariance of the Boolean probe stock\<close>

lemma pp_t_closed_logical_stock_aut_iff:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_closed_logical_stock \<sigma> w (pp_t_aut \<sigma> x)
    \<longleftrightarrow>
    pp_t_closed_logical_stock \<sigma> (pp_t_root_swap w) x"
proof
  assume stock:
      "pp_t_closed_logical_stock \<sigma> w (pp_t_aut \<sigma> x)"
  then obtain M where typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and related:
      "pp_t_eqv \<sigma> w
        (pp_t_aut \<sigma> x) (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have den: "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have fixed:
      "pp_t_aut \<sigma> (pp_t_closed_den M) = pp_t_closed_den M"
    by (rule pp_t_closed_logical_den_aut_fixed[OF typed logical])
  have aut_related:
      "pp_t_eqv \<sigma> w
        (pp_t_aut \<sigma> x)
        (pp_t_aut \<sigma> (pp_t_closed_den M))"
    using related fixed by simp
  have base_related:
      "pp_t_eqv \<sigma> (pp_t_root_swap w)
        x (pp_t_closed_den M)"
    using pp_t_aut_eqv_iff[OF x den, of w] aut_related by blast
  show "pp_t_closed_logical_stock \<sigma>
      (pp_t_root_swap w) x"
    unfolding pp_t_closed_logical_stock_def
    using x typed logical base_related by blast
next
  assume stock:
      "pp_t_closed_logical_stock \<sigma> (pp_t_root_swap w) x"
  then obtain M where typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and related:
      "pp_t_eqv \<sigma> (pp_t_root_swap w)
        x (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have den: "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have fixed:
      "pp_t_aut \<sigma> (pp_t_closed_den M) = pp_t_closed_den M"
    by (rule pp_t_closed_logical_den_aut_fixed[OF typed logical])
  have aut_related:
      "pp_t_eqv \<sigma> w
        (pp_t_aut \<sigma> x)
        (pp_t_aut \<sigma> (pp_t_closed_den M))"
    using pp_t_aut_eqv_iff[OF x den, of w] related by blast
  have target:
      "pp_t_eqv \<sigma> w
        (pp_t_aut \<sigma> x) (pp_t_closed_den M)"
    using aut_related fixed by simp
  show "pp_t_closed_logical_stock \<sigma> w (pp_t_aut \<sigma> x)"
    unfolding pp_t_closed_logical_stock_def
    using pp_t_aut_in_domain[OF x] typed logical target by blast
qed

lemma pp_t_aut_fixed_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and f_fixed:
      "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f = f"
    and x_fixed: "pp_t_aut \<sigma> x = x"
  shows "pp_t_aut \<tau> (f \<acute> x) = f \<acute> x"
proof -
  have ax: "Elem (pp_t_aut \<sigma> x) (pp_t_domain \<sigma>)"
    by (rule pp_t_aut_in_domain[OF x])
  have application:
      "pp_t_aut (\<sigma> \<rightarrow>\<^sub>o \<tau>) f
          \<acute> pp_t_aut \<sigma> x
        =
        pp_t_aut \<tau>
          (f \<acute> pp_t_aut \<sigma> (pp_t_aut \<sigma> x))"
    by (rule pp_t_aut_apply[OF ax])
  have involution:
      "pp_t_aut \<sigma> (pp_t_aut \<sigma> x) = x"
    by (rule pp_t_aut_involution[OF x])
  show ?thesis
    using application f_fixed x_fixed involution by simp
qed

lemma pp_t_arrow_function_ext:
  assumes F: "Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and G: "Elem G (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and applications:
      "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        F \<acute> x = G \<acute> x"
  shows "F = G"
proof -
  have F_fun:
      "Elem F (Fun (pp_t_domain \<sigma>) (pp_t_domain \<tau>))"
    by (rule pp_t_arrow_member_function[OF F])
  have G_fun:
      "Elem G (Fun (pp_t_domain \<sigma>) (pp_t_domain \<tau>))"
    by (rule pp_t_arrow_member_function[OF G])
  obtain A where F_rep: "F = Lambda (pp_t_domain \<sigma>) A"
    using Elem_Fun_Lambda[OF F_fun] by blast
  obtain B where G_rep: "G = Lambda (pp_t_domain \<sigma>) B"
    using Elem_Fun_Lambda[OF G_fun] by blast
  have pointwise:
      "\<And>x. Elem x (pp_t_domain \<sigma>) \<Longrightarrow> A x = B x"
  proof -
    fix x
    assume x: "Elem x (pp_t_domain \<sigma>)"
    have app: "F \<acute> x = G \<acute> x"
      by (rule applications[OF x])
    show "A x = B x"
      using app
      apply (subst (asm) F_rep)
      apply (subst (asm) G_rep)
      using x by (simp add: Lambda_app)
  qed
  show ?thesis
    apply (subst F_rep)
    apply (subst G_rep)
    using pointwise by (simp add: Lambda_ext)
qed

lemma pp_t_symmetrized_closed_stock_probe_aut_fixed:
  "pp_t_aut pp_t_boolean_probe_unary_type
      pp_t_symmetrized_closed_stock_probe
    =
    pp_t_symmetrized_closed_stock_probe"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_aut pp_t_boolean_probe_unary_type
        pp_t_symmetrized_closed_stock_probe)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_aut_in_domain)
      (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  show "Elem pp_t_symmetrized_closed_stock_probe
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  let ?B =
    "pp_t_closed_den pp_t_symmetrized_singleton_family_builder"
  have aq: "Elem (pp_t_aut Prop q) (pp_t_domain Prop)"
    by (rule pp_t_aut_in_domain[OF q])
  have B:
      "Elem ?B
        (pp_t_domain
          (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type))"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_symmetrized_singleton_family_builder_typed)
  have B_fixed:
      "pp_t_aut
          (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) ?B
        = ?B"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical])
  have Bq:
      "Elem (?B \<acute> q)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF B q])
  have B_aq:
      "?B \<acute> pp_t_aut Prop q
        =
        pp_t_aut pp_t_boolean_probe_unary_type (?B \<acute> q)"
  proof -
    have application:
        "pp_t_aut
            (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) ?B
            \<acute> pp_t_aut Prop q
          =
          pp_t_aut pp_t_boolean_probe_unary_type
            (?B \<acute> pp_t_aut Prop (pp_t_aut Prop q))"
      by (rule pp_t_aut_apply[OF aq])
    have involution:
        "pp_t_aut Prop (pp_t_aut Prop q) = q"
      by (rule pp_t_aut_involution[OF q])
    show ?thesis
      using application B_fixed involution by simp
  qed
  show "pp_t_aut pp_t_boolean_probe_unary_type
          pp_t_symmetrized_closed_stock_probe \<acute> q
      =
      pp_t_symmetrized_closed_stock_probe \<acute> q"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut pp_t_boolean_probe_unary_type
          pp_t_symmetrized_closed_stock_probe \<acute> q)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed)
        (rule pp_t_aut_in_domain[
          OF pp_t_symmetrized_closed_stock_probe_in_domain],
         rule q)
    show "Elem
        (pp_t_symmetrized_closed_stock_probe \<acute> q)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_symmetrized_closed_stock_probe_in_domain q])
    fix w
    have aut_application:
        "pp_t_aut pp_t_boolean_probe_unary_type
            pp_t_symmetrized_closed_stock_probe \<acute> q
          =
          pp_t_aut Prop
            (pp_t_symmetrized_closed_stock_probe
              \<acute> pp_t_aut Prop q)"
      by (rule pp_t_aut_apply[OF q])
    have left_semantics:
        "pp_t_holds
          (pp_t_symmetrized_closed_stock_probe
            \<acute> pp_t_aut Prop q)
          (pp_t_root_swap w)
        =
        pp_t_closed_logical_stock
          pp_t_boolean_probe_unary_type
          (pp_t_root_swap w)
          (?B \<acute> pp_t_aut Prop q)"
      unfolding pp_t_symmetrized_closed_stock_probe_def
      by (rule pp_t_family_probe_for_stock_apply_holds[
        OF pp_t_symmetrized_singleton_family_builder_typed
          pp_t_closed_logical_stock_admissible aq])
    have transported:
        "pp_t_closed_logical_stock
            pp_t_boolean_probe_unary_type
            (pp_t_root_swap w)
            (?B \<acute> pp_t_aut Prop q)
        =
        pp_t_closed_logical_stock
            pp_t_boolean_probe_unary_type w (?B \<acute> q)"
      unfolding B_aq
      using pp_t_closed_logical_stock_aut_iff[
        OF Bq, of "pp_t_root_swap w"]
      by simp
    have right_semantics:
        "pp_t_holds
          (pp_t_symmetrized_closed_stock_probe \<acute> q) w
        =
        pp_t_closed_logical_stock
          pp_t_boolean_probe_unary_type w (?B \<acute> q)"
      unfolding pp_t_symmetrized_closed_stock_probe_def
      by (rule pp_t_family_probe_for_stock_apply_holds[
        OF pp_t_symmetrized_singleton_family_builder_typed
          pp_t_closed_logical_stock_admissible q])
    show "pp_t_holds
          (pp_t_aut pp_t_boolean_probe_unary_type
            pp_t_symmetrized_closed_stock_probe \<acute> q) w
        =
        pp_t_holds
          (pp_t_symmetrized_closed_stock_probe \<acute> q) w"
      using aut_application left_semantics transported right_semantics
      by simp
  qed
qed

lemma pp_t_probe_boolean_expr_den_aut_fixed:
  assumes valid: "pp_t_probe_boolean_expr_valid E"
  shows "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_probe_boolean_expr_den E)
    =
    pp_t_probe_boolean_expr_den E"
  using valid
proof (induction E)
  case (PPProbeBooleanLogical M)
  have typed:
      "[] \<turnstile> M : pp_t_boolean_probe_unary_type"
    and logical: "pp_logical_vocabulary M"
    using PPProbeBooleanLogical.prems by simp_all
  show ?case
    using pp_t_closed_logical_den_aut_fixed[OF typed logical]
    by simp
next
  case PPProbeBooleanGenerator
  show ?case
    using pp_t_symmetrized_closed_stock_probe_aut_fixed by simp
next
  case (PPProbeBooleanNeg E)
  have E_valid: "pp_t_probe_boolean_expr_valid E"
    using PPProbeBooleanNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_expr_den_in_domain[OF E_valid])
  have negator:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have negator_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          (pp_t_closed_den pp_t_unary_output_negator)
        =
        pp_t_closed_den pp_t_unary_output_negator"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_unary_output_negator_typed
        pp_t_unary_output_negator_logical])
  have E_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_probe_boolean_expr_den E)
        =
        pp_t_probe_boolean_expr_den E"
    by (rule PPProbeBooleanNeg.IH[OF E_valid])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_closed_den pp_t_unary_output_negator
            \<acute> pp_t_probe_boolean_expr_den E)
        =
        pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_boolean_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF negator E_domain negator_fixed E_fixed])
  show ?case
    using fixed by simp
next
  case (PPProbeBooleanConj E F)
  have E_valid: "pp_t_probe_boolean_expr_valid E"
    and F_valid: "pp_t_probe_boolean_expr_valid F"
    using PPProbeBooleanConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_expr_den_in_domain[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_boolean_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_expr_den_in_domain[OF F_valid])
  have conjunction:
      "Elem pp_t_unary_output_conjunction_den
        (pp_t_domain pp_t_boolean_probe_builder_type)"
    by (rule pp_t_unary_output_conjunction_den_in_domain)
  have conjunction_fixed:
      "pp_t_aut pp_t_boolean_probe_builder_type
          pp_t_unary_output_conjunction_den
        =
        pp_t_unary_output_conjunction_den"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_unary_output_conjunction_typed
        pp_t_unary_output_conjunction_logical])
  have E_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_probe_boolean_expr_den E)
        =
        pp_t_probe_boolean_expr_den E"
    by (rule PPProbeBooleanConj.IH(1)[OF E_valid])
  have F_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_probe_boolean_expr_den F)
        =
        pp_t_probe_boolean_expr_den F"
    by (rule PPProbeBooleanConj.IH(2)[OF F_valid])
  have first_domain:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[OF conjunction E_domain])
  have first_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_boolean_expr_den E)
        =
        pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_boolean_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF conjunction E_domain conjunction_fixed E_fixed])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          ((pp_t_unary_output_conjunction_den
              \<acute> pp_t_probe_boolean_expr_den E)
            \<acute> pp_t_probe_boolean_expr_den F)
        =
        (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_boolean_expr_den E)
          \<acute> pp_t_probe_boolean_expr_den F"
    by (rule pp_t_aut_fixed_application[
      OF first_domain F_domain first_fixed F_fixed])
  show ?case
    using fixed by simp
qed

lemma pp_t_probe_boolean_representative_aut_fixed:
  assumes d: "d \<in> pp_t_probe_boolean_representatives"
  shows "pp_t_aut pp_t_boolean_probe_unary_type d = d"
proof -
  obtain E where valid: "pp_t_probe_boolean_expr_valid E"
    and d_eq: "d = pp_t_probe_boolean_expr_den E"
    using d unfolding pp_t_probe_boolean_representatives_def by blast
  show ?thesis
    unfolding d_eq
    by (rule pp_t_probe_boolean_expr_den_aut_fixed[OF valid])
qed

lemma pp_t_probe_boolean_stock_aut_iff:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
  shows "pp_t_probe_boolean_stock w
      (pp_t_aut pp_t_boolean_probe_unary_type X)
    \<longleftrightarrow>
    pp_t_probe_boolean_stock (pp_t_root_swap w) X"
proof
  assume stock:
      "pp_t_probe_boolean_stock w
        (pp_t_aut pp_t_boolean_probe_unary_type X)"
  then obtain d where d: "d \<in> pp_t_probe_boolean_representatives"
    and related:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_aut pp_t_boolean_probe_unary_type X) d"
    unfolding pp_t_probe_boolean_stock_def by blast
  have d_domain:
      "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_representative_in_domain[OF d])
  have d_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type d = d"
    by (rule pp_t_probe_boolean_representative_aut_fixed[OF d])
  have aut_related:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_aut pp_t_boolean_probe_unary_type X)
        (pp_t_aut pp_t_boolean_probe_unary_type d)"
    using related d_fixed by simp
  have base_related:
      "pp_t_eqv pp_t_boolean_probe_unary_type
        (pp_t_root_swap w) X d"
    using pp_t_aut_eqv_iff[OF X d_domain, of w]
      aut_related by blast
  show "pp_t_probe_boolean_stock (pp_t_root_swap w) X"
    unfolding pp_t_probe_boolean_stock_def
    using X d base_related by blast
next
  assume stock: "pp_t_probe_boolean_stock (pp_t_root_swap w) X"
  then obtain d where d: "d \<in> pp_t_probe_boolean_representatives"
    and related:
      "pp_t_eqv pp_t_boolean_probe_unary_type
        (pp_t_root_swap w) X d"
    unfolding pp_t_probe_boolean_stock_def by blast
  have d_domain:
      "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_representative_in_domain[OF d])
  have d_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type d = d"
    by (rule pp_t_probe_boolean_representative_aut_fixed[OF d])
  have aut_related:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_aut pp_t_boolean_probe_unary_type X)
        (pp_t_aut pp_t_boolean_probe_unary_type d)"
    using pp_t_aut_eqv_iff[OF X d_domain, of w]
      related by blast
  have target:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_aut pp_t_boolean_probe_unary_type X) d"
    using aut_related d_fixed by simp
  show "pp_t_probe_boolean_stock w
      (pp_t_aut pp_t_boolean_probe_unary_type X)"
    unfolding pp_t_probe_boolean_stock_def
    using pp_t_aut_in_domain[OF X] d target by blast
qed

lemma pp_t_probe_boolean_classifier_aut_fixed:
  "pp_t_aut
      (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
      (pp_t_classifier pp_t_boolean_probe_unary_type
        pp_t_probe_boolean_stock)
    =
    pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_stock"
proof (rule pp_t_arrow_function_ext)
  show "Elem
      (pp_t_aut
        (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
        (pp_t_classifier pp_t_boolean_probe_unary_type
          pp_t_probe_boolean_stock))
      (pp_t_domain
        (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_aut_in_domain[
      OF pp_t_classifier_in_domain[
        OF pp_t_probe_boolean_stock_admissible]])
  show "Elem
      (pp_t_classifier pp_t_boolean_probe_unary_type
        pp_t_probe_boolean_stock)
      (pp_t_domain
        (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain)
      (rule pp_t_probe_boolean_stock_admissible)
  fix X
  assume X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
  show "pp_t_aut
          (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
          (pp_t_classifier pp_t_boolean_probe_unary_type
            pp_t_probe_boolean_stock) \<acute> X
      =
      pp_t_classifier pp_t_boolean_probe_unary_type
        pp_t_probe_boolean_stock \<acute> X"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_aut
          (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
          (pp_t_classifier pp_t_boolean_probe_unary_type
            pp_t_probe_boolean_stock) \<acute> X)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed, rule pp_t_aut_in_domain)
        (rule pp_t_classifier_in_domain[
          OF pp_t_probe_boolean_stock_admissible], rule X)
    show "Elem
        (pp_t_classifier pp_t_boolean_probe_unary_type
          pp_t_probe_boolean_stock \<acute> X)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed,
          rule pp_t_classifier_in_domain[
            OF pp_t_probe_boolean_stock_admissible],
          rule X)
    fix w
    have application:
        "pp_t_aut
            (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
            (pp_t_classifier pp_t_boolean_probe_unary_type
              pp_t_probe_boolean_stock) \<acute> X
          =
          pp_t_aut Prop
            (pp_t_classifier pp_t_boolean_probe_unary_type
              pp_t_probe_boolean_stock
              \<acute> pp_t_aut pp_t_boolean_probe_unary_type X)"
      by (rule pp_t_aut_apply[OF X])
    have aX:
        "Elem (pp_t_aut pp_t_boolean_probe_unary_type X)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_aut_in_domain[OF X])
    have transport:
        "pp_t_probe_boolean_stock (pp_t_root_swap w)
            (pp_t_aut pp_t_boolean_probe_unary_type X)
        =
        pp_t_probe_boolean_stock w X"
      using pp_t_probe_boolean_stock_aut_iff[
        OF X, of "pp_t_root_swap w"]
      by simp
    show "pp_t_holds
          (pp_t_aut
            (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
            (pp_t_classifier pp_t_boolean_probe_unary_type
              pp_t_probe_boolean_stock) \<acute> X) w
        =
        pp_t_holds
          (pp_t_classifier pp_t_boolean_probe_unary_type
            pp_t_probe_boolean_stock \<acute> X) w"
      using application transport
        pp_t_classifier_holds[
          OF aX, of pp_t_probe_boolean_stock "pp_t_root_swap w"]
        pp_t_classifier_holds[
          OF X, of pp_t_probe_boolean_stock w]
      by simp
  qed
qed

lemma pp_t_probe_boolean_family_probe_aut_fixed:
  "pp_t_aut pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_family_probe
    =
    pp_t_probe_boolean_family_probe"
proof -
  let ?builder =
    "pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder)"
  let ?classifier =
    "pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_boolean_stock"
  have builder:
      "Elem ?builder
        (pp_t_domain
          ((pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
            \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type))"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_family_probe_builder_typed[
        OF pp_t_symmetrized_singleton_family_builder_typed])
  have classifier:
      "Elem ?classifier
        (pp_t_domain
          (pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain)
      (rule pp_t_probe_boolean_stock_admissible)
  have builder_fixed:
      "pp_t_aut
          ((pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop)
            \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type)
          ?builder
        =
        ?builder"
    by (rule pp_t_closed_logical_den_aut_fixed)
      (rule pp_t_family_probe_builder_typed[
          OF pp_t_symmetrized_singleton_family_builder_typed],
       rule pp_t_family_probe_builder_logical[
          OF pp_t_symmetrized_singleton_family_builder_logical])
  have applied_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (?builder \<acute> ?classifier)
        =
        ?builder \<acute> ?classifier"
    by (rule pp_t_aut_fixed_application[
      OF builder classifier builder_fixed
        pp_t_probe_boolean_classifier_aut_fixed])
  show ?thesis
    using applied_fixed
    unfolding pp_t_probe_boolean_family_probe_def
      pp_t_family_probe_for_stock_def
    by simp
qed

section \<open>The four canonical complement-classes\<close>

lemma pp_t_aut_symmetrized_singleton_family_at:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_symmetrized_singleton_family_at p)
    =
    pp_t_symmetrized_singleton_family_at (pp_t_aut Prop p)"
proof -
  let ?B =
    "pp_t_closed_den pp_t_symmetrized_singleton_family_builder"
  have ap: "Elem (pp_t_aut Prop p) (pp_t_domain Prop)"
    by (rule pp_t_aut_in_domain[OF p])
  have application:
      "pp_t_aut
          (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) ?B
          \<acute> pp_t_aut Prop p
        =
        pp_t_aut pp_t_boolean_probe_unary_type
          (?B \<acute> pp_t_aut Prop (pp_t_aut Prop p))"
    by (rule pp_t_aut_apply[OF ap])
  have B_fixed:
      "pp_t_aut
          (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) ?B
        = ?B"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical])
  have involution: "pp_t_aut Prop (pp_t_aut Prop p) = p"
    by (rule pp_t_aut_involution[OF p])
  show ?thesis
    using application B_fixed involution by simp
qed

lemma pp_t_symmetrized_singleton_family_not_fixed_if_parameter_moves:
  assumes p: "Elem p (pp_t_domain Prop)"
    and moves: "pp_t_aut Prop p \<noteq> p"
    and not_complement:
      "p \<noteq> pp_t_complement (pp_t_aut Prop p)"
  shows "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_symmetrized_singleton_family_at p)
    \<noteq>
    pp_t_symmetrized_singleton_family_at p"
proof
  assume fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_symmetrized_singleton_family_at p)
        =
        pp_t_symmetrized_singleton_family_at p"
  have ap: "Elem (pp_t_aut Prop p) (pp_t_domain Prop)"
    by (rule pp_t_aut_in_domain[OF p])
  have cap:
      "Elem (pp_t_complement (pp_t_aut Prop p))
        (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have family_eq:
      "pp_t_symmetrized_singleton_family_at (pp_t_aut Prop p)
        =
        pp_t_symmetrized_singleton_family_at p"
    using fixed pp_t_aut_symmetrized_singleton_family_at[OF p]
    by simp
  have moved_false:
      "\<not> pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          (pp_t_aut Prop p) \<acute> p) []"
  proof -
    have not_first:
        "\<not> pp_t_eqv Prop [] p (pp_t_aut Prop p)"
      using pp_t_root_eqv_iff_eq[OF p ap] moves by auto
    have not_second:
        "\<not> pp_t_eqv Prop []
          p (pp_t_complement (pp_t_aut Prop p))"
      using pp_t_root_eqv_iff_eq[OF p cap] not_complement
      by auto
    show ?thesis
      using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF ap p, of "[]"] not_first not_second
      by blast
  qed
  have original_true:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at p \<acute> p) []"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF p p, of "[]"]
      pp_t_eqv_reflexive[OF p]
    by blast
  have applications:
      "pp_t_symmetrized_singleton_family_at (pp_t_aut Prop p)
          \<acute> p
        =
        pp_t_symmetrized_singleton_family_at p \<acute> p"
    by (rule arg_cong[OF family_eq])
  have truth_eq:
      "pp_t_holds
          (pp_t_symmetrized_singleton_family_at
            (pp_t_aut Prop p) \<acute> p) []
        =
        pp_t_holds
          (pp_t_symmetrized_singleton_family_at p \<acute> p) []"
    by (rule arg_cong[OF applications])
  show False
    using moved_false original_true truth_eq by blast
qed

definition pp_t_even_true_parity :: ZF where
  "pp_t_even_true_parity =
    pp_t_word_character_prop True True False"

definition pp_t_even_false_word_parity :: ZF where
  "pp_t_even_false_word_parity =
    pp_t_word_character_prop True False True"

definition pp_t_even_length_parity :: ZF where
  "pp_t_even_length_parity =
    pp_t_word_character_prop True True True"

lemma pp_t_even_true_parity_in_domain:
  "Elem pp_t_even_true_parity (pp_t_domain Prop)"
  unfolding pp_t_even_true_parity_def
  by (rule pp_t_word_character_prop_in_domain)

lemma pp_t_even_false_word_parity_in_domain:
  "Elem pp_t_even_false_word_parity (pp_t_domain Prop)"
  unfolding pp_t_even_false_word_parity_def
  by (rule pp_t_word_character_prop_in_domain)

lemma pp_t_even_length_parity_in_domain:
  "Elem pp_t_even_length_parity (pp_t_domain Prop)"
  unfolding pp_t_even_length_parity_def
  by (rule pp_t_word_character_prop_in_domain)

lemma pp_t_aut_even_true_parity_ne:
  "pp_t_aut Prop pp_t_even_true_parity
    \<noteq> pp_t_even_true_parity"
proof
  assume equality:
      "pp_t_aut Prop pp_t_even_true_parity
        = pp_t_even_true_parity"
  have at_false:
      "pp_t_holds
          (pp_t_aut Prop pp_t_even_true_parity) [False]
        =
        pp_t_holds pp_t_even_true_parity [False]"
    by (rule arg_cong[OF equality])
  show False
    using at_false
    by (simp add: pp_t_even_true_parity_def)
qed

lemma pp_t_even_true_parity_ne_complement_aut:
  "pp_t_even_true_parity
    \<noteq> pp_t_complement
      (pp_t_aut Prop pp_t_even_true_parity)"
proof
  assume equality:
      "pp_t_even_true_parity =
        pp_t_complement
          (pp_t_aut Prop pp_t_even_true_parity)"
  have at_root:
      "pp_t_holds pp_t_even_true_parity []
        =
        pp_t_holds
          (pp_t_complement
            (pp_t_aut Prop pp_t_even_true_parity)) []"
    by (rule arg_cong[OF equality])
  show False
    using at_root
    by (simp add: pp_t_even_true_parity_def)
qed

lemma pp_t_symmetrized_singleton_even_true_parity_not_fixed:
  "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_true_parity)
    \<noteq>
    pp_t_symmetrized_singleton_family_at pp_t_even_true_parity"
  by (rule
    pp_t_symmetrized_singleton_family_not_fixed_if_parameter_moves[
      OF pp_t_even_true_parity_in_domain
        pp_t_aut_even_true_parity_ne
        pp_t_even_true_parity_ne_complement_aut])

lemma pp_t_aut_even_false_word_parity_ne:
  "pp_t_aut Prop pp_t_even_false_word_parity
    \<noteq> pp_t_even_false_word_parity"
proof
  assume equality:
      "pp_t_aut Prop pp_t_even_false_word_parity
        = pp_t_even_false_word_parity"
  have at_true:
      "pp_t_holds
          (pp_t_aut Prop pp_t_even_false_word_parity) [True]
        =
        pp_t_holds pp_t_even_false_word_parity [True]"
    by (rule arg_cong[OF equality])
  show False
    using at_true
    by (simp add: pp_t_even_false_word_parity_def)
qed

lemma pp_t_even_false_word_parity_ne_complement_aut:
  "pp_t_even_false_word_parity
    \<noteq> pp_t_complement
      (pp_t_aut Prop pp_t_even_false_word_parity)"
proof
  assume equality:
      "pp_t_even_false_word_parity =
        pp_t_complement
          (pp_t_aut Prop pp_t_even_false_word_parity)"
  have at_root:
      "pp_t_holds pp_t_even_false_word_parity []
        =
        pp_t_holds
          (pp_t_complement
            (pp_t_aut Prop pp_t_even_false_word_parity)) []"
    by (rule arg_cong[OF equality])
  show False
    using at_root
    by (simp add: pp_t_even_false_word_parity_def)
qed

lemma pp_t_symmetrized_singleton_even_false_word_parity_not_fixed:
  "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_false_word_parity)
    \<noteq>
    pp_t_symmetrized_singleton_family_at
      pp_t_even_false_word_parity"
  by (rule
    pp_t_symmetrized_singleton_family_not_fixed_if_parameter_moves[
      OF pp_t_even_false_word_parity_in_domain
        pp_t_aut_even_false_word_parity_ne
        pp_t_even_false_word_parity_ne_complement_aut])

lemma pp_t_aut_even_length_parity_fixed:
  "pp_t_aut Prop pp_t_even_length_parity
    = pp_t_even_length_parity"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_aut Prop pp_t_even_length_parity)
      (pp_t_domain Prop)"
    by (rule pp_t_aut_in_domain[
      OF pp_t_even_length_parity_in_domain])
  show "Elem pp_t_even_length_parity (pp_t_domain Prop)"
    by (rule pp_t_even_length_parity_in_domain)
  fix w
  show "pp_t_holds (pp_t_aut Prop pp_t_even_length_parity) w
      =
      pp_t_holds pp_t_even_length_parity w"
    by (cases w)
      (simp_all add: pp_t_even_length_parity_def)
qed

lemma pp_t_symmetrized_singleton_even_length_parity_fixed:
  "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)
    =
    pp_t_symmetrized_singleton_family_at pp_t_even_length_parity"
  using pp_t_aut_symmetrized_singleton_family_at[
      OF pp_t_even_length_parity_in_domain]
    pp_t_aut_even_length_parity_fixed
  by simp

lemma pp_t_word_character_prop_flip_initial:
  "pp_t_word_character_prop (\<not> initial) on_true on_false
    =
    pp_t_complement
      (pp_t_word_character_prop initial on_true on_false)"
proof (rule pp_t_prop_ext)
  show "Elem
      (pp_t_word_character_prop (\<not> initial) on_true on_false)
      (pp_t_domain Prop)"
    by (rule pp_t_word_character_prop_in_domain)
  show "Elem
      (pp_t_complement
        (pp_t_word_character_prop initial on_true on_false))
      (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  fix w
  show "pp_t_holds
        (pp_t_word_character_prop
          (\<not> initial) on_true on_false) w
      =
      pp_t_holds
        (pp_t_complement
          (pp_t_word_character_prop initial on_true on_false)) w"
    by simp
qed

lemma pp_t_word_character_constant_prop_closed_logical:
  "pp_t_closed_logical_stock Prop w
    (pp_t_word_character_prop initial False False)"
proof -
  have true_domain:
      "Elem (pp_t_closed_den ObjTrue) (pp_t_domain Prop)"
    by (rule pp_t_closed_den_in_domain)
      (rule typed_ObjTrue)
  have false_domain:
      "Elem (pp_t_closed_den ObjFalse) (pp_t_domain Prop)"
    by (rule pp_t_closed_den_in_domain)
      (rule typed_ObjFalse)
  have zero:
      "\<And>v. pp_t_word_character False False v = False"
  proof -
    fix v
    show "pp_t_word_character False False v = False"
      by (induction v) simp_all
  qed
  have equality:
      "pp_t_word_character_prop initial False False
        =
        pp_t_closed_den (if initial then ObjTrue else ObjFalse)"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_word_character_prop initial False False)
        (pp_t_domain Prop)"
      by (rule pp_t_word_character_prop_in_domain)
    show "Elem
        (pp_t_closed_den
          (if initial then ObjTrue else ObjFalse))
        (pp_t_domain Prop)"
      using true_domain false_domain
      by (cases initial) simp_all
    fix v
    show "pp_t_holds
          (pp_t_word_character_prop initial False False) v
        =
        pp_t_holds
          (pp_t_closed_den
            (if initial then ObjTrue else ObjFalse)) v"
      using zero[of v]
      by (cases initial)
        (simp_all add: pp_t_closed_den_def
          ObjFalse_def ObjTrue_def pp_t_eval_ObjTrue)
  qed
  have typed:
      "[] \<turnstile> (if initial then ObjTrue else ObjFalse) : Prop"
    by (cases initial) (simp_all add: typed_ObjTrue typed_ObjFalse)
  have logical:
      "pp_logical_vocabulary
        (if initial then ObjTrue else ObjFalse)"
    by (cases initial)
      (simp_all add: pp_logical_vocabulary_def
        ObjFalse_def ObjTrue_def)
  show ?thesis
    unfolding equality
    by (rule pp_t_closed_logical_stockI[OF typed logical])
qed

lemma pp_t_symmetrized_constant_character_family_in_boolean_stock:
  "pp_t_probe_boolean_stock w
    (pp_t_symmetrized_singleton_family_at
      (pp_t_word_character_prop initial False False))"
proof -
  have B_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type) w
        (pp_t_closed_den
          pp_t_symmetrized_singleton_family_builder)"
    by (rule pp_t_closed_logical_stockI[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical])
  have family_stock:
      "pp_t_closed_logical_stock pp_t_boolean_probe_unary_type w
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop initial False False))"
    using pp_t_closed_logical_stock_application_closed[
      OF B_stock
        pp_t_word_character_constant_prop_closed_logical] .
  show ?thesis
    by (rule pp_t_closed_logical_stock_subset_probe_boolean_stock[
      OF family_stock])
qed

lemma pp_t_symmetrized_word_character_family_initial_irrelevant:
  "pp_t_symmetrized_singleton_family_at
      (pp_t_word_character_prop initial on_true on_false)
    =
    pp_t_symmetrized_singleton_family_at
      (pp_t_word_character_prop True on_true on_false)"
proof (cases initial)
  case True
  then show ?thesis by simp
next
  case False
  have parameter:
      "pp_t_word_character_prop False on_true on_false
        =
        pp_t_complement
          (pp_t_word_character_prop True on_true on_false)"
    using pp_t_word_character_prop_flip_initial[
      of True on_true on_false]
    by simp
  show ?thesis
    using pp_t_symmetrized_singleton_family_at_complement[
        OF pp_t_word_character_prop_in_domain,
        of True on_true on_false]
      parameter False
    by simp
qed

theorem pp_t_fixed_canonical_character_family_reduction:
  assumes fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop initial on_true on_false))
      =
      pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop initial on_true on_false)"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop initial on_true on_false))
    \<or>
    pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop initial on_true on_false)
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  let ?p =
    "pp_t_word_character_prop initial on_true on_false"
  let ?F = "pp_t_symmetrized_singleton_family_at ?p"
  have normalize:
      "?F =
        pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop True on_true on_false)"
    by (rule
      pp_t_symmetrized_word_character_family_initial_irrelevant)
  show ?thesis
  proof (cases on_true)
    case False
    have on_true_false: "on_true = False"
      using False by simp
    show ?thesis
    proof (cases on_false)
      case False
      have on_false_false: "on_false = False"
        using False by simp
      show ?thesis
      proof (intro disjI1)
        show "pp_t_probe_boolean_stock [] ?F"
          using
            pp_t_symmetrized_constant_character_family_in_boolean_stock[
              of "[]" initial]
            on_true_false on_false_false
          by simp
      qed
    next
      case True
      have on_false_true: "on_false = True"
        using True by simp
      have target:
          "?F =
          pp_t_symmetrized_singleton_family_at
            pp_t_even_false_word_parity"
        using normalize on_true_false on_false_true
        unfolding pp_t_even_false_word_parity_def by simp
      have target_fixed:
          "pp_t_aut pp_t_boolean_probe_unary_type
              (pp_t_symmetrized_singleton_family_at
                pp_t_even_false_word_parity)
            =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_false_word_parity"
        using fixed target by simp
      show ?thesis
        using
          pp_t_symmetrized_singleton_even_false_word_parity_not_fixed
          target_fixed
        by contradiction
    qed
  next
    case True
    have on_true_true: "on_true = True"
      using True by simp
    show ?thesis
    proof (cases on_false)
      case False
      have on_false_false: "on_false = False"
        using False by simp
      have target:
          "?F =
          pp_t_symmetrized_singleton_family_at
            pp_t_even_true_parity"
        using normalize on_true_true on_false_false
        unfolding pp_t_even_true_parity_def by simp
      have target_fixed:
          "pp_t_aut pp_t_boolean_probe_unary_type
              (pp_t_symmetrized_singleton_family_at
                pp_t_even_true_parity)
            =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_true_parity"
        using fixed target by simp
      show ?thesis
        using
          pp_t_symmetrized_singleton_even_true_parity_not_fixed
          target_fixed
        by contradiction
    next
      case True
      have on_false_true: "on_false = True"
        using True by simp
      show ?thesis
      proof (intro disjI2)
        show "?F =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_length_parity"
          using normalize on_true_true on_false_true
          unfolding pp_t_even_length_parity_def by simp
      qed
    qed
  qed
qed

theorem pp_t_canonical_character_collision_reduction:
  assumes collision:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            initial on_true on_false))"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop initial on_true on_false))
    \<or>
    pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop initial on_true on_false)
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  let ?p =
    "pp_t_word_character_prop initial on_true on_false"
  let ?F = "pp_t_symmetrized_singleton_family_at ?p"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_word_character_prop_in_domain)
  have F:
      "Elem ?F (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
  have equality: "pp_t_probe_boolean_family_probe = ?F"
    by (rule pp_t_root_eqv_imp_eq[
      OF pp_t_probe_boolean_family_probe_in_domain F collision])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type ?F = ?F"
    using pp_t_probe_boolean_family_probe_aut_fixed equality
    by simp
  have normalize:
      "?F =
        pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop True on_true on_false)"
    by (rule
      pp_t_symmetrized_word_character_family_initial_irrelevant)
  show ?thesis
  proof (cases on_true)
    case False
    have on_true_false: "on_true = False"
      using False by simp
    show ?thesis
    proof (cases on_false)
      case False
      have on_false_false: "on_false = False"
        using False by simp
      show ?thesis
      proof (intro disjI1)
        show "pp_t_probe_boolean_stock [] ?F"
          using
            pp_t_symmetrized_constant_character_family_in_boolean_stock[
              of "[]" initial]
            on_true_false on_false_false
          by simp
      qed
    next
      case True
      have on_false_true: "on_false = True"
        using True by simp
      have target:
          "?F =
          pp_t_symmetrized_singleton_family_at
            pp_t_even_false_word_parity"
        using normalize on_true_false on_false_true
        unfolding pp_t_even_false_word_parity_def by simp
      have target_fixed:
          "pp_t_aut pp_t_boolean_probe_unary_type
              (pp_t_symmetrized_singleton_family_at
                pp_t_even_false_word_parity)
            =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_false_word_parity"
        using fixed target by simp
      show ?thesis
        using
          pp_t_symmetrized_singleton_even_false_word_parity_not_fixed
          target_fixed
        by contradiction
    qed
  next
    case True
    have on_true_true: "on_true = True"
      using True by simp
    show ?thesis
    proof (cases on_false)
      case False
      have on_false_false: "on_false = False"
        using False by simp
      have target:
          "?F =
          pp_t_symmetrized_singleton_family_at
            pp_t_even_true_parity"
        using normalize on_true_true on_false_false
        unfolding pp_t_even_true_parity_def by simp
      have target_fixed:
          "pp_t_aut pp_t_boolean_probe_unary_type
              (pp_t_symmetrized_singleton_family_at
                pp_t_even_true_parity)
            =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_true_parity"
        using fixed target by simp
      show ?thesis
        using
          pp_t_symmetrized_singleton_even_true_parity_not_fixed
          target_fixed
        by contradiction
    next
      case True
      have on_false_true: "on_false = True"
        using True by simp
      show ?thesis
      proof (intro disjI2)
        show "?F =
            pp_t_symmetrized_singleton_family_at
              pp_t_even_length_parity"
          using normalize on_true_true on_false_true
          unfolding pp_t_even_length_parity_def by simp
      qed
    qed
  qed
qed

theorem pp_t_probe_boolean_root_collision_reduction:
  assumes p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at p)"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    pp_t_symmetrized_singleton_family_at p
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  have parameter:
      "p =
        pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
    by (rule
      pp_t_probe_boolean_root_collision_parameter_classification[
        OF p collision])
  have family_eq:
      "pp_t_symmetrized_singleton_family_at p
        =
        pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))"
    by (rule arg_cong[OF parameter])
  have reduced:
      "pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p [])))
      \<or>
      pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity"
  proof (rule pp_t_canonical_character_collision_reduction)
    show "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p [])))"
      using collision family_eq by simp
  qed
  show ?thesis
    using reduced family_eq by simp
qed

theorem
  pp_t_probe_boolean_all_collisions_absorbed_iff_length_collision_absorbed:
  "(\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_boolean_probe_unary_type w
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at p)
      \<longrightarrow>
      pp_t_probe_boolean_stock w
        (pp_t_symmetrized_singleton_family_at p))
  \<longleftrightarrow>
  (pp_t_eqv pp_t_boolean_probe_unary_type []
      pp_t_probe_boolean_family_probe
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)
    \<longrightarrow>
    pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity))"
proof
  assume all:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type w
          pp_t_probe_boolean_family_probe
          (pp_t_symmetrized_singleton_family_at p)
        \<longrightarrow>
        pp_t_probe_boolean_stock w
          (pp_t_symmetrized_singleton_family_at p)"
  show "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<longrightarrow>
      pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
    using all pp_t_even_length_parity_in_domain by blast
next
  assume length:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
          pp_t_probe_boolean_family_probe
          (pp_t_symmetrized_singleton_family_at
            pp_t_even_length_parity)
        \<longrightarrow>
        pp_t_probe_boolean_stock []
          (pp_t_symmetrized_singleton_family_at
            pp_t_even_length_parity)"
  show "\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_boolean_probe_unary_type w
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at p)
      \<longrightarrow>
      pp_t_probe_boolean_stock w
        (pp_t_symmetrized_singleton_family_at p)"
  proof (intro allI impI)
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_boolean_probe_unary_type w
          pp_t_probe_boolean_family_probe
          (pp_t_symmetrized_singleton_family_at p)"
    let ?q = "pp_t_cone_view w p"
    let ?Fp = "pp_t_symmetrized_singleton_family_at p"
    let ?Fq = "pp_t_symmetrized_singleton_family_at ?q"
    let ?L =
      "pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
    have q: "Elem ?q (pp_t_domain Prop)"
      by (rule pp_t_cone_view_in_domain)
    have Fp:
        "Elem ?Fp (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
    have Fq:
        "Elem ?Fq (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF q])
    have probe_cone:
        "pp_t_cone_rel pp_t_boolean_probe_unary_type w
          pp_t_probe_boolean_family_probe
          pp_t_probe_boolean_family_probe"
      by (rule pp_t_probe_boolean_family_probe_cone_natural)
    have family_cone:
        "pp_t_cone_rel pp_t_boolean_probe_unary_type w ?Fp ?Fq"
      by (rule pp_t_logical_family_at_cone_related[
        OF pp_t_symmetrized_singleton_family_builder_typed
          pp_t_symmetrized_singleton_family_builder_logical p])
    have collision_root:
        "pp_t_eqv pp_t_boolean_probe_unary_type []
          pp_t_probe_boolean_family_probe ?Fq"
      using UnconditionalCone.pp_t_cone_rel_eqv_iff[
        OF pp_t_probe_boolean_family_probe_in_domain
          pp_t_probe_boolean_family_probe_in_domain
          Fp Fq probe_cone family_cone,
        of "[]"]
        collision
      by simp
    have reduced:
        "pp_t_probe_boolean_stock [] ?Fq \<or> ?Fq = ?L"
      by (rule
        pp_t_probe_boolean_root_collision_reduction[
          OF q collision_root])
    from reduced show "pp_t_probe_boolean_stock w ?Fp"
    proof
      assume q_stock: "pp_t_probe_boolean_stock [] ?Fq"
      show ?thesis
        using pp_t_probe_boolean_stock_cone_iff[
          OF Fp Fq family_cone, of "[]"] q_stock
        by simp
    next
      assume q_length: "?Fq = ?L"
      have length_collision:
          "pp_t_eqv pp_t_boolean_probe_unary_type []
            pp_t_probe_boolean_family_probe ?L"
        using collision_root q_length by simp
      have length_stock: "pp_t_probe_boolean_stock [] ?L"
        using length length_collision by blast
      have q_stock: "pp_t_probe_boolean_stock [] ?Fq"
        using length_stock q_length by simp
      show ?thesis
        using pp_t_probe_boolean_stock_cone_iff[
          OF Fp Fq family_cone, of "[]"] q_stock
        by simp
    qed
  qed
qed

theorem
  pp_t_probe_boolean_family_stabilizes_iff_length_collision_absorbed:
  "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement
        pp_t_probe_boolean_stock
        pp_t_symmetrized_singleton_family_builder)
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_probe_boolean_family_probe
  \<longleftrightarrow>
  (pp_t_eqv pp_t_boolean_probe_unary_type []
      pp_t_probe_boolean_family_probe
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)
    \<longrightarrow>
    pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity))"
  using
    pp_t_probe_boolean_family_stabilizes_iff_collisions_absorbed
    pp_t_probe_boolean_all_collisions_absorbed_iff_length_collision_absorbed
  by blast

lemma pp_t_probe_boolean_length_family_no_collision:
  "\<not> pp_t_eqv pp_t_boolean_probe_unary_type []
    pp_t_probe_boolean_family_probe
    (pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity)"
proof
  assume collision:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        pp_t_probe_boolean_family_probe
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
  let ?t = "pp_t_word_character_prop True False False"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have t: "Elem ?t (pp_t_domain Prop)"
    by (rule pp_t_word_character_prop_in_domain)
  have L:
      "Elem ?L (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[
      OF pp_t_even_length_parity_in_domain])
  have equality: "pp_t_probe_boolean_family_probe = ?L"
    by (rule pp_t_root_eqv_imp_eq[
      OF pp_t_probe_boolean_family_probe_in_domain L collision])
  have family_stock:
      "pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at ?t)"
    by (rule
      pp_t_symmetrized_constant_character_family_in_boolean_stock)
  have probe_true:
      "pp_t_holds
        (pp_t_probe_boolean_family_probe \<acute> ?t) []"
    unfolding pp_t_probe_boolean_family_probe_def
    using pp_t_family_probe_for_stock_apply_holds[
        OF pp_t_symmetrized_singleton_family_builder_typed
          pp_t_probe_boolean_stock_admissible t,
        of "[]"]
      family_stock
    by simp
  have t_ne_length: "?t \<noteq> pp_t_even_length_parity"
  proof
    assume parameter: "?t = pp_t_even_length_parity"
    have at_true:
        "pp_t_holds ?t [True]
          =
          pp_t_holds pp_t_even_length_parity [True]"
      by (rule arg_cong[OF parameter])
    show False
      using at_true
      by (simp add: pp_t_even_length_parity_def)
  qed
  have t_ne_complement_length:
      "?t \<noteq> pp_t_complement pp_t_even_length_parity"
  proof
    assume parameter:
        "?t = pp_t_complement pp_t_even_length_parity"
    have at_root:
        "pp_t_holds ?t []
          =
          pp_t_holds
            (pp_t_complement pp_t_even_length_parity) []"
      by (rule arg_cong[OF parameter])
    show False
      using at_root
      by (simp add: pp_t_even_length_parity_def)
  qed
  have not_first:
      "\<not> pp_t_eqv Prop [] ?t pp_t_even_length_parity"
    using pp_t_root_eqv_iff_eq[
      OF t pp_t_even_length_parity_in_domain]
      t_ne_length by simp
  have complement_domain:
      "Elem (pp_t_complement pp_t_even_length_parity)
        (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have not_second:
      "\<not> pp_t_eqv Prop []
        ?t (pp_t_complement pp_t_even_length_parity)"
    using pp_t_root_eqv_iff_eq[OF t complement_domain]
      t_ne_complement_length by simp
  have length_false:
      "\<not> pp_t_holds (?L \<acute> ?t) []"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF pp_t_even_length_parity_in_domain t, of "[]"]
      not_first not_second
    by blast
  have applications:
      "pp_t_probe_boolean_family_probe \<acute> ?t = ?L \<acute> ?t"
    by (rule arg_cong[OF equality])
  have truth_eq:
      "pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> ?t) []
        =
        pp_t_holds (?L \<acute> ?t) []"
    by (rule arg_cong[OF applications])
  show False
    using probe_true length_false truth_eq by blast
qed

theorem pp_t_probe_boolean_family_stabilizes:
  "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement
        pp_t_probe_boolean_stock
        pp_t_symmetrized_singleton_family_builder)
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_probe_boolean_family_probe"
  using
    pp_t_probe_boolean_family_stabilizes_iff_length_collision_absorbed
    pp_t_probe_boolean_length_family_no_collision
  by blast

end
