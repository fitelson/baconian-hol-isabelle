theory Bacon_PP_ZF_Tree_One_Step_Classifier_Stock
  imports Bacon_PP_ZF_Tree_CEV_Soundness
begin

section \<open>The one-step enlargement by the old purity classifier\<close>

abbreviation pp_t_one_step_unary_type :: otype where
  "pp_t_one_step_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_one_step_classifier_type :: otype where
  "pp_t_one_step_classifier_type \<equiv>
    pp_t_one_step_unary_type \<rightarrow>\<^sub>o Prop"

definition pp_t_old_unary_stock_classifier :: ZF where
  "pp_t_old_unary_stock_classifier =
    pp_t_classifier pp_t_one_step_unary_type
      (pp_t_closed_logical_stock pp_t_one_step_unary_type)"

lemma pp_t_old_unary_stock_classifier_in_domain:
  "Elem pp_t_old_unary_stock_classifier
    (pp_t_domain pp_t_one_step_classifier_type)"
  unfolding pp_t_old_unary_stock_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_closed_logical_stock_admissible)

lemma pp_t_old_unary_stock_classifier_cone_natural:
  "pp_t_cone_rel pp_t_one_step_classifier_type s
    pp_t_old_unary_stock_classifier
    pp_t_old_unary_stock_classifier"
  unfolding pp_t_old_unary_stock_classifier_def
  by (rule pp_t_closed_logical_classifier_cone_related)

datatype pp_t_one_step_expr =
    PPOneStepLogical oterm
  | PPOneStepClassifier
  | PPOneStepApply pp_t_one_step_expr pp_t_one_step_expr

instantiation pp_t_one_step_expr :: countable
begin

instance
  by countable_datatype

end

fun pp_t_one_step_expr_type ::
    "pp_t_one_step_expr \<Rightarrow> otype option"
where
  "pp_t_one_step_expr_type (PPOneStepLogical M) =
    (if pp_logical_vocabulary M
     then infer_type [] M
     else None)"
| "pp_t_one_step_expr_type PPOneStepClassifier =
    Some pp_t_one_step_classifier_type"
| "pp_t_one_step_expr_type (PPOneStepApply F X) =
    (case pp_t_one_step_expr_type F of
      Some (\<sigma> \<rightarrow>\<^sub>o \<tau>) =>
        (if pp_t_one_step_expr_type X = Some \<sigma>
         then Some \<tau> else None)
    | _ => None)"

fun pp_t_one_step_expr_den ::
    "pp_t_one_step_expr \<Rightarrow> ZF"
where
  "pp_t_one_step_expr_den (PPOneStepLogical M) =
    pp_t_closed_den M"
| "pp_t_one_step_expr_den PPOneStepClassifier =
    pp_t_old_unary_stock_classifier"
| "pp_t_one_step_expr_den (PPOneStepApply F X) =
    pp_t_one_step_expr_den F \<acute> pp_t_one_step_expr_den X"

fun pp_t_one_step_context_body ::
    "pp_t_one_step_expr \<Rightarrow> oterm"
where
  "pp_t_one_step_context_body (PPOneStepLogical M) = shift M"
| "pp_t_one_step_context_body PPOneStepClassifier = Var 0"
| "pp_t_one_step_context_body (PPOneStepApply F X) =
    App (pp_t_one_step_context_body F)
      (pp_t_one_step_context_body X)"

definition pp_t_one_step_context :: "pp_t_one_step_expr \<Rightarrow> oterm"
where
  "pp_t_one_step_context T =
    Lam pp_t_one_step_classifier_type
      (pp_t_one_step_context_body T)"

definition pp_t_one_step_basis :: "otype \<Rightarrow> ZF set" where
  "pp_t_one_step_basis \<sigma> =
    pp_t_one_step_expr_den `
      {T. pp_t_one_step_expr_type T = Some \<sigma>}"

lemma pp_t_one_step_context_body_typed:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "[pp_t_one_step_classifier_type]
    \<turnstile> pp_t_one_step_context_body T : \<sigma>"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPOneStepLogical M)
  then have inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have "[] \<turnstile> M : \<sigma>"
    using inferred by (rule infer_type_sound)
  then show ?case
    by (simp add: weakening_front)
next
  case PPOneStepClassifier
  then show ?case
    by (auto intro: has_type.Var)
next
  case (PPOneStepApply F X)
  then obtain \<alpha> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    by (auto split: option.splits otype.splits if_splits)
  have F_typed:
      "[pp_t_one_step_classifier_type]
        \<turnstile> pp_t_one_step_context_body F :
          \<alpha> \<rightarrow>\<^sub>o \<sigma>"
    using PPOneStepApply.IH(1)[OF F_type] .
  have X_typed:
      "[pp_t_one_step_classifier_type]
        \<turnstile> pp_t_one_step_context_body X : \<alpha>"
    using PPOneStepApply.IH(2)[OF X_type] .
  show ?case
    using F_typed X_typed by (simp add: has_type.App)
qed

lemma pp_t_one_step_context_typed:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "[] \<turnstile> pp_t_one_step_context T :
    pp_t_one_step_classifier_type \<rightarrow>\<^sub>o \<sigma>"
  unfolding pp_t_one_step_context_def
  using pp_t_one_step_context_body_typed[OF T]
  by (rule has_type.Lam)

lemma pp_t_one_step_context_body_logical:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "pp_logical_vocabulary (pp_t_one_step_context_body T)"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPOneStepLogical M)
  then have logical: "pp_logical_vocabulary M"
    by (auto split: if_splits)
  show ?case
    using logical
    by (simp add: pp_logical_vocabulary_def shift_def)
next
  case PPOneStepClassifier
  then show ?case
    by (simp add: pp_logical_vocabulary_def)
next
  case (PPOneStepApply F X)
  then obtain \<alpha> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    by (auto split: option.splits otype.splits if_splits)
  have F_logical:
      "pp_logical_vocabulary (pp_t_one_step_context_body F)"
    using PPOneStepApply.IH(1)[OF F_type] .
  have X_logical:
      "pp_logical_vocabulary (pp_t_one_step_context_body X)"
    using PPOneStepApply.IH(2)[OF X_type] .
  show ?case
    using F_logical X_logical
    by (simp add: pp_logical_vocabulary_def)
qed

lemma pp_t_one_step_context_logical:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "pp_logical_vocabulary (pp_t_one_step_context T)"
  unfolding pp_t_one_step_context_def
    pp_logical_vocabulary_def
  using pp_t_one_step_context_body_logical[OF T]
  unfolding pp_logical_vocabulary_def
  by simp

lemma pp_t_one_step_context_body_den:
  "pp_t_eval pp_t_default_constants
      (extend_env pp_t_old_unary_stock_classifier pp_t_closed_env)
      (pp_t_one_step_context_body T)
    = pp_t_one_step_expr_den T"
proof (induction T)
  case (PPOneStepLogical M)
  then show ?case
    by (simp add: pp_t_closed_den_def pp_t_eval_shift)
next
  case PPOneStepClassifier
  then show ?case by simp
next
  case (PPOneStepApply F X)
  then show ?case by simp
qed

lemma pp_t_one_step_context_applied:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "pp_t_closed_den (pp_t_one_step_context T)
      \<acute> pp_t_old_unary_stock_classifier
    = pp_t_one_step_expr_den T"
  unfolding pp_t_closed_den_def pp_t_one_step_context_def
  using pp_t_old_unary_stock_classifier_in_domain
    pp_t_one_step_context_body_den[of T]
  by (simp add: Lambda_app)

lemma pp_t_one_step_expr_den_typed:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "Elem (pp_t_one_step_expr_den T) (pp_t_domain \<sigma>)"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPOneStepLogical M)
  then have logical: "pp_logical_vocabulary M"
    and inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have typed: "[] \<turnstile> M : \<sigma>"
    using infer_type_sound[OF inferred] .
  show ?case
    using pp_t_closed_den_in_domain[OF typed] by simp
next
  case PPOneStepClassifier
  then have "\<sigma> = pp_t_one_step_classifier_type"
    by simp
  then show ?case
    using pp_t_old_unary_stock_classifier_in_domain by simp
next
  case (PPOneStepApply F X)
  then obtain \<alpha> \<beta> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    and sigma: "\<sigma> = \<beta>"
    by (auto split: option.splits otype.splits if_splits)
  have F_den:
      "Elem (pp_t_one_step_expr_den F)
        (pp_t_domain (\<alpha> \<rightarrow>\<^sub>o \<beta>))"
    using PPOneStepApply.IH(1)[OF F_type] .
  have X_den:
      "Elem (pp_t_one_step_expr_den X) (pp_t_domain \<alpha>)"
    using PPOneStepApply.IH(2)[OF X_type] .
  show ?case
    unfolding sigma pp_t_one_step_expr_den.simps
    using pp_t_app_closed[OF F_den X_den] .
qed

lemma pp_t_one_step_expr_den_cone_natural:
  assumes T: "pp_t_one_step_expr_type T = Some \<sigma>"
  shows "pp_t_cone_rel \<sigma> s
    (pp_t_one_step_expr_den T)
    (pp_t_one_step_expr_den T)"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPOneStepLogical M)
  then have logical: "pp_logical_vocabulary M"
    and inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have typed: "[] \<turnstile> M : \<sigma>"
    using infer_type_sound[OF inferred] .
  show ?case
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] by simp
next
  case PPOneStepClassifier
  then have "\<sigma> = pp_t_one_step_classifier_type"
    by simp
  then show ?case
    using pp_t_old_unary_stock_classifier_cone_natural by simp
next
  case (PPOneStepApply F X)
  then obtain \<alpha> \<beta> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    and sigma: "\<sigma> = \<beta>"
    by (auto split: option.splits otype.splits if_splits)
  have F_rel:
      "pp_t_cone_rel (\<alpha> \<rightarrow>\<^sub>o \<beta>) s
        (pp_t_one_step_expr_den F)
        (pp_t_one_step_expr_den F)"
    using PPOneStepApply.IH(1)[OF F_type] .
  have X_rel:
      "pp_t_cone_rel \<alpha> s
        (pp_t_one_step_expr_den X)
        (pp_t_one_step_expr_den X)"
    using PPOneStepApply.IH(2)[OF X_type] .
  have X_den:
      "Elem (pp_t_one_step_expr_den X) (pp_t_domain \<alpha>)"
    using pp_t_one_step_expr_den_typed[OF X_type] .
  show ?case
    unfolding sigma pp_t_one_step_expr_den.simps
    using F_rel X_den X_rel by simp
qed

lemma pp_t_one_step_basis_typed:
  assumes d: "d \<in> pp_t_one_step_basis \<sigma>"
  shows "Elem d (pp_t_domain \<sigma>)"
proof -
  obtain T where T: "pp_t_one_step_expr_type T = Some \<sigma>"
    and d: "d = pp_t_one_step_expr_den T"
    using d unfolding pp_t_one_step_basis_def
    by (rule imageE) auto
  show ?thesis
    unfolding d
    using pp_t_one_step_expr_den_typed[OF T] .
qed

lemma pp_t_one_step_basis_countable:
  "countable (pp_t_one_step_basis \<sigma>)"
proof -
  have "countable
      ({T. pp_t_one_step_expr_type T = Some \<sigma>} ::
        pp_t_one_step_expr set)"
    by simp
  then show ?thesis
    unfolding pp_t_one_step_basis_def
    by (rule countable_image)
qed

lemma pp_t_one_step_basis_cone_natural:
  assumes d: "d \<in> pp_t_one_step_basis \<sigma>"
  shows "pp_t_cone_rel \<sigma> s d d"
proof -
  obtain T where T: "pp_t_one_step_expr_type T = Some \<sigma>"
    and d: "d = pp_t_one_step_expr_den T"
    using d unfolding pp_t_one_step_basis_def
    by (rule imageE) auto
  show ?thesis
    unfolding d
    using pp_t_one_step_expr_den_cone_natural[OF T] .
qed

lemma pp_t_one_step_basis_contains_logical:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_closed_den M \<in> pp_t_one_step_basis \<sigma>"
proof -
  have inferred: "infer_type [] M = Some \<sigma>"
    using infer_type_complete[OF typed] .
  have expression:
      "pp_t_one_step_expr_type (PPOneStepLogical M) = Some \<sigma>"
    using logical inferred by simp
  show ?thesis
    unfolding pp_t_one_step_basis_def
  proof (rule image_eqI[where x="PPOneStepLogical M"])
    show "pp_t_closed_den M =
        pp_t_one_step_expr_den (PPOneStepLogical M)"
      by simp
    show "PPOneStepLogical M \<in>
        {T. pp_t_one_step_expr_type T = Some \<sigma>}"
      using expression by simp
  qed
qed

lemma pp_t_old_classifier_in_one_step_basis:
  "pp_t_old_unary_stock_classifier
    \<in> pp_t_one_step_basis pp_t_one_step_classifier_type"
  unfolding pp_t_one_step_basis_def
  by (rule image_eqI[where x=PPOneStepClassifier]) simp_all

lemma pp_t_one_step_basis_application:
  assumes f:
      "f \<in> pp_t_one_step_basis (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and x: "x \<in> pp_t_one_step_basis \<sigma>"
  shows "f \<acute> x \<in> pp_t_one_step_basis \<tau>"
proof -
  obtain F where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and f: "f = pp_t_one_step_expr_den F"
    using f unfolding pp_t_one_step_basis_def
    by (rule imageE) auto
  obtain X where X_type:
      "pp_t_one_step_expr_type X = Some \<sigma>"
    and x: "x = pp_t_one_step_expr_den X"
    using x unfolding pp_t_one_step_basis_def
    by (rule imageE) auto
  have app_type:
      "pp_t_one_step_expr_type (PPOneStepApply F X) = Some \<tau>"
    using F_type X_type by simp
  show ?thesis
    unfolding pp_t_one_step_basis_def f x
  proof (rule image_eqI[where x="PPOneStepApply F X"])
    show "pp_t_one_step_expr_den F \<acute>
        pp_t_one_step_expr_den X =
      pp_t_one_step_expr_den (PPOneStepApply F X)"
      by simp
    show "PPOneStepApply F X \<in>
        {T. pp_t_one_step_expr_type T = Some \<tau>}"
      using app_type by simp
  qed
qed

interpretation OneStepBasis:
  pp_t_stock_basis pp_t_one_step_basis
proof
  fix \<sigma> d
  assume "d \<in> pp_t_one_step_basis \<sigma>"
  then show "Elem d (pp_t_domain \<sigma>)"
    by (rule pp_t_one_step_basis_typed)
next
  fix \<sigma>
  show "countable (pp_t_one_step_basis \<sigma>)"
    by (rule pp_t_one_step_basis_countable)
next
  fix \<sigma> d s
  assume "d \<in> pp_t_one_step_basis \<sigma>"
  then show "pp_t_cone_rel \<sigma> s d d"
    by (rule pp_t_one_step_basis_cone_natural)
next
  fix \<sigma> M
  assume typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  show "pp_t_closed_den M \<in> pp_t_one_step_basis \<sigma>"
    using typed logical by (rule pp_t_one_step_basis_contains_logical)
next
  fix \<sigma> \<tau> f x
  assume f:
      "f \<in> pp_t_one_step_basis (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and x: "x \<in> pp_t_one_step_basis \<sigma>"
  have application:
      "f \<acute> x \<in> pp_t_one_step_basis \<tau>"
    using f x by (rule pp_t_one_step_basis_application)
  have typed:
      "Elem (f \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_one_step_basis_typed[OF application] .
  have reflexive:
      "pp_t_eqv \<tau> [] (f \<acute> x) (f \<acute> x)"
    using pp_t_eqv_reflexive[OF typed] .
  show "\<exists>d \<in> pp_t_one_step_basis \<tau>.
      pp_t_eqv \<tau> [] (f \<acute> x) d"
    using application reflexive by blast
qed

interpretation OneStepConstants:
  pp_t_constants
    "pp_t_seeded_internal_constants
      (pp_t_basis_stock pp_t_one_step_basis)
      OneStepBasis.pp_t_basis_seed_at"
  by standard
    (rule
      OneStepBasis.BasisSeeded.pp_t_seeded_internal_constants_typed)

section \<open>Unary stabilization and self-classification\<close>

definition pp_t_one_step_unary_stabilizes :: bool where
  "pp_t_one_step_unary_stabilizes \<longleftrightarrow>
    (\<forall>w X.
      pp_t_basis_stock pp_t_one_step_basis
          pp_t_one_step_unary_type w X
      \<longleftrightarrow>
      pp_t_closed_logical_stock
          pp_t_one_step_unary_type w X)"

definition pp_t_one_step_unary_eliminates_classifier :: bool where
  "pp_t_one_step_unary_eliminates_classifier \<longleftrightarrow>
    (\<forall>T.
      pp_t_one_step_expr_type T =
        Some pp_t_one_step_unary_type
      \<longrightarrow>
      (\<exists>M.
        [] \<turnstile> M : pp_t_one_step_unary_type
        \<and> pp_logical_vocabulary M
        \<and> pp_t_one_step_expr_den T = pp_t_closed_den M))"

definition pp_t_one_step_unary_context_conservative :: bool where
  "pp_t_one_step_unary_context_conservative \<longleftrightarrow>
    (\<forall>G.
      [] \<turnstile> G :
        pp_t_one_step_classifier_type
          \<rightarrow>\<^sub>o pp_t_one_step_unary_type
      \<longrightarrow>
      pp_logical_vocabulary G
      \<longrightarrow>
      (\<exists>M.
        [] \<turnstile> M : pp_t_one_step_unary_type
        \<and> pp_logical_vocabulary M
        \<and> pp_t_closed_den G
              \<acute> pp_t_old_unary_stock_classifier
            = pp_t_closed_den M))"

lemma pp_t_one_step_unary_stabilizes_predicate_eq:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "pp_t_basis_stock pp_t_one_step_basis
      pp_t_one_step_unary_type =
    pp_t_closed_logical_stock pp_t_one_step_unary_type"
proof (rule ext)+
  fix w X
  show "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type w X =
      pp_t_closed_logical_stock
        pp_t_one_step_unary_type w X"
    using stabilization
    unfolding pp_t_one_step_unary_stabilizes_def
    by blast
qed

lemma pp_t_one_step_stabilization_implies_elimination:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "pp_t_one_step_unary_eliminates_classifier"
    unfolding pp_t_one_step_unary_eliminates_classifier_def
proof (intro allI impI)
  fix T
  assume T:
      "pp_t_one_step_expr_type T =
        Some pp_t_one_step_unary_type"
  let ?d = "pp_t_one_step_expr_den T"
  have d_basis:
      "?d \<in> pp_t_one_step_basis pp_t_one_step_unary_type"
    unfolding pp_t_one_step_basis_def
  proof (rule image_eqI[where x=T])
    show "?d = pp_t_one_step_expr_den T" by simp
    show "T \<in>
        {U. pp_t_one_step_expr_type U =
          Some pp_t_one_step_unary_type}"
      using T by simp
  qed
  have d_stock:
      "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type [] ?d"
    using OneStepBasis.pp_t_basis_member_in_stock[
      OF d_basis] .
  have d_old:
      "pp_t_closed_logical_stock
        pp_t_one_step_unary_type [] ?d"
    using stabilization d_stock
    unfolding pp_t_one_step_unary_stabilizes_def
    by blast
  then obtain M where
      M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and dM:
      "pp_t_eqv pp_t_one_step_unary_type []
        ?d (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have d_typed:
      "Elem ?d (pp_t_domain pp_t_one_step_unary_type)"
    using pp_t_one_step_expr_den_typed[OF T] .
  have M_den_typed:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_step_unary_type)"
    using pp_t_closed_den_in_domain[OF M_typed] .
  have equality: "?d = pp_t_closed_den M"
    using pp_t_root_eqv_iff_eq[
      OF d_typed M_den_typed] dM by blast
  show "\<exists>M.
      [] \<turnstile> M : pp_t_one_step_unary_type
      \<and> pp_logical_vocabulary M
      \<and> ?d = pp_t_closed_den M"
    using M_typed M_logical equality by blast
qed

lemma pp_t_one_step_elimination_implies_stabilization:
  assumes elimination:
      "pp_t_one_step_unary_eliminates_classifier"
  shows "pp_t_one_step_unary_stabilizes"
  unfolding pp_t_one_step_unary_stabilizes_def
proof (intro allI)
  fix w X
  show "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type w X
      \<longleftrightarrow>
      pp_t_closed_logical_stock
        pp_t_one_step_unary_type w X"
  proof
    assume X_stock:
        "pp_t_basis_stock pp_t_one_step_basis
          pp_t_one_step_unary_type w X"
    then obtain d where X_typed:
        "Elem X (pp_t_domain pp_t_one_step_unary_type)"
      and d_basis:
        "d \<in> pp_t_one_step_basis pp_t_one_step_unary_type"
      and Xd:
        "pp_t_eqv pp_t_one_step_unary_type w X d"
      unfolding pp_t_basis_stock_def by blast
    obtain T where T:
        "pp_t_one_step_expr_type T =
          Some pp_t_one_step_unary_type"
      and d: "d = pp_t_one_step_expr_den T"
      using d_basis unfolding pp_t_one_step_basis_def
      by (rule imageE) auto
    obtain M where
        M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
      and M_logical: "pp_logical_vocabulary M"
      and TM:
        "pp_t_one_step_expr_den T = pp_t_closed_den M"
      using elimination T
      unfolding pp_t_one_step_unary_eliminates_classifier_def
      by blast
    have XM:
        "pp_t_eqv pp_t_one_step_unary_type w
          X (pp_t_closed_den M)"
      using Xd unfolding d TM .
    show "pp_t_closed_logical_stock
        pp_t_one_step_unary_type w X"
      unfolding pp_t_closed_logical_stock_def
      using X_typed M_typed M_logical XM by blast
  next
    assume X_old:
        "pp_t_closed_logical_stock
          pp_t_one_step_unary_type w X"
    then obtain M where X_typed:
        "Elem X (pp_t_domain pp_t_one_step_unary_type)"
      and M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
      and M_logical: "pp_logical_vocabulary M"
      and XM:
        "pp_t_eqv pp_t_one_step_unary_type w
          X (pp_t_closed_den M)"
      unfolding pp_t_closed_logical_stock_def by blast
    have M_basis:
        "pp_t_closed_den M
          \<in> pp_t_one_step_basis pp_t_one_step_unary_type"
      using M_typed M_logical
      by (rule pp_t_one_step_basis_contains_logical)
    show "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type w X"
      unfolding pp_t_basis_stock_def
      using X_typed M_basis XM by blast
  qed
qed

theorem pp_t_one_step_stabilizes_iff_eliminates_classifier:
  "pp_t_one_step_unary_stabilizes
    \<longleftrightarrow>
    pp_t_one_step_unary_eliminates_classifier"
  using pp_t_one_step_stabilization_implies_elimination
    pp_t_one_step_elimination_implies_stabilization
  by blast

lemma pp_t_one_step_elimination_implies_context_conservativity:
  assumes elimination:
      "pp_t_one_step_unary_eliminates_classifier"
  shows "pp_t_one_step_unary_context_conservative"
  unfolding pp_t_one_step_unary_context_conservative_def
proof (intro allI impI)
  fix G
  assume G_typed:
      "[] \<turnstile> G :
        pp_t_one_step_classifier_type
          \<rightarrow>\<^sub>o pp_t_one_step_unary_type"
    and G_logical: "pp_logical_vocabulary G"
  let ?T =
    "PPOneStepApply (PPOneStepLogical G) PPOneStepClassifier"
  have T_type:
      "pp_t_one_step_expr_type ?T =
        Some pp_t_one_step_unary_type"
    using infer_type_complete[OF G_typed] G_logical by simp
  obtain M where
      M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and TM: "pp_t_one_step_expr_den ?T = pp_t_closed_den M"
    using elimination[unfolded
      pp_t_one_step_unary_eliminates_classifier_def,
      rule_format, OF T_type]
    by blast
  show "\<exists>M.
      [] \<turnstile> M : pp_t_one_step_unary_type
      \<and> pp_logical_vocabulary M
      \<and> pp_t_closed_den G
            \<acute> pp_t_old_unary_stock_classifier
          = pp_t_closed_den M"
    apply (rule exI[where x=M])
    using M_typed M_logical TM
    by simp
qed

lemma pp_t_one_step_context_conservativity_implies_elimination:
  assumes conservative:
      "pp_t_one_step_unary_context_conservative"
  shows "pp_t_one_step_unary_eliminates_classifier"
  unfolding pp_t_one_step_unary_eliminates_classifier_def
proof (intro allI impI)
  fix T
  assume T_type:
      "pp_t_one_step_expr_type T =
        Some pp_t_one_step_unary_type"
  have G_typed:
      "[] \<turnstile> pp_t_one_step_context T :
        pp_t_one_step_classifier_type
          \<rightarrow>\<^sub>o pp_t_one_step_unary_type"
    using pp_t_one_step_context_typed[OF T_type] .
  have G_logical:
      "pp_logical_vocabulary (pp_t_one_step_context T)"
    using pp_t_one_step_context_logical[OF T_type] .
  obtain M where
      M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and GM:
      "pp_t_closed_den (pp_t_one_step_context T)
          \<acute> pp_t_old_unary_stock_classifier
        = pp_t_closed_den M"
    using conservative[unfolded
      pp_t_one_step_unary_context_conservative_def,
      rule_format, OF G_typed G_logical]
    by blast
  have TM:
      "pp_t_one_step_expr_den T = pp_t_closed_den M"
    using pp_t_one_step_context_applied[OF T_type] GM
    by simp
  show "\<exists>M.
      [] \<turnstile> M : pp_t_one_step_unary_type
      \<and> pp_logical_vocabulary M
      \<and> pp_t_one_step_expr_den T = pp_t_closed_den M"
    apply (rule exI[where x=M])
    using M_typed M_logical TM
    by simp
qed

theorem pp_t_one_step_stabilizes_iff_context_conservative:
  "pp_t_one_step_unary_stabilizes
    \<longleftrightarrow>
    pp_t_one_step_unary_context_conservative"
  using pp_t_one_step_stabilization_implies_elimination
    pp_t_one_step_elimination_implies_context_conservativity
    pp_t_one_step_context_conservativity_implies_elimination
    pp_t_one_step_elimination_implies_stabilization
  by blast

lemma pp_t_one_step_classifier_eq_old:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "pp_t_classifier pp_t_one_step_unary_type
      (pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type)
    = pp_t_old_unary_stock_classifier"
  unfolding pp_t_old_unary_stock_classifier_def
  using pp_t_one_step_unary_stabilizes_predicate_eq[
    OF stabilization]
  by simp

theorem pp_t_one_step_stabilization_self_classifies:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "pp_t_basis_stock pp_t_one_step_basis
    pp_t_one_step_classifier_type []
    (pp_t_classifier pp_t_one_step_unary_type
      (pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_unary_type))"
proof -
  have old_in:
      "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_classifier_type []
        pp_t_old_unary_stock_classifier"
    using OneStepBasis.pp_t_basis_member_in_stock[
      OF pp_t_old_classifier_in_one_step_basis] .
  show ?thesis
    unfolding pp_t_one_step_classifier_eq_old[
      OF stabilization]
    using old_in .
qed

section \<open>The first classifier-elimination test\<close>

definition pp_t_one_step_singleton_test_builder :: oterm where
  "pp_t_one_step_singleton_test_builder =
    Lam pp_t_one_step_classifier_type
      (Lam Prop
        (App (Var 1)
          (Lam Prop
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1))))))"

lemma pp_t_one_step_singleton_test_builder_typed:
  "[] \<turnstile> pp_t_one_step_singleton_test_builder :
    pp_t_one_step_classifier_type
      \<rightarrow>\<^sub>o pp_t_one_step_unary_type"
  unfolding pp_t_one_step_singleton_test_builder_def
  apply (rule has_type.Lam)
  apply (rule has_type.Lam)
  apply (rule has_type.App)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Lam)
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
  done

lemma pp_t_one_step_singleton_test_builder_logical:
  "pp_logical_vocabulary pp_t_one_step_singleton_test_builder"
  unfolding pp_t_one_step_singleton_test_builder_def
    pp_logical_vocabulary_def
  by simp

definition pp_t_one_step_singleton_test :: ZF where
  "pp_t_one_step_singleton_test =
    pp_t_closed_den pp_t_one_step_singleton_test_builder
      \<acute> pp_t_old_unary_stock_classifier"

lemma pp_t_one_step_singleton_test_in_basis:
  "pp_t_one_step_singleton_test
    \<in> pp_t_one_step_basis pp_t_one_step_unary_type"
proof -
  have builder:
      "pp_t_closed_den pp_t_one_step_singleton_test_builder
        \<in> pp_t_one_step_basis
          (pp_t_one_step_classifier_type
            \<rightarrow>\<^sub>o pp_t_one_step_unary_type)"
    using pp_t_one_step_singleton_test_builder_typed
      pp_t_one_step_singleton_test_builder_logical
    by (rule pp_t_one_step_basis_contains_logical)
  show ?thesis
    unfolding pp_t_one_step_singleton_test_def
    using pp_t_one_step_basis_application[
      OF builder pp_t_old_classifier_in_one_step_basis] .
qed

corollary pp_t_one_step_stabilization_forces_singleton_test_logical:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "\<exists>M.
    [] \<turnstile> M : pp_t_one_step_unary_type
    \<and> pp_logical_vocabulary M
    \<and> pp_t_one_step_singleton_test = pp_t_closed_den M"
proof -
  have elimination:
      "pp_t_one_step_unary_eliminates_classifier"
    using stabilization
    by (rule pp_t_one_step_stabilization_implies_elimination)
  obtain T where T:
      "pp_t_one_step_expr_type T =
        Some pp_t_one_step_unary_type"
    and test: "pp_t_one_step_singleton_test =
      pp_t_one_step_expr_den T"
    using pp_t_one_step_singleton_test_in_basis
    unfolding pp_t_one_step_basis_def
    by (rule imageE) auto
  obtain M where
      M_typed: "[] \<turnstile> M : pp_t_one_step_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and TM: "pp_t_one_step_expr_den T = pp_t_closed_den M"
    using elimination[unfolded
      pp_t_one_step_unary_eliminates_classifier_def,
      rule_format, OF T]
    by blast
  show ?thesis
    apply (rule exI[where x=M])
    using M_typed M_logical test TM
    by simp
qed

theorem pp_t_one_step_stabilization_gives_PP_model:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows
    "OneStepConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms"
  using OneStepBasis.pp_t_basis_recombination_PP_gvalid_iff_root
    pp_t_one_step_stabilization_self_classifies[
      OF stabilization]
  by simp

theorem pp_t_one_step_stabilization_answers_Goodman:
  assumes stabilization: "pp_t_one_step_unary_stabilizes"
  shows "pp_recombination_axiom_consistency_question"
proof -
  have axioms:
      "OneStepConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
    using stabilization
    by (rule pp_t_one_step_stabilization_gives_PP_model)
  show ?thesis
    using
      OneStepConstants.pp_t_base_sound
      OneStepConstants.pp_t_zeta_sound
      axioms
    by (rule
      OneStepConstants.TreeHenkin.pp_recombination_question_of_gvalid)
qed

theorem pp_t_full_closed_logical_stock_one_step_stabilization:
  assumes collapse:
    "\<And>T. pp_t_one_step_expr_type T =
        Some pp_t_one_step_unary_type
      \<Longrightarrow> \<exists>M.
        [] \<turnstile> M : pp_t_one_step_unary_type
        \<and> pp_logical_vocabulary M
        \<and> pp_t_one_step_expr_den T = pp_t_closed_den M"
  shows stabilization: "pp_t_one_step_unary_stabilizes"
    and self_classification:
      "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_classifier_type []
        (pp_t_classifier pp_t_one_step_unary_type
          (pp_t_basis_stock pp_t_one_step_basis
            pp_t_one_step_unary_type))"
    and PP_model:
      "OneStepConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
    and consistency:
      "pp_recombination_axiom_consistency_question"
proof -
  have elimination:
      "pp_t_one_step_unary_eliminates_classifier"
    unfolding pp_t_one_step_unary_eliminates_classifier_def
    using collapse by blast
  show stabilization: "pp_t_one_step_unary_stabilizes"
    using elimination
    by (rule pp_t_one_step_elimination_implies_stabilization)
  show self_classification:
      "pp_t_basis_stock pp_t_one_step_basis
        pp_t_one_step_classifier_type []
        (pp_t_classifier pp_t_one_step_unary_type
          (pp_t_basis_stock pp_t_one_step_basis
            pp_t_one_step_unary_type))"
    using stabilization
    by (rule pp_t_one_step_stabilization_self_classifies)
  show PP_model:
      "OneStepConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
    using stabilization
    by (rule pp_t_one_step_stabilization_gives_PP_model)
  show consistency:
      "pp_recombination_axiom_consistency_question"
    using stabilization
    by (rule pp_t_one_step_stabilization_answers_Goodman)
qed

end
