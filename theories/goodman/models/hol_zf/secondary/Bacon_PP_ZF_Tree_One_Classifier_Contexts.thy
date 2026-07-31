theory Bacon_PP_ZF_Tree_One_Classifier_Contexts
  imports Bacon_PP_ZF_Tree_One_Step_Classifier_Stock
begin

section \<open>One occurrence of the unary purity classifier\<close>

text \<open>
  We begin with contexts in which the old unary purity classifier occurs
  exactly once and outside the scope of object-language quantifiers.  The
  first distinction is whether the classifier is applied to a fixed closed
  logical operator or to an operator depending on the eventual proposition
  argument.
\<close>

abbreviation pp_t_one_context_unary_type :: otype where
  "pp_t_one_context_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_one_context_classifier_type :: otype where
  "pp_t_one_context_classifier_type \<equiv>
    pp_t_one_context_unary_type \<rightarrow>\<^sub>o Prop"

fun pp_t_classifier_occurrences ::
    "pp_t_one_step_expr \<Rightarrow> nat"
where
  "pp_t_classifier_occurrences (PPOneStepLogical M) = 0"
| "pp_t_classifier_occurrences PPOneStepClassifier = 1"
| "pp_t_classifier_occurrences (PPOneStepApply F X) =
    pp_t_classifier_occurrences F
      + pp_t_classifier_occurrences X"

text \<open>
  The datatype contains only closed logical leaves, the classifier leaf, and
  application.  Thus an occurrence counted here cannot lie in the scope of a
  quantifier contributed by another leaf.  Count one therefore captures the
  promised first stratum: a unique classifier occurrence, with every branch
  off its application spine classifier-free.
\<close>

lemma pp_t_one_classifier_application_split:
  "pp_t_classifier_occurrences (PPOneStepApply F X) = 1
    \<longleftrightarrow>
    (pp_t_classifier_occurrences F = 1
      \<and> pp_t_classifier_occurrences X = 0)
    \<or>
    (pp_t_classifier_occurrences F = 0
      \<and> pp_t_classifier_occurrences X = 1)"
  by auto

lemma pp_t_classifier_free_eliminates:
  assumes T_type: "pp_t_one_step_expr_type T = Some \<sigma>"
    and T_free: "pp_t_classifier_occurrences T = 0"
  shows "\<exists>M.
    [] \<turnstile> M : \<sigma>
    \<and> pp_logical_vocabulary M
    \<and> pp_t_one_step_expr_den T = pp_t_closed_den M"
  using T_type T_free
proof (induction T arbitrary: \<sigma>)
  case (PPOneStepLogical M)
  then have logical: "pp_logical_vocabulary M"
    and inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have typed: "[] \<turnstile> M : \<sigma>"
    using inferred by (rule infer_type_sound)
  show ?case
    using typed logical by auto
next
  case PPOneStepClassifier
  then show ?case by simp
next
  case (PPOneStepApply F X)
  then obtain \<alpha> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    by (auto split: option.splits otype.splits if_splits)
  have F_free: "pp_t_classifier_occurrences F = 0"
    and X_free: "pp_t_classifier_occurrences X = 0"
    using PPOneStepApply.prems(2) by simp_all
  obtain A where
      A_typed: "[] \<turnstile> A : \<alpha> \<rightarrow>\<^sub>o \<sigma>"
    and A_logical: "pp_logical_vocabulary A"
    and FA: "pp_t_one_step_expr_den F = pp_t_closed_den A"
    using PPOneStepApply.IH(1)[OF F_type F_free] by blast
  obtain B where
      B_typed: "[] \<turnstile> B : \<alpha>"
    and B_logical: "pp_logical_vocabulary B"
    and XB: "pp_t_one_step_expr_den X = pp_t_closed_den B"
    using PPOneStepApply.IH(2)[OF X_type X_free] by blast
  have app_typed: "[] \<turnstile> App A B : \<sigma>"
    using A_typed B_typed by (rule has_type.App)
  have app_logical: "pp_logical_vocabulary (App A B)"
    using A_logical B_logical
    by (simp add: pp_logical_vocabulary_def)
  have den:
      "pp_t_one_step_expr_den (PPOneStepApply F X) =
        pp_t_closed_den (App A B)"
    using FA XB by (simp add: pp_t_closed_den_def)
  show ?case
    using app_typed app_logical den by blast
qed

theorem pp_t_one_classifier_spine_classification:
  assumes T_type: "pp_t_one_step_expr_type T = Some \<sigma>"
    and T_one: "pp_t_classifier_occurrences T = 1"
  obtains
    (classifier) "T = PPOneStepClassifier"
  | (left) F X \<alpha> M where
      "T = PPOneStepApply F X"
      "pp_t_classifier_occurrences F = 1"
      "pp_t_one_step_expr_type F =
        Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
      "pp_t_one_step_expr_type X = Some \<alpha>"
      "[] \<turnstile> M : \<alpha>"
      "pp_logical_vocabulary M"
      "pp_t_one_step_expr_den X = pp_t_closed_den M"
  | (right) F X \<alpha> M where
      "T = PPOneStepApply F X"
      "pp_t_classifier_occurrences X = 1"
      "pp_t_one_step_expr_type F =
        Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
      "pp_t_one_step_expr_type X = Some \<alpha>"
      "[] \<turnstile> M : \<alpha> \<rightarrow>\<^sub>o \<sigma>"
      "pp_logical_vocabulary M"
      "pp_t_one_step_expr_den F = pp_t_closed_den M"
proof (cases T)
  case (PPOneStepLogical M)
  then show ?thesis
    using T_one by simp
next
  case PPOneStepClassifier
  then show ?thesis
    by (rule classifier)
next
  case (PPOneStepApply F X)
  then obtain \<alpha> where
      F_type:
        "pp_t_one_step_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<sigma>)"
    and X_type: "pp_t_one_step_expr_type X = Some \<alpha>"
    using T_type
    by (auto split: option.splits otype.splits if_splits)
  have split:
      "(pp_t_classifier_occurrences F = 1
          \<and> pp_t_classifier_occurrences X = 0)
        \<or>
       (pp_t_classifier_occurrences F = 0
          \<and> pp_t_classifier_occurrences X = 1)"
    using T_one unfolding PPOneStepApply
    by (simp only: pp_t_one_classifier_application_split)
  then show ?thesis
  proof
    assume left_case:
        "pp_t_classifier_occurrences F = 1
          \<and> pp_t_classifier_occurrences X = 0"
    obtain M where
        M_typed: "[] \<turnstile> M : \<alpha>"
      and M_logical: "pp_logical_vocabulary M"
      and XM: "pp_t_one_step_expr_den X = pp_t_closed_den M"
      using pp_t_classifier_free_eliminates[
        OF X_type left_case[THEN conjunct2]]
      by blast
    show ?thesis
      using left[OF PPOneStepApply left_case[THEN conjunct1]
        F_type X_type M_typed M_logical XM] .
  next
    assume right_case:
        "pp_t_classifier_occurrences F = 0
          \<and> pp_t_classifier_occurrences X = 1"
    obtain M where
        M_typed:
          "[] \<turnstile> M : \<alpha> \<rightarrow>\<^sub>o \<sigma>"
      and M_logical: "pp_logical_vocabulary M"
      and FM: "pp_t_one_step_expr_den F = pp_t_closed_den M"
      using pp_t_classifier_free_eliminates[
        OF F_type right_case[THEN conjunct1]]
      by blast
    show ?thesis
      using right[OF PPOneStepApply right_case[THEN conjunct2]
        F_type X_type M_typed M_logical FM] .
  qed
qed

subsection \<open>Fixed closed logical arguments\<close>

lemma pp_t_old_classifier_accepts_closed_logical:
  assumes M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
  shows "pp_t_old_unary_stock_classifier
      \<acute> pp_t_closed_den M
    = pp_zf_truth True"
proof (rule pp_t_prop_ext)
  show "Elem
      (pp_t_old_unary_stock_classifier \<acute> pp_t_closed_den M)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_old_unary_stock_classifier_in_domain
        pp_t_closed_den_in_domain[OF M_typed]] .
  show "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  fix w
  have M_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w (pp_t_closed_den M)"
    using M_typed M_logical
    by (rule pp_t_closed_logical_stockI)
  show "pp_t_holds
        (pp_t_old_unary_stock_classifier \<acute> pp_t_closed_den M) w
      \<longleftrightarrow>
      pp_t_holds (pp_zf_truth True) w"
    unfolding pp_t_old_unary_stock_classifier_def
    using pp_t_classifier_holds[
      OF pp_t_closed_den_in_domain[OF M_typed],
      of "pp_t_closed_logical_stock
        pp_t_one_context_unary_type" w]
      M_stock
    by simp
qed

definition pp_t_fixed_argument_context_expr ::
    "oterm \<Rightarrow> oterm \<Rightarrow> pp_t_one_step_expr"
where
  "pp_t_fixed_argument_context_expr H M =
    PPOneStepApply (PPOneStepLogical H)
      (PPOneStepApply PPOneStepClassifier
        (PPOneStepLogical M))"

lemma pp_t_fixed_argument_context_one_classifier:
  "pp_t_classifier_occurrences
      (pp_t_fixed_argument_context_expr H M) = 1"
  by (simp add: pp_t_fixed_argument_context_expr_def)

theorem pp_t_fixed_argument_context_eliminates_classifier:
  assumes M_typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and H_typed:
      "[] \<turnstile> H : Prop \<rightarrow>\<^sub>o \<sigma>"
    and H_logical: "pp_logical_vocabulary H"
  shows "pp_t_one_step_expr_type
        (pp_t_fixed_argument_context_expr H M) = Some \<sigma>
    \<and>
    pp_t_one_step_expr_den
        (pp_t_fixed_argument_context_expr H M)
      = pp_t_closed_den (App H ObjTrue)"
proof -
  have M_inferred:
      "infer_type [] M = Some pp_t_one_context_unary_type"
    using infer_type_complete[OF M_typed] .
  have H_inferred:
      "infer_type [] H = Some (Prop \<rightarrow>\<^sub>o \<sigma>)"
    using infer_type_complete[OF H_typed] .
  have expression_type:
      "pp_t_one_step_expr_type
        (pp_t_fixed_argument_context_expr H M) = Some \<sigma>"
    using M_logical H_logical M_inferred H_inferred
    by (simp add: pp_t_fixed_argument_context_expr_def)
  have den:
      "pp_t_one_step_expr_den
          (pp_t_fixed_argument_context_expr H M)
        = pp_t_closed_den (App H ObjTrue)"
    using pp_t_old_classifier_accepts_closed_logical[
      OF M_typed M_logical]
    by (simp add: pp_t_fixed_argument_context_expr_def
        pp_t_closed_den_def pp_t_eval_ObjTrue)
  show ?thesis
    using expression_type den by blast
qed

subsection \<open>Logical families of arguments\<close>

definition pp_t_family_probe_builder :: "oterm \<Rightarrow> oterm" where
  "pp_t_family_probe_builder B =
    Lam pp_t_one_context_classifier_type
      (Lam Prop
        (App (Var 1)
          (App (shift (shift B)) (Var 0))))"

lemma pp_t_family_probe_builder_typed:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  shows "[] \<turnstile> pp_t_family_probe_builder B :
    pp_t_one_context_classifier_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
proof -
  have B_shift:
      "[pp_t_one_context_classifier_type]
        \<turnstile> shift B :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_typed by (rule weakening_front)
  have B_shift_shift:
      "[Prop, pp_t_one_context_classifier_type]
        \<turnstile> shift (shift B) :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_shift by (rule weakening_front)
  show ?thesis
    unfolding pp_t_family_probe_builder_def
    apply (rule has_type.Lam)
    apply (rule has_type.Lam)
    apply (rule has_type.App)
     apply (rule has_type.Var)
     apply simp
    apply (rule has_type.App)
     apply (rule B_shift_shift)
    apply (rule has_type.Var)
    apply simp
    done
qed

lemma pp_t_family_probe_builder_logical:
  assumes B_logical: "pp_logical_vocabulary B"
  shows "pp_logical_vocabulary (pp_t_family_probe_builder B)"
  using B_logical
  by (simp add: pp_t_family_probe_builder_def
      pp_logical_vocabulary_def shift_def)

definition pp_t_family_probe :: "oterm \<Rightarrow> ZF" where
  "pp_t_family_probe B =
    pp_t_closed_den (pp_t_family_probe_builder B)
      \<acute> pp_t_old_unary_stock_classifier"

lemma pp_t_family_probe_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  shows "Elem (pp_t_family_probe B)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_family_probe_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_family_probe_builder_typed[OF B_typed]]
      pp_t_old_unary_stock_classifier_in_domain] .

lemma pp_t_family_probe_apply:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_family_probe B \<acute> p =
    pp_t_old_unary_stock_classifier
      \<acute> (pp_t_closed_den B \<acute> p)"
  unfolding pp_t_family_probe_def
    pp_t_family_probe_builder_def pp_t_closed_den_def
  using p pp_t_old_unary_stock_classifier_in_domain
    pp_t_closed_den_in_domain[OF B_typed]
  by (simp add: Lambda_app pp_t_eval_shift)

theorem pp_t_family_probe_apply_holds:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_family_probe B \<acute> p) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w
      (pp_t_closed_den B \<acute> p)"
proof -
  have B_den:
      "Elem (pp_t_closed_den B)
        (pp_t_domain
          (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[OF B_typed] .
  have Bp:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_app_closed[OF B_den p] .
  show ?thesis
    unfolding pp_t_family_probe_apply[OF B_typed p]
      pp_t_old_unary_stock_classifier_def
    using pp_t_classifier_holds[
      OF Bp,
      of "pp_t_closed_logical_stock
        pp_t_one_context_unary_type" w]
    by simp
qed

lemma pp_t_unary_function_ext:
  assumes F:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and applications:
      "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow>
        F \<acute> p = G \<acute> p"
  shows "F = G"
proof -
  have F_fun:
      "Elem F (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[OF F] .
  have G_fun:
      "Elem G (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[OF G] .
  obtain A where F_rep: "F = Lambda (pp_t_domain Prop) A"
    using Elem_Fun_Lambda[OF F_fun] by blast
  obtain B where G_rep: "G = Lambda (pp_t_domain Prop) B"
    using Elem_Fun_Lambda[OF G_fun] by blast
  have pointwise:
      "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow> A p = B p"
  proof -
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    have app: "F \<acute> p = G \<acute> p"
      using applications[OF p] .
    show "A p = B p"
      using app
      apply (subst (asm) F_rep)
      apply (subst (asm) G_rep)
      using p by (simp add: Lambda_app)
  qed
  show ?thesis
    apply (subst F_rep)
    apply (subst G_rep)
    using pointwise by (simp add: Lambda_ext)
qed

lemma pp_t_closed_eval_independent:
  assumes M_typed: "[] \<turnstile> M : \<sigma>"
  shows "pp_t_eval pp_t_default_constants \<rho> M =
    pp_t_eval pp_t_default_constants \<eta> M"
proof -
  have left:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF M_typed pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have right:
      "Elem (pp_t_eval pp_t_default_constants \<eta> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF M_typed pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have related:
      "pp_t_eqv \<sigma> []
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants \<eta> M)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF M_typed pp_t_empty_env_eqv] .
  show ?thesis
    using pp_t_root_eqv_iff_eq[OF left right] related by blast
qed

theorem pp_t_family_probe_elimination_criterion:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_typed: "[] \<turnstile> S : pp_t_one_context_unary_type"
    and criterion:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den B \<acute> p)
          \<longleftrightarrow>
         pp_t_holds (pp_t_closed_den S \<acute> p) w)"
  shows "pp_t_family_probe B = pp_t_closed_den S"
proof (rule pp_t_unary_function_ext)
  show "Elem (pp_t_family_probe B)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_in_domain[OF B_typed] .
  show "Elem (pp_t_closed_den S)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_closed_den_in_domain[OF S_typed] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe B \<acute> p =
      pp_t_closed_den S \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_family_probe B \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_in_domain[OF B_typed] p] .
    show "Elem (pp_t_closed_den S \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_closed_den_in_domain[OF S_typed] p] .
    fix w
    show "pp_t_holds (pp_t_family_probe B \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds (pp_t_closed_den S \<acute> p) w"
      using pp_t_family_probe_apply_holds[OF B_typed p, of w]
        criterion[OF p, of w]
      by blast
  qed
qed

subsection \<open>The constant-operator probe\<close>

definition pp_t_one_context_constant_operator :: "ZF \<Rightarrow> ZF" where
  "pp_t_one_context_constant_operator p =
    pp_t_closed_den pp_constant_builder \<acute> p"

lemma pp_t_one_context_constant_builder_typed:
  "[] \<turnstile> pp_constant_builder :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  using typed_pp_constant_builder[of "[]"]
  unfolding pp_unary_ty_def .

lemma pp_t_one_context_constant_builder_logical:
  "pp_logical_vocabulary pp_constant_builder"
  by (simp add: pp_logical_vocabulary_def pp_constant_builder_def)

lemma pp_t_one_context_constant_operator_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_one_context_constant_operator p)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_one_context_constant_operator_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_one_context_constant_builder_typed] p] .

lemma pp_t_one_context_constant_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_one_context_constant_operator p \<acute> q = p"
  unfolding pp_t_one_context_constant_operator_def
    pp_t_closed_den_def pp_constant_builder_def
  using p q by (simp add: Lambda_app)

lemma pp_t_one_context_truth_in_closed_stock:
  "pp_t_closed_logical_stock Prop w (pp_zf_truth True)"
proof -
  have den: "pp_t_closed_den ObjTrue = pp_zf_truth True"
    by (simp add: pp_t_closed_den_def pp_t_eval_ObjTrue)
  show ?thesis
    unfolding den[symmetric]
    using typed_ObjTrue
    by (rule pp_t_closed_logical_stockI)
      (simp add: pp_logical_vocabulary_def ObjTrue_def)
qed

lemma pp_t_one_context_false_in_closed_stock:
  "pp_t_closed_logical_stock Prop w (pp_zf_truth False)"
proof -
  have false_typed: "[] \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  have false_logical: "pp_logical_vocabulary ObjFalse"
    by (simp add: pp_logical_vocabulary_def ObjFalse_def ObjTrue_def)
  have den: "pp_t_closed_den ObjFalse = pp_zf_truth False"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_closed_den ObjFalse) (pp_t_domain Prop)"
      using pp_t_closed_den_in_domain[OF false_typed] .
    show "Elem (pp_zf_truth False) (pp_t_domain Prop)"
      by (rule pp_t_truth_in_domain)
    fix v
    show "pp_t_holds (pp_t_closed_den ObjFalse) v
        \<longleftrightarrow> pp_t_holds (pp_zf_truth False) v"
      by (simp add: pp_t_closed_den_def ObjFalse_def
          pp_t_eval_ObjTrue)
  qed
  show ?thesis
    unfolding den[symmetric]
    using false_typed false_logical
    by (rule pp_t_closed_logical_stockI)
qed

theorem pp_t_constant_operator_in_closed_stock_iff_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_one_context_constant_operator p)
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof
  assume constant_stock:
      "pp_t_closed_logical_stock
        pp_t_one_context_unary_type w
        (pp_t_one_context_constant_operator p)"
  then obtain M where
      M_typed: "[] \<turnstile> M : pp_t_one_context_unary_type"
    and M_logical: "pp_logical_vocabulary M"
    and constant_M:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_one_context_constant_operator p)
        (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have truth: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have truth_refl:
      "pp_t_eqv Prop w (pp_zf_truth True) (pp_zf_truth True)"
    using pp_t_eqv_reflexive[OF truth] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_one_context_constant_operator p \<acute>
          pp_zf_truth True)
        (pp_t_closed_den M \<acute> pp_zf_truth True)"
    using pp_t_app_respects[
      OF constant_M truth truth truth_refl] .
  let ?A = "App M ObjTrue"
  have A_typed: "[] \<turnstile> ?A : Prop"
    using M_typed typed_ObjTrue by (rule has_type.App)
  have A_logical: "pp_logical_vocabulary ?A"
    using M_logical
    by (simp add: pp_logical_vocabulary_def ObjTrue_def)
  have A_den:
      "pp_t_closed_den ?A =
        pp_t_closed_den M \<acute> pp_zf_truth True"
    by (simp add: pp_t_closed_den_def pp_t_eval_ObjTrue)
  have pA:
      "pp_t_eqv Prop w p (pp_t_closed_den ?A)"
    using applications
      pp_t_one_context_constant_operator_apply[OF p truth]
    unfolding A_den by simp
  have A_root:
      "pp_t_eqv Prop []
        (pp_t_closed_den ?A)
        (pp_zf_truth (pp_t_holds (pp_t_closed_den ?A) []))"
    using pp_t_closed_logical_prop_den_root_truth[
      OF A_typed A_logical] .
  have A_world:
      "pp_t_eqv Prop w
        (pp_t_closed_den ?A)
        (pp_zf_truth (pp_t_holds (pp_t_closed_den ?A) []))"
    using pp_t_eqv_persistent[OF A_root, of w] by simp
  have p_truth:
      "pp_t_eqv Prop w p
        (pp_zf_truth (pp_t_holds (pp_t_closed_den ?A) []))"
    using pp_t_eqv_transitive[
      OF p pp_t_closed_den_in_domain[OF A_typed]
        pp_t_truth_in_domain pA A_world] .
  show "pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
    using p_truth by (cases "pp_t_holds (pp_t_closed_den ?A) []")
      simp_all
next
  assume settled:
      "pp_t_eqv Prop w p (pp_zf_truth True)
        \<or> pp_t_eqv Prop w p (pp_zf_truth False)"
  have p_stock: "pp_t_closed_logical_stock Prop w p"
    using settled
  proof (elim disjE)
    assume p_true:
        "pp_t_eqv Prop w p (pp_zf_truth True)"
    show ?thesis
      unfolding pp_t_closed_logical_stock_def
    proof (intro conjI)
      show "Elem p (pp_t_domain Prop)"
        using p .
      show "\<exists>M.
          [] \<turnstile> M : Prop
          \<and> pp_logical_vocabulary M
          \<and> pp_t_eqv Prop w p (pp_t_closed_den M)"
      proof (rule exI[where x=ObjTrue], intro conjI)
        show "[] \<turnstile> ObjTrue : Prop"
          by (rule typed_ObjTrue)
        show "pp_logical_vocabulary ObjTrue"
          by (simp add: pp_logical_vocabulary_def ObjTrue_def)
        show "pp_t_eqv Prop w p (pp_t_closed_den ObjTrue)"
          using p_true
          by (simp add: pp_t_closed_den_def pp_t_eval_ObjTrue)
      qed
    qed
  next
    assume p_false:
        "pp_t_eqv Prop w p (pp_zf_truth False)"
    show ?thesis
      unfolding pp_t_closed_logical_stock_def
    proof (intro conjI)
      show "Elem p (pp_t_domain Prop)"
        using p .
      show "\<exists>M.
          [] \<turnstile> M : Prop
          \<and> pp_logical_vocabulary M
          \<and> pp_t_eqv Prop w p (pp_t_closed_den M)"
      proof (rule exI[where x=ObjFalse], intro conjI)
        show "[] \<turnstile> ObjFalse : Prop"
          by (rule typed_ObjFalse)
        show "pp_logical_vocabulary ObjFalse"
          by (simp add: pp_logical_vocabulary_def
              ObjFalse_def ObjTrue_def)
        show "pp_t_eqv Prop w p (pp_t_closed_den ObjFalse)"
          using p_false
          by (simp add: pp_t_closed_den_def ObjFalse_def
              pp_t_eval_ObjTrue)
      qed
    qed
  qed
  have builder_stock:
      "pp_t_closed_logical_stock
        (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type) w
        (pp_t_closed_den pp_constant_builder)"
    using pp_t_one_context_constant_builder_typed
      pp_t_one_context_constant_builder_logical
    by (rule pp_t_closed_logical_stockI)
  show "pp_t_closed_logical_stock
      pp_t_one_context_unary_type w
      (pp_t_one_context_constant_operator p)"
    unfolding pp_t_one_context_constant_operator_def
    using pp_t_closed_logical_stock_application_closed[
      OF builder_stock p_stock] .
qed

subsection \<open>Eliminating the constant-operator probe\<close>

definition pp_t_constant_probe_builder :: oterm where
  "pp_t_constant_probe_builder =
    Lam pp_t_one_context_classifier_type
      (Lam Prop
        (App (Var 1)
          (App pp_constant_builder (Var 0))))"

lemma pp_t_constant_probe_builder_typed:
  "[] \<turnstile> pp_t_constant_probe_builder :
    pp_t_one_context_classifier_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
proof -
  have builder:
      "[Prop, pp_t_one_context_classifier_type]
        \<turnstile> pp_constant_builder :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using typed_pp_constant_builder[
      of "[Prop, pp_t_one_context_classifier_type]"]
    unfolding pp_unary_ty_def .
  show ?thesis
    unfolding pp_t_constant_probe_builder_def
    apply (rule has_type.Lam)
    apply (rule has_type.Lam)
    apply (rule has_type.App)
     apply (rule has_type.Var)
     apply simp
    apply (rule has_type.App)
     apply (rule builder)
    apply (rule has_type.Var)
    apply simp
    done
qed

lemma pp_t_constant_probe_builder_logical:
  "pp_logical_vocabulary pp_t_constant_probe_builder"
  by (simp add: pp_logical_vocabulary_def
      pp_t_constant_probe_builder_def pp_constant_builder_def)

definition pp_t_constant_probe :: ZF where
  "pp_t_constant_probe =
    pp_t_closed_den pp_t_constant_probe_builder
      \<acute> pp_t_old_unary_stock_classifier"

definition pp_t_constant_probe_expr :: pp_t_one_step_expr where
  "pp_t_constant_probe_expr =
    PPOneStepApply
      (PPOneStepLogical pp_t_constant_probe_builder)
      PPOneStepClassifier"

lemma pp_t_constant_probe_expr_one_classifier:
  "pp_t_classifier_occurrences pp_t_constant_probe_expr = 1"
  by (simp add: pp_t_constant_probe_expr_def)

lemma pp_t_constant_probe_expr_type:
  "pp_t_one_step_expr_type pp_t_constant_probe_expr =
    Some pp_t_one_context_unary_type"
  using infer_type_complete[
      OF pp_t_constant_probe_builder_typed]
    pp_t_constant_probe_builder_logical
  by (simp add: pp_t_constant_probe_expr_def)

lemma pp_t_constant_probe_expr_den:
  "pp_t_one_step_expr_den pp_t_constant_probe_expr =
    pp_t_constant_probe"
  by (simp add: pp_t_constant_probe_expr_def
      pp_t_constant_probe_def)

lemma pp_t_constant_probe_in_domain:
  "Elem pp_t_constant_probe
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_constant_probe_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_constant_probe_builder_typed]
      pp_t_old_unary_stock_classifier_in_domain] .

lemma pp_t_constant_probe_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_constant_probe \<acute> p) w
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof -
  have constant_domain:
      "Elem (pp_t_one_context_constant_operator p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_one_context_constant_operator_in_domain[OF p] .
  have beta:
      "pp_t_constant_probe \<acute> p =
        pp_t_old_unary_stock_classifier
          \<acute> pp_t_one_context_constant_operator p"
    unfolding pp_t_constant_probe_def
      pp_t_closed_den_def pp_t_constant_probe_builder_def
      pp_t_one_context_constant_operator_def
      pp_constant_builder_def
    using p pp_t_old_unary_stock_classifier_in_domain
    by (simp add: Lambda_app)
  show ?thesis
    unfolding beta pp_t_old_unary_stock_classifier_def
    using pp_t_classifier_holds[
      OF constant_domain,
      of "pp_t_closed_logical_stock
        pp_t_one_context_unary_type" w]
      pp_t_constant_operator_in_closed_stock_iff_settled[OF p]
    by simp
qed

definition pp_t_settled_now_operator :: oterm where
  "pp_t_settled_now_operator =
    Lam Prop
      (Disj
        (\<box>\<^sub>o (Var 0))
        (\<box>\<^sub>o (Neg (Var 0))))"

lemma pp_t_settled_now_operator_typed:
  "[] \<turnstile> pp_t_settled_now_operator :
    pp_t_one_context_unary_type"
  unfolding pp_t_settled_now_operator_def
  by (intro has_type.Lam has_type.Disj typed_ObjBox
      has_type.Neg has_type.Var)
    simp_all

lemma pp_t_settled_now_operator_logical:
  "pp_logical_vocabulary pp_t_settled_now_operator"
  by (simp add: pp_logical_vocabulary_def
      pp_t_settled_now_operator_def ObjBox_def ObjTrue_def)

lemma pp_t_settled_now_apply_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_settled_now_operator) \<acute> p) w
    \<longleftrightarrow>
    (pp_t_eqv Prop w p (pp_zf_truth True)
      \<or> pp_t_eqv Prop w p (pp_zf_truth False))"
proof -
  have beta:
      "(pp_t_closed_den pp_t_settled_now_operator) \<acute> p =
        pp_t_eval pp_t_default_constants
          (extend_env p pp_t_closed_env)
          (Disj
            (\<box>\<^sub>o (Var 0))
            (\<box>\<^sub>o (Neg (Var 0))))"
    unfolding pp_t_closed_den_def pp_t_settled_now_operator_def
    using p by (simp add: Lambda_app)
  show ?thesis
    unfolding beta
    using pp_t_eval_ObjBox_holds[
        of pp_t_default_constants
          "extend_env p pp_t_closed_env" "Var 0" w]
      pp_t_box_neg_holds_iff_false[
        of pp_t_default_constants
          "extend_env p pp_t_closed_env" "Var 0" w]
    by simp
qed

lemma pp_t_constant_probe_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_constant_probe \<acute> p =
    pp_t_closed_den pp_t_settled_now_operator \<acute> p"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_constant_probe \<acute> p) (pp_t_domain Prop)"
    using pp_t_app_closed[OF pp_t_constant_probe_in_domain p] .
  show "Elem
      (pp_t_closed_den pp_t_settled_now_operator \<acute> p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[
        OF pp_t_settled_now_operator_typed] p] .
  fix w
  show "pp_t_holds (pp_t_constant_probe \<acute> p) w
      \<longleftrightarrow>
      pp_t_holds
        (pp_t_closed_den pp_t_settled_now_operator \<acute> p) w"
    using pp_t_constant_probe_apply_holds[OF p, of w]
      pp_t_settled_now_apply_holds[OF p, of w]
    by blast
qed

theorem pp_t_constant_probe_eliminates_classifier:
  "pp_t_constant_probe =
    pp_t_closed_den pp_t_settled_now_operator"
proof -
  have probe_fun:
      "Elem pp_t_constant_probe
        (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[
      OF pp_t_constant_probe_in_domain] .
  have settled_fun:
      "Elem (pp_t_closed_den pp_t_settled_now_operator)
        (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[
      OF pp_t_closed_den_in_domain[
        OF pp_t_settled_now_operator_typed]] .
  obtain F where probe_rep:
      "pp_t_constant_probe = Lambda (pp_t_domain Prop) F"
    using Elem_Fun_Lambda[OF probe_fun] by blast
  obtain G where settled_rep:
      "pp_t_closed_den pp_t_settled_now_operator =
        Lambda (pp_t_domain Prop) G"
    using Elem_Fun_Lambda[OF settled_fun] by blast
  have pointwise:
      "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow> F p = G p"
  proof -
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    have applications:
        "pp_t_constant_probe \<acute> p =
          pp_t_closed_den pp_t_settled_now_operator \<acute> p"
      using pp_t_constant_probe_apply[OF p] .
    show "F p = G p"
      using applications
      apply (subst (asm) probe_rep)
      apply (subst (asm) settled_rep)
      using p by (simp add: Lambda_app)
  qed
  show ?thesis
    apply (subst probe_rep)
    apply (subst settled_rep)
    using pointwise by (simp add: Lambda_ext)
qed

corollary pp_t_constant_probe_in_closed_logical_stock:
  "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w pp_t_constant_probe"
  unfolding pp_t_constant_probe_eliminates_classifier
  using pp_t_settled_now_operator_typed
    pp_t_settled_now_operator_logical
  by (rule pp_t_closed_logical_stockI)

subsection \<open>Closed logical postprocessing\<close>

theorem pp_t_constant_probe_postprocessing_eliminates_classifier:
  assumes H_typed:
      "[] \<turnstile> H :
        pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and H_logical: "pp_logical_vocabulary H"
  shows "pp_t_closed_den H \<acute> pp_t_constant_probe =
    pp_t_closed_den (App H pp_t_settled_now_operator)"
proof -
  have den:
      "pp_t_closed_den (App H pp_t_settled_now_operator) =
        pp_t_closed_den H
          \<acute> pp_t_closed_den pp_t_settled_now_operator"
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    using den
    by (simp add: pp_t_constant_probe_eliminates_classifier)
qed

corollary pp_t_constant_probe_postprocessing_in_closed_stock:
  assumes H_typed:
      "[] \<turnstile> H :
        pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and H_logical: "pp_logical_vocabulary H"
  shows "pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_closed_den H \<acute> pp_t_constant_probe)"
proof -
  have app_typed:
      "[] \<turnstile> App H pp_t_settled_now_operator :
        pp_t_one_context_unary_type"
    using H_typed pp_t_settled_now_operator_typed
    by (rule has_type.App)
  have app_logical:
      "pp_logical_vocabulary (App H pp_t_settled_now_operator)"
    using H_logical pp_t_settled_now_operator_logical
    by (simp add: pp_logical_vocabulary_def)
  show ?thesis
    unfolding pp_t_constant_probe_postprocessing_eliminates_classifier[
      OF H_typed H_logical]
    using app_typed app_logical
    by (rule pp_t_closed_logical_stockI)
qed

definition pp_t_constant_probe_postprocessing_expr ::
    "oterm \<Rightarrow> pp_t_one_step_expr"
where
  "pp_t_constant_probe_postprocessing_expr H =
    PPOneStepApply (PPOneStepLogical H)
      pp_t_constant_probe_expr"

lemma pp_t_constant_probe_postprocessing_one_classifier:
  "pp_t_classifier_occurrences
      (pp_t_constant_probe_postprocessing_expr H) = 1"
  by (simp add: pp_t_constant_probe_postprocessing_expr_def
      pp_t_constant_probe_expr_one_classifier)

theorem pp_t_constant_probe_postprocessing_expr_eliminates:
  assumes H_typed:
      "[] \<turnstile> H :
        pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and H_logical: "pp_logical_vocabulary H"
  shows "pp_t_one_step_expr_type
        (pp_t_constant_probe_postprocessing_expr H) =
          Some pp_t_one_context_unary_type
    \<and>
    pp_t_one_step_expr_den
        (pp_t_constant_probe_postprocessing_expr H)
      = pp_t_closed_den (App H pp_t_settled_now_operator)"
proof -
  have H_inferred:
      "infer_type [] H =
        Some (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type)"
    using infer_type_complete[OF H_typed] .
  have expression_type:
      "pp_t_one_step_expr_type
        (pp_t_constant_probe_postprocessing_expr H) =
          Some pp_t_one_context_unary_type"
    using H_logical H_inferred pp_t_constant_probe_expr_type
    by (simp add: pp_t_constant_probe_postprocessing_expr_def)
  have den:
      "pp_t_one_step_expr_den
          (pp_t_constant_probe_postprocessing_expr H)
        = pp_t_closed_den (App H pp_t_settled_now_operator)"
    using pp_t_constant_probe_postprocessing_eliminates_classifier[
      OF H_typed H_logical]
    by (simp add: pp_t_constant_probe_postprocessing_expr_def
        pp_t_constant_probe_expr_def pp_t_constant_probe_def)
  show ?thesis
    using expression_type den by blast
qed

subsection \<open>The first unresolved one-occurrence context\<close>

definition pp_t_singleton_family_builder :: oterm where
  "pp_t_singleton_family_builder =
    Lam Prop
      (Lam Prop
        (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1))))"

lemma pp_t_singleton_family_builder_typed:
  "[] \<turnstile> pp_t_singleton_family_builder :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  unfolding pp_t_singleton_family_builder_def
  apply (rule has_type.Lam)
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

lemma pp_t_singleton_family_builder_logical:
  "pp_logical_vocabulary pp_t_singleton_family_builder"
  by (simp add: pp_t_singleton_family_builder_def
      pp_logical_vocabulary_def)

definition pp_t_singleton_test_expr :: pp_t_one_step_expr where
  "pp_t_singleton_test_expr =
    PPOneStepApply
      (PPOneStepLogical pp_t_one_step_singleton_test_builder)
      PPOneStepClassifier"

lemma pp_t_singleton_test_expr_one_classifier:
  "pp_t_classifier_occurrences pp_t_singleton_test_expr = 1"
  by (simp add: pp_t_singleton_test_expr_def)

lemma pp_t_singleton_test_expr_type:
  "pp_t_one_step_expr_type pp_t_singleton_test_expr =
    Some pp_t_one_context_unary_type"
  using infer_type_complete[
      OF pp_t_one_step_singleton_test_builder_typed]
    pp_t_one_step_singleton_test_builder_logical
  by (simp add: pp_t_singleton_test_expr_def)

lemma pp_t_singleton_test_expr_den:
  "pp_t_one_step_expr_den pp_t_singleton_test_expr =
    pp_t_one_step_singleton_test"
  by (simp add: pp_t_singleton_test_expr_def
      pp_t_one_step_singleton_test_def)

lemma pp_t_singleton_test_in_domain:
  "Elem pp_t_one_step_singleton_test
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_one_step_expr_den_typed[
    OF pp_t_singleton_test_expr_type]
  unfolding pp_t_singleton_test_expr_den .

lemma pp_t_singleton_test_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_one_step_singleton_test \<acute> p =
    pp_t_old_unary_stock_classifier \<acute>
      (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)"
proof -
  have family_independent:
      "pp_t_eval pp_t_default_constants
          (extend_env pp_t_old_unary_stock_classifier
            pp_t_closed_env)
          pp_t_singleton_family_builder
        = pp_t_closed_den pp_t_singleton_family_builder"
    unfolding pp_t_closed_den_def
    using pp_t_closed_eval_independent[
      OF pp_t_singleton_family_builder_typed] .
  have beta:
      "pp_t_one_step_singleton_test \<acute> p =
        pp_t_old_unary_stock_classifier \<acute>
          (pp_t_eval pp_t_default_constants
              (extend_env pp_t_old_unary_stock_classifier
                pp_t_closed_env)
              pp_t_singleton_family_builder
            \<acute> p)"
    unfolding pp_t_one_step_singleton_test_def
      pp_t_one_step_singleton_test_builder_def
      pp_t_singleton_family_builder_def pp_t_closed_den_def
    using p pp_t_old_unary_stock_classifier_in_domain
    by (simp add: Lambda_app)
  show ?thesis
    using beta family_independent by simp
qed

theorem pp_t_singleton_test_is_family_probe:
  "pp_t_one_step_singleton_test =
    pp_t_family_probe pp_t_singleton_family_builder"
proof (rule pp_t_unary_function_ext)
  show "Elem pp_t_one_step_singleton_test
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_test_in_domain)
  show "Elem (pp_t_family_probe pp_t_singleton_family_builder)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_in_domain[
      OF pp_t_singleton_family_builder_typed] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_one_step_singleton_test \<acute> p =
      pp_t_family_probe pp_t_singleton_family_builder \<acute> p"
    using pp_t_singleton_test_apply[OF p]
      pp_t_family_probe_apply[
        OF pp_t_singleton_family_builder_typed p]
    by simp
qed

corollary pp_t_singleton_test_apply_holds_iff_family_in_stock:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_one_step_singleton_test \<acute> p) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w
      (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)"
  unfolding pp_t_singleton_test_is_family_probe
  using pp_t_family_probe_apply_holds[
    OF pp_t_singleton_family_builder_typed p, of w] .

theorem pp_t_singleton_test_eliminable_iff_family_stock_definable:
  "(\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> pp_t_one_step_singleton_test = pp_t_closed_den S)
    \<longleftrightarrow>
   (\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> (\<forall>p w.
        Elem p (pp_t_domain Prop) \<longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)
          \<longleftrightarrow>
         pp_t_holds (pp_t_closed_den S \<acute> p) w)))"
proof
  assume eliminable:
      "\<exists>S.
        [] \<turnstile> S : pp_t_one_context_unary_type
        \<and> pp_logical_vocabulary S
        \<and> pp_t_one_step_singleton_test = pp_t_closed_den S"
  then obtain S where
      S_typed: "[] \<turnstile> S : pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and test_S:
      "pp_t_one_step_singleton_test = pp_t_closed_den S"
    by blast
  show "\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> (\<forall>p w.
        Elem p (pp_t_domain Prop) \<longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)
          \<longleftrightarrow>
         pp_t_holds (pp_t_closed_den S \<acute> p) w))"
  proof (rule exI[where x=S], intro conjI allI impI)
    show "[] \<turnstile> S : pp_t_one_context_unary_type"
      using S_typed .
    show "pp_logical_vocabulary S"
      using S_logical .
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)
        \<longleftrightarrow>
        pp_t_holds (pp_t_closed_den S \<acute> p) w"
      using pp_t_singleton_test_apply_holds_iff_family_in_stock[
        OF p, of w]
      unfolding test_S
      by blast
  qed
next
  assume definable:
      "\<exists>S.
        [] \<turnstile> S : pp_t_one_context_unary_type
        \<and> pp_logical_vocabulary S
        \<and> (\<forall>p w.
          Elem p (pp_t_domain Prop) \<longrightarrow>
          (pp_t_closed_logical_stock
              pp_t_one_context_unary_type w
              (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)
            \<longleftrightarrow>
           pp_t_holds (pp_t_closed_den S \<acute> p) w))"
  then obtain S where
      S_typed: "[] \<turnstile> S : pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and criterion:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            (pp_t_closed_den pp_t_singleton_family_builder \<acute> p)
          \<longleftrightarrow>
         pp_t_holds (pp_t_closed_den S \<acute> p) w)"
    by blast
  have family_S:
      "pp_t_family_probe pp_t_singleton_family_builder =
        pp_t_closed_den S"
    using pp_t_family_probe_elimination_criterion[
      OF pp_t_singleton_family_builder_typed S_typed criterion] .
  have test_S:
      "pp_t_one_step_singleton_test = pp_t_closed_den S"
  proof -
    have "pp_t_one_step_singleton_test =
        pp_t_family_probe pp_t_singleton_family_builder"
      by (rule pp_t_singleton_test_is_family_probe)
    also have "... = pp_t_closed_den S"
      by (rule family_S)
    finally show ?thesis .
  qed
  show "\<exists>S.
      [] \<turnstile> S : pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> pp_t_one_step_singleton_test = pp_t_closed_den S"
    apply (rule exI[where x=S])
    using S_typed S_logical test_S
    by blast
qed

text \<open>
  This places the singleton test inside the very first syntactic stratum.  It
  is not covered by the constant-operator theorem: its argument to the
  classifier is the family
  \<open>p \<mapsto> (\<lambda>q. \<box>(q \<longleftrightarrow> p))\<close>, rather than a constant
  operator.  Eliminating this expression, or proving that it has no closed
  logical representative, is therefore the next strict classification step.
\<close>

end
