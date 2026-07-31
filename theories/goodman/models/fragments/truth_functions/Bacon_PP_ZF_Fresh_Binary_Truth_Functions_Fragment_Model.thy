theory Bacon_PP_ZF_Fresh_Binary_Truth_Functions_Fragment_Model
  imports
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Fresh_Conjunction_Fragment_Model"
begin

section \<open>All curried binary truth-functions\<close>

definition pp_truth_value :: "bool \<Rightarrow> oterm" where
  "pp_truth_value b = (if b then ObjTrue else ObjFalse)"

definition pp_truth_choice ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm"
where
  "pp_truth_choice P A B =
    Disj (Conj P A) (Conj (Neg P) B)"

definition pp_truth_function_builder ::
    "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> oterm"
where
  "pp_truth_function_builder F =
    Lam Prop (Lam Prop
      (pp_truth_choice (Var 1)
        (pp_truth_choice (Var 0)
          (pp_truth_value (F True True))
          (pp_truth_value (F True False)))
        (pp_truth_choice (Var 0)
          (pp_truth_value (F False True))
          (pp_truth_value (F False False)))))"

lemma typed_pp_truth_value:
  "\<Gamma> \<turnstile> pp_truth_value b : Prop"
  by (cases b)
    (simp_all add: pp_truth_value_def typed_ObjTrue typed_ObjFalse)

lemma typed_pp_truth_choice:
  assumes P: "\<Gamma> \<turnstile> P : Prop"
    and A: "\<Gamma> \<turnstile> A : Prop"
    and B: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile> pp_truth_choice P A B : Prop"
  unfolding pp_truth_choice_def
  using P A B by auto

lemma typed_pp_truth_function_builder:
  "\<Gamma> \<turnstile> pp_truth_function_builder F :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
proof -
  have p: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by simp
  have q: "Prop # Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by simp
  have tt:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_value (F True True) : Prop"
    by (rule typed_pp_truth_value)
  have tf:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_value (F True False) : Prop"
    by (rule typed_pp_truth_value)
  have ft:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_value (F False True) : Prop"
    by (rule typed_pp_truth_value)
  have ff:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_value (F False False) : Prop"
    by (rule typed_pp_truth_value)
  have true_row:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_choice (Var 0)
          (pp_truth_value (F True True))
          (pp_truth_value (F True False)) : Prop"
    by (rule typed_pp_truth_choice[OF q tt tf])
  have false_row:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_choice (Var 0)
          (pp_truth_value (F False True))
          (pp_truth_value (F False False)) : Prop"
    by (rule typed_pp_truth_choice[OF q ft ff])
  have body:
      "Prop # Prop # \<Gamma> \<turnstile>
        pp_truth_choice (Var 1)
          (pp_truth_choice (Var 0)
            (pp_truth_value (F True True))
            (pp_truth_value (F True False)))
          (pp_truth_choice (Var 0)
            (pp_truth_value (F False True))
            (pp_truth_value (F False False))) : Prop"
    by (rule typed_pp_truth_choice[OF p true_row false_row])
  show ?thesis
    unfolding pp_truth_function_builder_def pp_unary_ty_def
    by (intro has_type.Lam body)
qed

lemma pp_truth_function_builder_closed:
  "consts_of (pp_truth_function_builder F) = {}"
  by (cases "F True True"; cases "F True False";
      cases "F False True"; cases "F False False")
    (simp_all add: pp_truth_function_builder_def
      pp_truth_choice_def pp_truth_value_def
      ObjFalse_def ObjTrue_def)

lemma pp_truth_function_builder_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      (pp_truth_function_builder F)
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_truth_function_builder F :
      Prop \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_truth_function_builder)
  show "consts_of (pp_truth_function_builder F) = {}"
    by (rule pp_truth_function_builder_closed)
  show "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        (pp_truth_function_builder F) =
      pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        (pp_truth_function_builder F)"
    by simp
qed

abbreviation pp_t_binary_truth_builder_type :: otype where
  "pp_t_binary_truth_builder_type \<equiv>
    Prop \<rightarrow>\<^sub>o pp_t_constants_unary_type"

definition pp_t_truth_function_result ::
    "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_truth_function_result F p q =
    pp_t_prop (\<lambda>w. F (pp_t_holds p w) (pp_t_holds q w))"

lemma pp_t_truth_function_result_in_domain:
  "Elem (pp_t_truth_function_result F p q) (pp_t_domain Prop)"
  unfolding pp_t_truth_function_result_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_truth_function_result_respects:
  assumes p: "Elem p (pp_t_domain Prop)"
    and p': "Elem p' (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and q': "Elem q' (pp_t_domain Prop)"
    and pp': "pp_t_eqv Prop w p p'"
    and qq': "pp_t_eqv Prop w q q'"
  shows "pp_t_eqv Prop w
    (pp_t_truth_function_result F p q)
    (pp_t_truth_function_result F p' q')"
  unfolding pp_t_truth_function_result_def
    pp_t_prop_eqv_pp_t_prop_iff
proof (intro allI impI)
  fix v
  assume future: "prefix w v"
  have p_at: "pp_t_holds p v = pp_t_holds p' v"
    using pp_t_prop_eqv_at[OF pp' future] by simp
  have q_at: "pp_t_holds q v = pp_t_holds q' v"
    using pp_t_prop_eqv_at[OF qq' future] by simp
  show "F (pp_t_holds p v) (pp_t_holds q v) =
      F (pp_t_holds p' v) (pp_t_holds q' v)"
    using p_at q_at by simp
qed

definition pp_t_truth_function_unary ::
    "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_truth_function_unary F p =
    Lambda (pp_t_domain Prop) (pp_t_truth_function_result F p)"

lemma pp_t_truth_function_unary_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_truth_function_unary F p)
    (pp_t_domain pp_t_constants_unary_type)"
proof (unfold pp_t_truth_function_unary_def, rule pp_t_lambda_closed)
  show "\<And>q. Elem q (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_t_truth_function_result F p q) (pp_t_domain Prop)"
    by (rule pp_t_truth_function_result_in_domain)
  show "\<And>w q q'.
      Elem q (pp_t_domain Prop) \<Longrightarrow>
      Elem q' (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w q q' \<Longrightarrow>
      pp_t_eqv Prop w
        (pp_t_truth_function_result F p q)
        (pp_t_truth_function_result F p q')"
  proof -
    fix w q q'
    assume q: "Elem q (pp_t_domain Prop)"
      and q': "Elem q' (pp_t_domain Prop)"
      and qq': "pp_t_eqv Prop w q q'"
    show "pp_t_eqv Prop w
        (pp_t_truth_function_result F p q)
        (pp_t_truth_function_result F p q')"
      by (rule pp_t_truth_function_result_respects[
        OF p p q q' pp_t_eqv_reflexive[OF p] qq'])
  qed
qed

lemma pp_t_truth_function_unary_apply:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_truth_function_unary F p \<acute> q =
    pp_t_truth_function_result F p q"
  using q
  by (simp add: pp_t_truth_function_unary_def Lambda_app)

lemma pp_t_truth_function_unary_respects:
  assumes p: "Elem p (pp_t_domain Prop)"
    and p': "Elem p' (pp_t_domain Prop)"
    and pp': "pp_t_eqv Prop w p p'"
  shows "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_truth_function_unary F p)
    (pp_t_truth_function_unary F p')"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_truth_function_unary F p)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_truth_function_unary_in_domain[OF p])
  show "Elem (pp_t_truth_function_unary F p')
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_truth_function_unary_in_domain[OF p'])
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_truth_function_unary F p \<acute> q)
          (pp_t_truth_function_unary F p' \<acute> q))"
  proof (intro allI impI)
    fix v q
    assume future: "prefix w v"
      and q: "Elem q (pp_t_domain Prop)"
    have pp'_v: "pp_t_eqv Prop v p p'"
      by (rule pp_t_eqv_persistent[OF pp' future])
    show "pp_t_eqv Prop v
        (pp_t_truth_function_unary F p \<acute> q)
        (pp_t_truth_function_unary F p' \<acute> q)"
      unfolding
        pp_t_truth_function_unary_apply[OF q]
        pp_t_truth_function_unary_apply[OF q]
      by (rule pp_t_truth_function_result_respects[
        OF p p' q q pp'_v pp_t_eqv_reflexive[OF q]])
  qed
qed

definition pp_t_truth_function_builder ::
    "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ZF"
where
  "pp_t_truth_function_builder F =
    Lambda (pp_t_domain Prop) (pp_t_truth_function_unary F)"

lemma pp_t_truth_function_builder_in_domain:
  "Elem (pp_t_truth_function_builder F)
    (pp_t_domain pp_t_binary_truth_builder_type)"
proof (unfold pp_t_truth_function_builder_def, rule pp_t_lambda_closed)
  show "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_t_truth_function_unary F p)
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_truth_function_unary_in_domain)
  show "\<And>w p p'.
      Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem p' (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w p p' \<Longrightarrow>
      pp_t_eqv pp_t_constants_unary_type w
        (pp_t_truth_function_unary F p)
        (pp_t_truth_function_unary F p')"
    by (rule pp_t_truth_function_unary_respects)
qed

lemma pp_t_truth_function_builder_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_truth_function_builder F \<acute> p =
    pp_t_truth_function_unary F p"
  using p
  by (simp add: pp_t_truth_function_builder_def Lambda_app)

lemma pp_t_eval_truth_value_holds:
  "pp_t_holds (pp_t_eval C \<rho> (pp_truth_value b)) w
    \<longleftrightarrow> b"
  by (cases b)
    (simp_all add: pp_truth_value_def ObjFalse_def
      pp_t_eval_ObjTrue)

lemma pp_t_eval_truth_choice_holds:
  "pp_t_holds
      (pp_t_eval C \<rho> (pp_truth_choice P A B)) w
    \<longleftrightarrow>
    (if pp_t_holds (pp_t_eval C \<rho> P) w
      then pp_t_holds (pp_t_eval C \<rho> A) w
      else pp_t_holds (pp_t_eval C \<rho> B) w)"
  by (simp add: pp_truth_choice_def)

lemma pp_t_eval_truth_function_builder_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval C \<rho> (pp_truth_function_builder F)
        \<acute> p \<acute> q) w
    \<longleftrightarrow>
    F (pp_t_holds p w) (pp_t_holds q w)"
  using p q
  by (simp add: pp_truth_function_builder_def Lambda_app
      pp_t_eval_truth_choice_holds pp_t_eval_truth_value_holds)

lemma pp_t_eval_truth_function_builder_eqv:
  assumes C_typed:
      "\<And>c \<sigma>. Elem (C c \<sigma>) (pp_t_domain \<sigma>)"
    and env: "pp_t_env_typed [] \<rho>"
  shows "pp_t_eqv pp_t_binary_truth_builder_type w
    (pp_t_truth_function_builder F)
    (pp_t_eval C \<rho> (pp_truth_function_builder F))"
proof -
  interpret TypedConstants: pp_t_constants C
    by standard (rule C_typed)
  show ?thesis
  proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_truth_function_builder F)
      (pp_t_domain pp_t_binary_truth_builder_type)"
    by (rule pp_t_truth_function_builder_in_domain)
  show "Elem (pp_t_eval C \<rho> (pp_truth_function_builder F))
      (pp_t_domain pp_t_binary_truth_builder_type)"
    using TypedConstants.pp_t_eval_type[
      OF typed_pp_truth_function_builder env]
    by (simp add: pp_t_dom_def pp_unary_ty_def)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type v
          (pp_t_truth_function_builder F \<acute> p)
          (pp_t_eval C \<rho> (pp_truth_function_builder F) \<acute> p))"
  proof (intro allI impI)
    fix v p
    assume "prefix w v"
      and p: "Elem p (pp_t_domain Prop)"
    show "pp_t_eqv pp_t_constants_unary_type v
        (pp_t_truth_function_builder F \<acute> p)
        (pp_t_eval C \<rho> (pp_truth_function_builder F) \<acute> p)"
    proof (rule pp_t_arrow_eqv_if_pointwise)
      show "Elem (pp_t_truth_function_builder F \<acute> p)
          (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_app_closed[
          OF pp_t_truth_function_builder_in_domain p])
      show "Elem
          (pp_t_eval C \<rho> (pp_truth_function_builder F) \<acute> p)
          (pp_t_domain pp_t_constants_unary_type)"
      proof (rule pp_t_app_closed[OF _ p])
        show "Elem
            (pp_t_eval C \<rho> (pp_truth_function_builder F))
            (pp_t_domain pp_t_binary_truth_builder_type)"
          using TypedConstants.pp_t_eval_type[
            OF typed_pp_truth_function_builder env]
          by (simp add: pp_t_dom_def pp_unary_ty_def)
      qed
      show "\<forall>u. prefix v u \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_eqv Prop u
              (pp_t_truth_function_builder F \<acute> p \<acute> q)
              (pp_t_eval C \<rho>
                (pp_truth_function_builder F) \<acute> p \<acute> q))"
      proof (intro allI impI)
        fix u q
        assume "prefix v u"
          and q: "Elem q (pp_t_domain Prop)"
        show "pp_t_eqv Prop u
            (pp_t_truth_function_builder F \<acute> p \<acute> q)
            (pp_t_eval C \<rho>
              (pp_truth_function_builder F) \<acute> p \<acute> q)"
          unfolding pp_t_truth_function_builder_apply[OF p]
            pp_t_truth_function_unary_apply[OF q]
            pp_t_truth_function_result_def
          using pp_t_eval_truth_function_builder_holds[
            OF p q, of C \<rho> F]
          by simp
      qed
    qed
  qed
qed
qed

definition pp_t_boolean_unary :: "bool \<Rightarrow> bool \<Rightarrow> ZF" where
  "pp_t_boolean_unary t f =
    (if t then
      (if f then pp_t_constant_operator True
       else pp_t_identity_operator)
     else
      (if f then pp_t_negation_operator
       else pp_t_constant_operator False))"

lemma pp_t_boolean_unary_in_domain:
  "Elem (pp_t_boolean_unary t f)
    (pp_t_domain pp_t_constants_unary_type)"
proof -
  consider (tt) "t" "f"
    | (tf) "t" "\<not> f"
    | (ft) "\<not> t" "f"
    | (ff) "\<not> t" "\<not> f"
    by blast
  then show ?thesis
  proof cases
    case tt
    have equality:
        "pp_t_boolean_unary t f = pp_t_constant_operator True"
      using tt by (simp add: pp_t_boolean_unary_def)
    show ?thesis
      unfolding equality
      by (rule pp_t_constant_operator_in_domain)
  next
    case tf
    have equality:
        "pp_t_boolean_unary t f = pp_t_identity_operator"
      using tf by (simp add: pp_t_boolean_unary_def)
    show ?thesis
      unfolding equality
      by (rule pp_t_identity_operator_in_domain)
  next
    case ft
    have equality:
        "pp_t_boolean_unary t f = pp_t_negation_operator"
      using ft by (simp add: pp_t_boolean_unary_def)
    show ?thesis
      unfolding equality
      by (rule pp_t_negation_operator_in_domain)
  next
    case ff
    have equality:
        "pp_t_boolean_unary t f = pp_t_constant_operator False"
      using ff by (simp add: pp_t_boolean_unary_def)
    show ?thesis
      unfolding equality
      by (rule pp_t_constant_operator_in_domain)
  qed
qed

lemma pp_t_boolean_unary_holds:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_boolean_unary t f \<acute> q) w
    \<longleftrightarrow>
    (if pp_t_holds q w then t else f)"
  using q
  by (cases t; cases f)
    (simp_all add: pp_t_boolean_unary_def
      pp_t_constant_operator_apply pp_t_identity_operator_def
      pp_t_negation_operator_apply Lambda_app)

lemma pp_t_boolean_unary_is_pure:
  "pp_t_conjunction_fragment_pure
    pp_t_constants_unary_type w (pp_t_boolean_unary t f)"
proof -
  have lift:
      "\<And>x. pp_t_constants_fragment_pure
          pp_t_constants_unary_type w x
        \<Longrightarrow> pp_t_conjunction_fragment_pure
          pp_t_constants_unary_type w x"
    unfolding pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def
    by blast
  show ?thesis
    unfolding pp_t_boolean_unary_def
    by (auto intro: lift
        pp_t_constants_constant_is_pure
        pp_t_constants_identity_is_pure
        pp_t_constants_negation_is_pure)
qed

lemma pp_t_truth_function_slice:
  assumes p: "Elem p (pp_t_domain Prop)"
    and e: "pp_t_eqv Prop w (pp_zf_truth b) p"
  shows "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_boolean_unary (F b True) (F b False))
    (pp_t_truth_function_unary F p)"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_boolean_unary (F b True) (F b False))
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_boolean_unary_in_domain)
  show "Elem (pp_t_truth_function_unary F p)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_truth_function_unary_in_domain[OF p])
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_boolean_unary (F b True) (F b False) \<acute> q)
          (pp_t_truth_function_unary F p \<acute> q))"
  proof (intro allI impI)
    fix v q
    assume future: "prefix w v"
      and q: "Elem q (pp_t_domain Prop)"
    have p_at:
        "pp_t_holds p v = b"
      using pp_t_prop_eqv_at[OF e future]
      by (cases b) simp_all
    show "pp_t_eqv Prop v
        (pp_t_boolean_unary (F b True) (F b False) \<acute> q)
        (pp_t_truth_function_unary F p \<acute> q)"
    proof (unfold pp_t_eqv.simps, intro allI impI)
      fix u
      assume vu: "prefix v u"
      have wu: "prefix w u"
        using future vu by (rule prefix_order.trans)
      have p_at_u: "pp_t_holds p u = b"
        using pp_t_prop_eqv_at[OF e wu]
        by (cases b) simp_all
      have left:
          "pp_t_holds
              (pp_t_boolean_unary
                (F b True) (F b False) \<acute> q) u =
            (if pp_t_holds q u then F b True else F b False)"
        using pp_t_boolean_unary_holds[
          OF q, of "F b True" "F b False" u]
        by simp
      have right:
          "pp_t_holds
              (pp_t_truth_function_unary F p \<acute> q) u =
            F (pp_t_holds p u) (pp_t_holds q u)"
        unfolding pp_t_truth_function_unary_apply[OF q]
          pp_t_truth_function_result_def
        by simp
      show "pp_t_holds
          (pp_t_boolean_unary
            (F b True) (F b False) \<acute> q) u =
        pp_t_holds (pp_t_truth_function_unary F p \<acute> q) u"
        using left right p_at_u
        by (cases "pp_t_holds q u") simp_all
    qed
  qed
qed

section \<open>The enlarged pure stock\<close>

definition pp_t_binary_truth_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_binary_truth_fragment_pure \<sigma> w x \<longleftrightarrow>
    pp_t_conjunction_fragment_pure \<sigma> w x
    \<or>
    (\<sigma> = pp_t_binary_truth_builder_type
      \<and> (\<exists>F. pp_t_eqv pp_t_binary_truth_builder_type
        w (pp_t_truth_function_builder F) x))"

lemma pp_t_binary_truth_inherits_old_pure:
  assumes old: "pp_t_conjunction_fragment_pure \<sigma> w x"
  shows "pp_t_binary_truth_fragment_pure \<sigma> w x"
  unfolding pp_t_binary_truth_fragment_pure_def
  using old by (rule disjI1)

lemma pp_t_conjunction_inherits_constants_pure:
  assumes old: "pp_t_constants_fragment_pure \<sigma> w x"
  shows "pp_t_conjunction_fragment_pure \<sigma> w x"
  unfolding pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
  using old by blast

lemma pp_t_binary_truth_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_binary_truth_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_conjunction_fragment_pure \<sigma>)"
    by (rule pp_t_conjunction_fragment_pure_admissible)
  have family:
      "\<And>F. pp_t_predicate_admissible
        pp_t_binary_truth_builder_type
        (\<lambda>w x. pp_t_eqv pp_t_binary_truth_builder_type
          w (pp_t_truth_function_builder F) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_truth_function_builder_in_domain] .
  show ?thesis
    using old family
    unfolding pp_t_predicate_admissible_def
      pp_t_binary_truth_fragment_pure_def
    by blast
qed

lemma pp_t_truth_function_is_pure[simp]:
  "pp_t_binary_truth_fragment_pure
    pp_t_binary_truth_builder_type w
    (pp_t_truth_function_builder F)"
  unfolding pp_t_binary_truth_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_truth_function_builder_in_domain]
  by blast

lemma pp_t_binary_truth_pure_Prop_iff:
  "pp_t_binary_truth_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_conjunction_fragment_pure Prop w P"
  unfolding pp_t_binary_truth_fragment_pure_def by simp

lemma pp_t_binary_truth_pure_unary_iff:
  "pp_t_binary_truth_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_conjunction_fragment_pure
      pp_t_constants_unary_type w X"
  unfolding pp_t_binary_truth_fragment_pure_def by simp

lemma pp_t_binary_truth_pure_classifier_iff:
  "pp_t_binary_truth_fragment_pure
      pp_t_constants_classifier_type w X
    \<longleftrightarrow>
    pp_t_conjunction_fragment_pure
      pp_t_constants_classifier_type w X"
  unfolding pp_t_binary_truth_fragment_pure_def by simp

lemma pp_t_binary_truth_old_input:
  assumes pure_f:
      "pp_t_conjunction_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_binary_truth_fragment_pure \<sigma> w x"
  shows "pp_t_conjunction_fragment_pure \<sigma> w x"
proof -
  from pure_x show ?thesis
    unfolding pp_t_binary_truth_fragment_pure_def
  proof
    assume "pp_t_conjunction_fragment_pure \<sigma> w x"
    then show ?thesis .
  next
    assume new:
      "\<sigma> = pp_t_binary_truth_builder_type
        \<and> (\<exists>F. pp_t_eqv pp_t_binary_truth_builder_type
          w (pp_t_truth_function_builder F) x)"
    then have sigma:
        "\<sigma> = pp_t_binary_truth_builder_type"
      by blast
    have False
      using pure_f
      unfolding sigma
        pp_t_conjunction_fragment_pure_def
        pp_t_constant_builder_fragment_pure_def
        pp_t_constants_fragment_pure_def
      by simp
    then show ?thesis by blast
  qed
qed

lemma pp_t_truth_function_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_binary_truth_builder_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_binary_truth_builder_type
        w (pp_t_truth_function_builder F) f"
    and pure_x:
      "pp_t_binary_truth_fragment_pure Prop w x"
  shows "pp_t_binary_truth_fragment_pure
    pp_t_constants_unary_type w (f \<acute> x)"
proof -
  have x_class:
      "pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x"
    using pure_x
    unfolding pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff .
  have x_refl: "pp_t_eqv Prop w x x"
    by (rule pp_t_eqv_reflexive[OF x])
  have application:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_truth_function_builder F \<acute> x) (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative x x x_refl])
  have "\<exists>b. pp_t_eqv Prop w (pp_zf_truth b) x"
  proof -
    from x_class show ?thesis
    proof
      assume xb:
          "pp_t_eqv Prop w (pp_zf_truth True) x"
      show ?thesis
        by (rule exI[of _ True]) (rule xb)
    next
      assume xb:
          "pp_t_eqv Prop w (pp_zf_truth False) x"
      show ?thesis
        by (rule exI[of _ False]) (rule xb)
    qed
  qed
  then obtain b where
      xb: "pp_t_eqv Prop w (pp_zf_truth b) x"
    by blast
  have slice:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_boolean_unary (F b True) (F b False))
        (pp_t_truth_function_builder F \<acute> x)"
    using pp_t_truth_function_slice[OF x xb]
    unfolding pp_t_truth_function_builder_apply[OF x] .
  have result:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_boolean_unary (F b True) (F b False))
        (f \<acute> x)"
  proof -
    have middle:
        "Elem (pp_t_truth_function_builder F \<acute> x)
          (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_truth_function_builder_in_domain x])
    have final:
        "Elem (f \<acute> x)
          (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_app_closed[OF f x])
    show ?thesis
      using pp_t_boolean_unary_in_domain middle final
        slice application
      by (meson pp_t_eqv_transitive)
  qed
  have old_pure:
      "pp_t_conjunction_fragment_pure
        pp_t_constants_unary_type w (f \<acute> x)"
    using pp_t_boolean_unary_is_pure result
    unfolding pp_t_conjunction_pure_unary_iff
      pp_t_constant_builder_pure_unary_iff
      pp_t_constants_fragment_pure_unary_iff
      pp_t_constants_unary_pure_def
      pp_t_idneg_unary_pure_def
      pp_t_boolean_unary_def
    by (cases "F b True"; cases "F b False"; auto)
  show ?thesis
    unfolding pp_t_binary_truth_fragment_pure_def
    using old_pure by blast
qed

lemma pp_t_binary_truth_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_binary_truth_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_binary_truth_fragment_pure \<sigma> w x"
  shows "pp_t_binary_truth_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_conjunction_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    | (family)
        "\<sigma> = Prop" "\<tau> = pp_t_constants_unary_type"
        "\<exists>F. pp_t_eqv pp_t_binary_truth_builder_type
          w (pp_t_truth_function_builder F) f"
    unfolding pp_t_binary_truth_fragment_pure_def
    by auto
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_conjunction_fragment_pure \<sigma> w x"
      by (rule pp_t_binary_truth_old_input[OF old pure_x])
    have old_result:
        "pp_t_conjunction_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_conjunction_fragment_application[
        OF f x old old_x])
    show ?thesis
      unfolding pp_t_binary_truth_fragment_pure_def
      using old_result by blast
  next
    case family
    then obtain F where representative:
        "pp_t_eqv pp_t_binary_truth_builder_type
          w (pp_t_truth_function_builder F) f"
      by blast
    show ?thesis
      using pp_t_truth_function_application[
        OF _ _ representative] f x pure_x family
      by simp
  qed
qed

section \<open>The moving-fundamental interpretation\<close>

interpretation BinaryTruthFragment:
  pp_t_moving_internal_parameters
    pp_t_binary_truth_fragment_pure
  by standard
    (rule pp_t_binary_truth_fragment_pure_admissible)

abbreviation pp_t_binary_truth_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_binary_truth_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_binary_truth_fragment_pure"

lemma pp_t_truth_function_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        (pp_truth_function_builder F))) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have related:
      "pp_t_eqv pp_t_binary_truth_builder_type w
        (pp_t_truth_function_builder F)
        (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
          (pp_truth_function_builder F))"
    by (rule pp_t_eval_truth_function_builder_eqv[
      OF BinaryTruthFragment.MovingTreeConstants.C_typed env])
  have evaluated:
      "Elem
        (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
          (pp_truth_function_builder F))
        (pp_t_domain pp_t_binary_truth_builder_type)"
    using
      BinaryTruthFragment.MovingTreeConstants.pp_t_eval_type[
        OF typed_pp_truth_function_builder env]
    by (simp add: pp_t_dom_def pp_unary_ty_def)
  have same_purity:
      "pp_t_binary_truth_fragment_pure
          pp_t_binary_truth_builder_type w
          (pp_t_truth_function_builder F)
        \<longleftrightarrow>
       pp_t_binary_truth_fragment_pure
          pp_t_binary_truth_builder_type w
          (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
            (pp_truth_function_builder F))"
    using pp_t_binary_truth_fragment_pure_admissible
      pp_t_truth_function_builder_in_domain evaluated related
    unfolding pp_t_predicate_admissible_def
    by blast
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_binary_truth_builder_type w
        (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
          (pp_truth_function_builder F))"
    using same_purity pp_t_truth_function_is_pure by blast
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed_pp_truth_function_builder env, of F w]
      pure
    by (simp add: pp_unary_ty_def)
qed

theorem pp_t_truth_function_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type
      (pp_truth_function_builder F))"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_truth_function_purity_holds by blast

lemma pp_t_binary_truth_conjunction_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        pp_conjunction_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_conjunction_builder :
        pp_t_binary_truth_builder_type"
    using typed_pp_conjunction_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_conjunction_builder"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_is_pure)
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure
    by simp
qed

theorem pp_t_binary_truth_conjunction_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type pp_conjunction_builder)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_conjunction_purity_holds by blast

lemma pp_t_binary_truth_constant_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        pp_constant_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_builder :
        pp_t_binary_truth_builder_type"
    using typed_pp_constant_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_constant_builder"
  proof (rule pp_t_binary_truth_inherits_old_pure)
    show "pp_t_conjunction_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_constant_builder"
      unfolding pp_t_conjunction_fragment_pure_def
      using pp_t_constant_builder_is_pure by (rule disjI1)
  qed
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w] pure
    by simp
qed

theorem pp_t_binary_truth_constant_builder_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type pp_constant_builder)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_constant_builder_purity_holds by blast

lemma pp_t_binary_truth_identity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type prop_id)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_unary_type w pp_t_identity_operator"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_inherits_constants_pure,
       rule pp_t_constants_identity_is_pure)
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed_prop_id env, of w]
      pure
    by simp
qed

theorem pp_t_binary_truth_identity_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type prop_id)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_identity_purity_holds by blast

lemma pp_t_binary_truth_negation_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_negation_operator)) w"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator :
        pp_t_constants_unary_type"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_unary_type w pp_t_negation_operator"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_inherits_constants_pure,
       rule pp_t_constants_negation_is_pure)
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure
    by simp
qed

theorem pp_t_binary_truth_negation_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type pp_negation_operator)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_negation_purity_holds by blast

lemma pp_t_binary_truth_constant_truth_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        (pp_constant_operator ObjTrue))) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_operator ObjTrue :
        pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjTrue]
    unfolding pp_unary_ty_def .
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_unary_type w
        (pp_t_constant_operator True)"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_inherits_constants_pure,
       rule pp_t_constants_constant_is_pure)
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure
    by simp
qed

theorem pp_t_binary_truth_constant_truth_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjTrue))"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using
    pp_t_binary_truth_constant_truth_purity_holds
  by blast

lemma pp_t_binary_truth_constant_falsity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        (pp_constant_operator ObjFalse))) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_operator ObjFalse :
        pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjFalse]
    unfolding pp_unary_ty_def .
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_unary_type w
        (pp_t_constant_operator False)"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_inherits_constants_pure,
       rule pp_t_constants_constant_is_pure)
  show ?thesis
    using
      BinaryTruthFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure
    by simp
qed

theorem pp_t_binary_truth_constant_falsity_purity_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjFalse))"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using
    pp_t_binary_truth_constant_falsity_purity_holds
  by blast

lemma pp_t_binary_truth_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_binary_truth_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_constants_stock_classifier"
    unfolding pp_t_constants_stock_classifier_def
      pp_t_classifier_def
    by (simp add: pp_t_binary_truth_pure_unary_iff
      pp_t_conjunction_pure_unary_iff
      pp_t_constant_builder_pure_unary_iff
      pp_t_constants_fragment_pure_unary_iff)
  have classifier_pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_classifier_type w
        pp_t_constants_stock_classifier"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_inherits_constants_pure,
       rule pp_t_constants_classifier_is_pure)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_constants_stock_classifier_in_domain,
      of "pp_t_binary_truth_fragment_pure
        pp_t_constants_classifier_type" w]
      classifier_pure
    by (simp add: unary_classifier
      pp_t_binary_truth_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_binary_truth_target_PP_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_target_PP_holds by blast

lemma pp_t_binary_truth_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_binary_truth_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_binary_truth_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_binary_truth_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_binary_truth_application_closure_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (BinaryTruthFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
      pp_t_binary_truth_application_closure_holds_iff
    using pp_t_binary_truth_fragment_application by blast
qed

theorem pp_t_binary_truth_unique_fundamental_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using
    BinaryTruthFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_binary_truth_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows
    "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
      (pp_no_fundamentals \<sigma>)"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using
    BinaryTruthFragment.pp_t_moving_no_fundamentals_holds[
      OF assms]
  by blast

section \<open>Recombination, Exhaustion, and functionality\<close>

lemma pp_t_binary_truth_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      pp_zeroary_recombination) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_recombination_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_t_domain Prop)"
    have extended:
        "pp_t_env_typed [Prop] (extend_env P \<rho>)"
      using pp_t_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_t_holds
          (pp_t_eval pp_t_binary_truth_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_binary_truth_fragment_pure Prop w P"
      using
        BinaryTruthFragment.pp_t_moving_eval_pure_holds[
          OF var_type extended, of w]
      by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
    proof -
      assume box:
          "pp_t_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_t_holds P w
            \<longleftrightarrow>
            pp_t_holds (pp_zf_truth True) w"
        using pp_t_prop_eqv_at[OF box, of w] by simp
      show "pp_t_holds P w"
        using at_w by simp
    qed
    show "pp_t_holds
        (pp_t_eval pp_t_binary_truth_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
        pp_t_binary_truth_pure_Prop_iff
        pp_t_constant_builder_pure_Prop_iff
        pp_t_constants_fragment_pure_Prop_iff
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_binary_truth_pure_true_implies_necessary:
  assumes P: "Elem P (pp_t_domain Prop)"
    and pure:
      "pp_t_binary_truth_fragment_pure Prop w P"
    and true_now: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  have old_pure:
      "pp_t_constant_builder_fragment_pure Prop w P"
    using pure
    unfolding pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff .
  show ?thesis
    by (rule pp_t_constant_builder_pure_true_implies_necessary[
      OF P old_pure true_now])
qed

lemma pp_t_binary_truth_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      pp_zeroary_exhaustion) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_exhaustion_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_t_domain Prop)"
    have extended:
        "pp_t_env_typed [Prop] (extend_env P \<rho>)"
      using pp_t_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_t_holds
          (pp_t_eval pp_t_binary_truth_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_binary_truth_fragment_pure Prop w P"
      using
        BinaryTruthFragment.pp_t_moving_eval_pure_holds[
          OF var_type extended, of w]
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_binary_truth_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_binary_truth_pure_true_implies_necessary[OF P]
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_binary_truth_zeroary_recombination_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_zeroary_recombination_holds
  by blast

theorem pp_t_binary_truth_zeroary_exhaustion_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_zeroary_exhaustion_holds
  by blast

lemma pp_t_binary_truth_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_binary_truth_fragment_pure
            pp_t_constants_unary_type w X
          \<and> pp_t_moving_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v)
          \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_binary_truth_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_binary_truth_fragment_pure
            pp_t_constants_unary_type w X
          \<and> pp_t_moving_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w)
          \<longrightarrow>
          (\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v))))"
  by (simp add: pp_unary_exhaustion_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

theorem pp_t_binary_truth_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding
    pp_t_binary_truth_unary_recombination_holds_iff
    pp_t_binary_truth_pure_unary_iff
    pp_t_conjunction_pure_unary_iff
    pp_t_constant_builder_pure_unary_iff
  using pp_t_constants_pure_unary_QLN(1)
  by blast

theorem pp_t_binary_truth_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding
    pp_t_binary_truth_unary_exhaustion_holds_iff
    pp_t_binary_truth_pure_unary_iff
    pp_t_conjunction_pure_unary_iff
    pp_t_constant_builder_pure_unary_iff
  using pp_t_constants_pure_unary_QLN(2)
  by blast

theorem pp_t_binary_truth_unary_recombination_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_unary_recombination_holds
  by blast

theorem pp_t_binary_truth_unary_exhaustion_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_binary_truth_unary_exhaustion_holds
  by blast

lemma pp_t_binary_truth_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_binary_truth_fragment_constants \<rho>
        (pp_modalized_functionality \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>g.
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
          (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> x)))
        \<longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g)))"
  by (simp add: pp_modalized_functionality_def
      pp_t_eval_ObjBox_holds pp_t_prop_eqv_truth_iff
      extend_env.simps pp_t_three_extensions_index_two)

theorem pp_t_binary_truth_modalized_functionality_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (BinaryTruthFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      BinaryTruthFragment.MovingTreeConstants.pp_t_den_def
      pp_t_binary_truth_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

section \<open>The binary truth-function fragment\<close>

definition pp_truth_function_purity_axioms :: "oterm set" where
  "pp_truth_function_purity_axioms =
    range
      (\<lambda>F :: bool \<Rightarrow> bool \<Rightarrow> bool.
        pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          (pp_truth_function_builder F))"

definition pp_binary_truth_fragment_PP_axioms ::
    "oterm set"
where
  "pp_binary_truth_fragment_PP_axioms =
    pp_conjunction_fragment_PP_axioms
      \<union> pp_truth_function_purity_axioms"

theorem pp_t_binary_truth_fragment_PP_gvalid:
  "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_binary_truth_fragment_PP_axioms"
  unfolding
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_binary_truth_fragment_PP_axioms"
  from A consider
      (truth_function) F where
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          (pp_truth_function_builder F)"
    | (builder)
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_conjunction_builder"
    | (constant_builder)
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_constant_builder"
    | (constant_truth)
        "A = pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue)"
    | (constant_falsity)
        "A = pp_pure pp_unary_ty
          (pp_constant_operator ObjFalse)"
    | (identity_purity)
        "A = pp_pure pp_t_idneg_unary_type prop_id"
    | (negation_purity)
        "A = pp_pure pp_t_idneg_unary_type
          pp_negation_operator"
    | (target) "A = pp_target_PP"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> pp_modalized_functionality_schema"
    unfolding pp_binary_truth_fragment_PP_axioms_def
      pp_truth_function_purity_axioms_def
      pp_conjunction_fragment_PP_axioms_def
      pp_constant_builder_fragment_PP_axioms_def
      pp_logical_constants_fragment_PP_axioms_def
      pp_identity_negation_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show
      "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case truth_function
    then show ?thesis
      using pp_t_truth_function_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case builder
    then show ?thesis
      using pp_t_binary_truth_conjunction_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_builder
    then show ?thesis
      using pp_t_binary_truth_constant_builder_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_truth
    then show ?thesis
      using pp_t_binary_truth_constant_truth_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_falsity
    then show ?thesis
      using pp_t_binary_truth_constant_falsity_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case identity_purity
    then show ?thesis
      using pp_t_binary_truth_identity_purity_gvalid by simp
  next
    case negation_purity
    then show ?thesis
      using pp_t_binary_truth_negation_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_binary_truth_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_binary_truth_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_binary_truth_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule
        pp_t_binary_truth_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_binary_truth_zeroary_recombination_gvalid
      by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_binary_truth_unary_recombination_gvalid
      by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_binary_truth_zeroary_exhaustion_gvalid
      by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_binary_truth_unary_exhaustion_gvalid
      by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_binary_truth_modalized_functionality_gvalid)
  qed
qed

theorem pp_binary_truth_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_binary_truth_fragment_PP_axioms"
  using
    BinaryTruthFragment.MovingTreeConstants.pp_t_base_sound
    BinaryTruthFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_binary_truth_fragment_PP_gvalid
  by (rule
    BinaryTruthFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_binary_truth_fragment_consistent:
  assumes "U \<subseteq> pp_binary_truth_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_binary_truth_fragment_PP_gvalid
    unfolding
      BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      BinaryTruthFragment.MovingTreeConstants.pp_t_base_sound
      BinaryTruthFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      BinaryTruthFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
