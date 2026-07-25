theory Bacon_PP
  imports Bacon_Zeta
begin

section \<open>Goodman's Purity of Pure consistency question\<close>

text \<open>
  This theory states the question over the clean Bacon--Dorr background:
  Baconian H, Classicism, propositional Equivalence, and theorem-level vector
  Equivalence.  It assumes no contextual equivalence rule and contains no
  application-specific theory.

  We consider exactly one fundamental entity, a proposition, and no
  fundamentals at any other type.  The target PP instance says that the
  purity predicate for unary propositional operators is itself pure.  Purity
  of Fun is deliberately absent.
\<close>

subsection \<open>Vocabulary\<close>

definition pp_pure_name :: string where
  "pp_pure_name = ''Pure''"

definition pp_fun_name :: string where
  "pp_fun_name = ''Fun''"

definition pp_Pure :: "otype \<Rightarrow> oterm" where
  "pp_Pure \<sigma> = Const pp_pure_name (\<sigma> \<rightarrow>\<^sub>o Prop)"

definition pp_Fun :: "otype \<Rightarrow> oterm" where
  "pp_Fun \<sigma> = Const pp_fun_name (\<sigma> \<rightarrow>\<^sub>o Prop)"

definition pp_pure :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pure \<sigma> M = App (pp_Pure \<sigma>) M"

definition pp_fun :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_fun \<sigma> M = App (pp_Fun \<sigma>) M"

lemma typed_pp_Pure:
  "\<Gamma> \<turnstile> pp_Pure \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding pp_Pure_def by (rule has_type.Const)

lemma typed_pp_Fun:
  "\<Gamma> \<turnstile> pp_Fun \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding pp_Fun_def by (rule has_type.Const)

lemma typed_pp_pure:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_pure \<sigma> M : Prop"
  unfolding pp_pure_def
  using typed_pp_Pure assms by (rule has_type.App)

lemma typed_pp_fun:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_fun \<sigma> M : Prop"
  unfolding pp_fun_def
  using typed_pp_Fun assms by (rule has_type.App)

subsection \<open>Named principles\<close>

definition pp_purity_of_pure :: "otype \<Rightarrow> oterm" where
  "pp_purity_of_pure \<sigma> =
    pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (pp_Pure \<sigma>)"

definition pp_purity_of_fun :: "otype \<Rightarrow> oterm" where
  "pp_purity_of_fun \<sigma> =
    pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (pp_Fun \<sigma>)"

definition pp_application_closure :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where
  "pp_application_closure \<sigma> \<tau> =
    Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (Var 1) (Var 0)))))"

definition pp_persistence :: "otype \<Rightarrow> oterm" where
  "pp_persistence \<sigma> =
    Forall \<sigma>
      (Imp (pp_pure \<sigma> (Var 0))
        (\<box>\<^sub>o (pp_pure \<sigma> (Var 0))))"

definition pp_unique_fundamental :: "otype \<Rightarrow> oterm" where
  "pp_unique_fundamental \<sigma> =
    Exists \<sigma>
      (Conj
        (pp_fun \<sigma> (Var 0))
        (Forall \<sigma>
          (Imp (pp_fun \<sigma> (Var 0)) (Eq \<sigma> (Var 0) (Var 1)))))"

definition pp_no_fundamentals :: "otype \<Rightarrow> oterm" where
  "pp_no_fundamentals \<sigma> =
    Forall \<sigma> (Neg (pp_fun \<sigma> (Var 0)))"

text \<open>
  With exactly one fundamental proposition, the required nonzero-arity QLN
  instance is unary.  The zero-ary instance is included separately.
\<close>

definition pp_zeroary_QLN :: oterm where
  "pp_zeroary_QLN =
    Forall Prop
      (Imp (pp_pure Prop (Var 0))
        ((\<box>\<^sub>o (Var 0)) \<longleftrightarrow>\<^sub>o Var 0))"

definition pp_unary_QLN :: oterm where
  "pp_unary_QLN =
    Forall (Prop \<rightarrow>\<^sub>o Prop)
      (Forall Prop
        (Imp
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))
          ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
            Forall Prop (App (Var 2) (Var 0)))))"

definition pp_QSS :: oterm where
  "pp_QSS =
    Forall (Prop \<rightarrow>\<^sub>o Prop)
      (Forall (Prop \<rightarrow>\<^sub>o Prop)
        (Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 2))
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))
              (Eq (Prop \<rightarrow>\<^sub>o Prop) (Var 2) (Var 1))))))"

lemma typed_pp_purity_of_pure:
  "[] \<turnstile> pp_purity_of_pure \<sigma> : Prop"
  unfolding pp_purity_of_pure_def
  using typed_pp_Pure by (rule typed_pp_pure)

lemma typed_pp_purity_of_fun:
  "[] \<turnstile> pp_purity_of_fun \<sigma> : Prop"
  unfolding pp_purity_of_fun_def
  using typed_pp_Fun by (rule typed_pp_pure)

lemma typed_pp_application_closure:
  "[] \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)

lemma typed_pp_persistence:
  "[] \<turnstile> pp_persistence \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_persistence_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unique_fundamental:
  "[] \<turnstile> pp_unique_fundamental \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def lookup_def)

lemma typed_pp_no_fundamentals:
  "[] \<turnstile> pp_no_fundamentals \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def lookup_def)

lemma typed_pp_zeroary_QLN:
  "[] \<turnstile> pp_zeroary_QLN : Prop"
  by (rule infer_type_sound)
    (simp add: pp_zeroary_QLN_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_unary_QLN:
  "[] \<turnstile> pp_unary_QLN : Prop"
  by (rule infer_type_sound)
    (simp add: pp_unary_QLN_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)

lemma typed_pp_QSS:
  "[] \<turnstile> pp_QSS : Prop"
  by (rule infer_type_sound)
    (simp add: pp_QSS_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def lookup_def)

subsection \<open>The axiom package\<close>

fun pp_consts_of :: "oterm \<Rightarrow> string set" where
  "pp_consts_of (Var n) = {}"
| "pp_consts_of (Const c \<sigma>) = {c}"
| "pp_consts_of (App M N) = pp_consts_of M \<union> pp_consts_of N"
| "pp_consts_of (Lam \<sigma> M) = pp_consts_of M"
| "pp_consts_of (Eq \<sigma> M N) = pp_consts_of M \<union> pp_consts_of N"
| "pp_consts_of (Neg A) = pp_consts_of A"
| "pp_consts_of (Conj A B) = pp_consts_of A \<union> pp_consts_of B"
| "pp_consts_of (Disj A B) = pp_consts_of A \<union> pp_consts_of B"
| "pp_consts_of (Imp A B) = pp_consts_of A \<union> pp_consts_of B"
| "pp_consts_of (Forall \<sigma> A) = pp_consts_of A"
| "pp_consts_of (Exists \<sigma> A) = pp_consts_of A"

definition pp_logical_vocabulary :: "oterm \<Rightarrow> bool" where
  "pp_logical_vocabulary M \<longleftrightarrow> pp_consts_of M = {}"

definition pp_purity_schema :: "oterm set" where
  "pp_purity_schema =
    {A. \<exists>\<sigma> M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and>
      A = pp_pure \<sigma> M}"

definition pp_application_closure_schema :: "oterm set" where
  "pp_application_closure_schema =
    {A. \<exists>\<sigma> \<tau>. A = pp_application_closure \<sigma> \<tau>}"

definition pp_no_other_fundamentals_schema :: "oterm set" where
  "pp_no_other_fundamentals_schema =
    {A. \<exists>\<sigma>. \<sigma> \<noteq> Prop \<and> A = pp_no_fundamentals \<sigma>}"

definition pp_persistence_schema :: "oterm set" where
  "pp_persistence_schema = {A. \<exists>\<sigma>. A = pp_persistence \<sigma>}"

definition pp_target_PP :: oterm where
  "pp_target_PP = pp_purity_of_pure (Prop \<rightarrow>\<^sub>o Prop)"

definition pp_core_axioms :: "oterm set" where
  "pp_core_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_target_PP} \<union>
    {pp_unique_fundamental Prop} \<union>
    pp_no_other_fundamentals_schema"

definition pp_full_QLN_axioms :: "oterm set" where
  "pp_full_QLN_axioms =
    pp_core_axioms \<union> {pp_zeroary_QLN, pp_unary_QLN}"

definition pp_full_QLN_persistence_axioms :: "oterm set" where
  "pp_full_QLN_persistence_axioms =
    pp_full_QLN_axioms \<union> pp_persistence_schema"

lemma typed_pp_target_PP:
  "[] \<turnstile> pp_target_PP : Prop"
  unfolding pp_target_PP_def by (rule typed_pp_purity_of_pure)

definition pp_typed_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "pp_typed_theory \<Gamma> T \<longleftrightarrow> (\<forall>A \<in> T. \<Gamma> \<turnstile> A : Prop)"

lemma pp_purity_schema_typed:
  assumes "A \<in> pp_purity_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_pure
  unfolding pp_purity_schema_def by blast

lemma pp_application_closure_schema_typed:
  assumes "A \<in> pp_application_closure_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_application_closure
  unfolding pp_application_closure_schema_def by blast

lemma pp_no_other_fundamentals_schema_typed:
  assumes "A \<in> pp_no_other_fundamentals_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_no_fundamentals
  unfolding pp_no_other_fundamentals_schema_def by blast

lemma pp_full_QLN_axioms_typed:
  "pp_typed_theory [] pp_full_QLN_axioms"
  unfolding pp_typed_theory_def pp_full_QLN_axioms_def pp_core_axioms_def
  using pp_purity_schema_typed pp_application_closure_schema_typed
    pp_no_other_fundamentals_schema_typed typed_pp_target_PP
    typed_pp_unique_fundamental typed_pp_zeroary_QLN typed_pp_unary_QLN
  by blast

lemma pp_target_PP_is_assumed:
  "pp_target_PP \<in> pp_full_QLN_axioms"
  unfolding pp_full_QLN_axioms_def pp_core_axioms_def by blast

lemma pp_unique_fundamental_proposition_is_assumed:
  "pp_unique_fundamental Prop \<in> pp_full_QLN_axioms"
  unfolding pp_full_QLN_axioms_def pp_core_axioms_def by blast

subsection \<open>Derivability from assumptions and consistency\<close>

inductive CEV_from :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>CEV\<^sub>s _" [50, 50, 50] 50) where
  Assumption[intro]:
    "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
| Theorem[intro]:
    "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
| Derive_MP[intro]:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"

lemma CEV_from_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_from.induct)
  case (Assumption A T \<Gamma>)
  then show ?case .
next
  case (Theorem \<Gamma> A T)
  then show ?case by (rule CEV_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case by (auto elim: has_type.cases)
qed

lemma CEV_from_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms
proof (induction rule: CEV_from.induct)
  case (Assumption A T \<Gamma>)
  then show ?case by (intro CEV_from.Assumption) blast+
next
  case (Theorem \<Gamma> A T)
  then show ?case by (rule CEV_from.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case by (rule CEV_from.Derive_MP)
qed

lemma CEV_from_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  obtains U where "finite U" and "U \<subseteq> T"
    and "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms
proof (induction rule: CEV_from.induct)
  case (Assumption A T \<Gamma>)
  show ?case
    using Assumption.hyps
    by (intro Assumption.prems[of "{A}"]) auto
next
  case (Theorem \<Gamma> A T)
  show ?case
    using Theorem.hyps
    by (intro Theorem.prems[of "{}"]) auto
next
  case (Derive_MP \<Gamma> T A B)
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
    and d_A: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
    using Derive_MP.IH(1) by blast
  obtain V where finite_V: "finite V" and V_sub: "V \<subseteq> T"
    and d_imp: "\<Gamma> ; V \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
    using Derive_MP.IH(2) by blast
  have d_A': "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sub>s A"
    using d_A by (rule CEV_from_mono) blast
  have d_imp': "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
    using d_imp by (rule CEV_from_mono) blast
  show ?case
    using finite_U finite_V U_sub V_sub d_A' d_imp'
    by (intro Derive_MP.prems[of "U \<union> V"]) (blast intro: CEV_from.Derive_MP)+
qed

definition CEV_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_consistent \<Gamma> T \<longleftrightarrow>
    \<not> (\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse)"

subsection \<open>The exact open question\<close>

definition pp_consistency_question :: bool where
  "pp_consistency_question \<longleftrightarrow>
    CEV_consistent [] pp_full_QLN_axioms"

definition pp_consistency_question_with_persistence :: bool where
  "pp_consistency_question_with_persistence \<longleftrightarrow>
    CEV_consistent [] pp_full_QLN_persistence_axioms"

theorem pp_negative_answer_iff_derives_contradiction:
  "\<not> pp_consistency_question \<longleftrightarrow>
    [] ; pp_full_QLN_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  unfolding pp_consistency_question_def CEV_consistent_def by blast

theorem pp_negative_answer_iff_finite_inconsistent_core:
  "\<not> pp_consistency_question \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse)"
proof
  assume "\<not> pp_consistency_question"
  then have "[] ; pp_full_QLN_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using pp_negative_answer_iff_derives_contradiction by blast
  then obtain U where "finite U" and "U \<subseteq> pp_full_QLN_axioms"
    and "[] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by (rule CEV_from_finite_support)
  then show "\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by blast
next
  assume "\<exists>U. finite U \<and> U \<subseteq> pp_full_QLN_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then obtain U where "U \<subseteq> pp_full_QLN_axioms"
    and "[] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by blast
  then have "[] ; pp_full_QLN_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by (rule CEV_from_mono)
  then show "\<not> pp_consistency_question"
    using pp_negative_answer_iff_derives_contradiction by blast
qed

text \<open>
  No consistency verdict is asserted here.  An affirmative answer requires a
  model or a consistency proof for this exact package.  A negative answer
  requires a CEV derivation of falsity, equivalently one from a finite subset.
\<close>

end
