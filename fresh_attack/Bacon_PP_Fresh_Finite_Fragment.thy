theory Bacon_PP_Fresh_Finite_Fragment
  imports "Higher_Order_Metaphysics.Bacon_CEV_Axiom_Extension"
begin

section \<open>A finitary form of Goodman's consistency question\<close>

text \<open>
  This theory begins from the foundational statement of the problem and
  imports no result from another attempted solution.

  The first lemma supplies the compactness fact appropriate to the
  axiom-extension consequence relation.  The earlier finite-support theorem for
  local consequence does not by itself cover derivations in which
  Generalization, Instantiation, and vector Equivalence are applied above the
  added principles.
\<close>

lemma CEV_axiom_proves_finite_support_ex:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<exists>U. finite U \<and> U \<subseteq> T \<and>
    \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
proof (induction rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  have "\<Gamma> ; {A} \<turnstile>\<^sub>CEV\<^sup>+ A"
    using Axiom.hyps by (intro CEV_axiom_proves.Axiom) auto
  then show ?case
    using Axiom.hyps by auto
next
  case (Base \<Gamma> A T)
  have "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ A"
    using Base.hyps by (rule CEV_axiom_proves.Base)
  then show ?case
    by auto
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
    and d_body:
      "\<sigma>s @ \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ zeta_body \<sigma>s F G"
    using VectorEquivalence.IH by auto
  have "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+
      Eq (arrow_type \<sigma>s Prop) F G"
    using VectorEquivalence.hyps(1,2) d_body
    by (rule CEV_axiom_proves.VectorEquivalence)
  then show ?case
    using finite_U U_sub by auto
next
  case (MP \<Gamma> T A B)
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
    and d_A: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
    using MP.IH(1) by auto
  obtain V where finite_V: "finite V" and V_sub: "V \<subseteq> T"
    and d_imp: "\<Gamma> ; V \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    using MP.IH(2) by auto
  have d_A_union: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sup>+ A"
    using d_A by (rule CEV_axiom_proves_mono) auto
  have d_imp_union: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    using d_imp by (rule CEV_axiom_proves_mono) auto
  have "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sup>+ B"
    using d_A_union d_imp_union by (rule CEV_axiom_proves.MP)
  then show ?case
    using finite_U finite_V U_sub V_sub by auto
next
  case (Gen \<Gamma> P \<sigma> Q T)
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
    and d_imp:
      "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q"
    using Gen.IH by auto
  have "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp P (Forall \<sigma> Q)"
    using Gen.hyps(1,2) d_imp by (rule CEV_axiom_proves.Gen)
  then show ?case
    using finite_U U_sub by auto
next
  case (Inst \<sigma> \<Gamma> P Q T)
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
    and d_imp:
      "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
    using Inst.IH by auto
  have "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> P) Q"
    using Inst.hyps(1,2) d_imp by (rule CEV_axiom_proves.Inst)
  then show ?case
    using finite_U U_sub by auto
qed

lemma CEV_axiom_proves_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  obtains U where "finite U" and "U \<subseteq> T"
    and "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
  using CEV_axiom_proves_finite_support_ex[OF assms] that by auto

theorem CEV_axiom_consistent_iff_finite_fragments:
  "CEV_axiom_consistent \<Gamma> T \<longleftrightarrow>
    (\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow>
      CEV_axiom_consistent \<Gamma> U)"
proof
  assume consistent_T: "CEV_axiom_consistent \<Gamma> T"
  show "\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow>
      CEV_axiom_consistent \<Gamma> U"
  proof (intro allI impI)
    fix U
    assume U_sub: "U \<subseteq> T"
    show "CEV_axiom_consistent \<Gamma> U"
    proof (unfold CEV_axiom_consistent_def, intro notI)
      assume "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
      then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
        using U_sub by (rule CEV_axiom_proves_mono)
      then show False
        using consistent_T unfolding CEV_axiom_consistent_def by blast
    qed
  qed
next
  assume finite_consistent:
    "\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow>
      CEV_axiom_consistent \<Gamma> U"
  show "CEV_axiom_consistent \<Gamma> T"
  proof (unfold CEV_axiom_consistent_def, intro notI)
    assume d_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> T"
      and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
      using d_false by (rule CEV_axiom_proves_finite_support)
    have "CEV_axiom_consistent \<Gamma> U"
      using finite_consistent finite_U U_sub by blast
    then show False
      using d_U unfolding CEV_axiom_consistent_def by blast
  qed
qed

subsection \<open>The background theory and Purity of Pure\<close>

definition fresh_modalized_functionality :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where
  "fresh_modalized_functionality \<sigma> \<tau> =
    Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (Imp
          (\<box>\<^sub>o (Forall \<sigma>
            (Eq \<tau> (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))))
          (Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1) (Var 0))))"

lemma typed_fresh_modalized_functionality:
  "[] \<turnstile> fresh_modalized_functionality \<sigma> \<tau> : Prop"
  by (rule infer_type_sound)
    (simp add: fresh_modalized_functionality_def ObjBox_def ObjTrue_def
      lookup_def)

definition fresh_modalized_functionality_schema :: "oterm set" where
  "fresh_modalized_functionality_schema =
    {A. \<exists>\<sigma> \<tau>. A = fresh_modalized_functionality \<sigma> \<tau>}"

lemma fresh_modalized_functionality_schema_typed:
  assumes "A \<in> fresh_modalized_functionality_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_fresh_modalized_functionality
  unfolding fresh_modalized_functionality_schema_def by blast

definition fresh_goodman_background_axioms :: "oterm set" where
  "fresh_goodman_background_axioms =
    pp_full_QLN_background_axioms \<union>
    fresh_modalized_functionality_schema"

definition fresh_goodman_axioms :: "oterm set" where
  "fresh_goodman_axioms =
    insert pp_target_PP fresh_goodman_background_axioms"

definition fresh_goodman_consistency_question :: bool where
  "fresh_goodman_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] fresh_goodman_axioms"

lemma fresh_goodman_axioms_typed:
  assumes "A \<in> fresh_goodman_axioms"
  shows "[] \<turnstile> A : Prop"
proof -
  have full_typed:
    "\<And>B. B \<in> pp_full_QLN_PP_axioms \<Longrightarrow> [] \<turnstile> B : Prop"
    by (rule pp_full_QLN_PP_axioms_typed)
  show ?thesis
    using assms full_typed fresh_modalized_functionality_schema_typed
    unfolding fresh_goodman_axioms_def fresh_goodman_background_axioms_def
      pp_full_QLN_PP_axioms_def
    by blast
qed

theorem fresh_goodman_consistency_iff_finite_fragments:
  "fresh_goodman_consistency_question \<longleftrightarrow>
    (\<forall>U. finite U \<longrightarrow> U \<subseteq> fresh_goodman_axioms \<longrightarrow>
      CEV_axiom_consistent [] U)"
  unfolding fresh_goodman_consistency_question_def
  by (rule CEV_axiom_consistent_iff_finite_fragments)

theorem fresh_goodman_negative_answer_iff_finite_inconsistent_core:
  "\<not> fresh_goodman_consistency_question \<longleftrightarrow>
    (\<exists>U. finite U \<and> U \<subseteq> fresh_goodman_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse)"
proof
  assume "\<not> fresh_goodman_consistency_question"
  then have d_false:
    "[] ; fresh_goodman_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    unfolding fresh_goodman_consistency_question_def
      CEV_axiom_consistent_def
    by simp
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> fresh_goodman_axioms"
    and d_U: "[] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using d_false by (rule CEV_axiom_proves_finite_support)
  show "\<exists>U. finite U \<and> U \<subseteq> fresh_goodman_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using finite_U U_sub d_U by auto
next
  assume "\<exists>U. finite U \<and> U \<subseteq> fresh_goodman_axioms \<and>
      [] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  then obtain U where U_sub: "U \<subseteq> fresh_goodman_axioms"
    and d_U: "[] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    by auto
  have "[] ; fresh_goodman_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using d_U U_sub by (rule CEV_axiom_proves_mono)
  then show "\<not> fresh_goodman_consistency_question"
    unfolding fresh_goodman_consistency_question_def
      CEV_axiom_consistent_def
    by simp
qed

text \<open>
  Thus the open question has an exact finite-fragment form for the intended
  proof relation.  An affirmative solution may establish consistency for each
  finite set of additional principles separately; a negative solution must
  exhibit one such finite set and a checked derivation of falsity from it.

  This is a proof-theoretic reduction, not yet a model of the theory.  The
  clean Henkin construction for CEV concerns CEV theorems together with local
  assumptions.  To obtain a model from the result above, one must still prove
  the corresponding extension theorem for CEV with additional axioms: each
  consistent, well-typed set of additional principles must extend to a Henkin
  theory in which those principles are true and in which Generalization,
  Instantiation, and vector Equivalence remain sound when applied to
  conclusions obtained from them.
\<close>

end
