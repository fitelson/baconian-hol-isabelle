theory Bacon_PP_Fresh_Relative_Lindenbaum
  imports Goodman_CEVplus.Bacon_CEV_Axiom_Extension
begin

section \<open>A Lindenbaum extension relative to added principles\<close>

text \<open>
  The added principles remain axioms of CEV, and hence remain available to
  Generalization, Instantiation, and Equivalence.  Temporary assumptions have
  a different role: above them we use only modus ponens.  The judgement
  \<open>\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A\<close> records this distinction.

  We now carry out the ordinary Lindenbaum construction in its third argument.
  Thus the resulting theory is maximal among local theories relative to the
  fixed stock \<open>T\<close> of added principles.  In particular, it contains every
  theorem of CEV extended by \<open>T\<close>.
\<close>

subsection \<open>Finite support and relative consistency\<close>

lemma CEV_axiom_from_finite_support:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  obtains S0 where "finite S0" and "S0 \<subseteq> S"
    and "\<Gamma> ; T ; S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
proof -
  have "\<exists>S0. finite S0 \<and> S0 \<subseteq> S \<and>
      \<Gamma> ; T ; S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using assms
  proof (induction rule: CEV_axiom_from.induct)
    case (Assumption A S \<Gamma> T)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> T A S)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (MP \<Gamma> T S A B)
    obtain S1 where finite_S1: "finite S1" and S1_sub: "S1 \<subseteq> S"
      and d_A: "\<Gamma> ; T ; S1 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
      using MP.IH(1) by auto
    obtain S2 where finite_S2: "finite S2" and S2_sub: "S2 \<subseteq> S"
      and d_imp: "\<Gamma> ; T ; S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A B"
      using MP.IH(2) by auto
    have d_A': "\<Gamma> ; T ; S1 \<union> S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
      using d_A by (rule CEV_axiom_from_mono) auto
    have d_imp': "\<Gamma> ; T ; S1 \<union> S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A B"
      using d_imp by (rule CEV_axiom_from_mono) auto
    have d_B: "\<Gamma> ; T ; S1 \<union> S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
      using d_A' d_imp' by (rule CEV_axiom_from.MP)
    show ?case
      using finite_S1 S1_sub finite_S2 S2_sub d_B
      by (intro exI[of _ "S1 \<union> S2"]) auto
  qed
  then show ?thesis
    using that by blast
qed

definition CEV_axiom_relative_consistent ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_axiom_relative_consistent \<Gamma> T S \<longleftrightarrow>
    \<not> \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"

lemma CEV_axiom_relative_consistentD:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
  shows "\<not> \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  using assms unfolding CEV_axiom_relative_consistent_def by blast

lemma CEV_axiom_relative_consistent_mono:
  assumes "CEV_axiom_relative_consistent \<Gamma> T U"
    and "S \<subseteq> U"
  shows "CEV_axiom_relative_consistent \<Gamma> T S"
  using assms CEV_axiom_from_mono
  unfolding CEV_axiom_relative_consistent_def by blast

lemma CEV_axiom_consistent_iff_empty_relative_consistent:
  "CEV_axiom_consistent \<Gamma> T \<longleftrightarrow>
    CEV_axiom_relative_consistent \<Gamma> T {}"
  unfolding CEV_axiom_consistent_def CEV_axiom_relative_consistent_def
  using CEV_axiom_from_empty_iff by blast

lemma CEV_axiom_relative_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and inconsistent_A:
      "\<not> CEV_axiom_relative_consistent \<Gamma> T (insert A S)"
  shows "CEV_axiom_relative_consistent \<Gamma> T (insert (Neg A) S)"
proof (unfold CEV_axiom_relative_consistent_def, intro notI)
  have d_false_A:
    "\<Gamma> ; T ; insert A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using inconsistent_A unfolding CEV_axiom_relative_consistent_def by blast
  have d_imp_A_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A ObjFalse"
    using A_type d_false_A by (rule CEV_axiom_from_deduction)
  have d_neg_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp A ObjFalse) (Neg A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_neg: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    using d_imp_A_false d_neg_rule by (rule CEV_axiom_from.MP)

  assume d_false_neg:
    "\<Gamma> ; T ; insert (Neg A) S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have d_imp_neg_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false_neg by (rule CEV_axiom_from_deduction)
  have d_A_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp (Neg A) ObjFalse) A"
    using CEV_proves_imp_neg_false_to_formula[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_A: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using d_imp_neg_false d_A_rule by (rule CEV_axiom_from.MP)
  have d_false: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_A d_neg by (rule CEV_axiom_from_contradiction)
  show False
    using consistent d_false
    unfolding CEV_axiom_relative_consistent_def by blast
qed

lemma CEV_axiom_relative_consistent_decidable_extension:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "CEV_axiom_relative_consistent \<Gamma> T (insert A S) \<or>
    CEV_axiom_relative_consistent \<Gamma> T (insert (Neg A) S)"
proof (cases "CEV_axiom_relative_consistent \<Gamma> T (insert A S)")
  case True
  then show ?thesis by blast
next
  case False
  have "CEV_axiom_relative_consistent \<Gamma> T (insert (Neg A) S)"
    using assms False
    by (rule CEV_axiom_relative_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis by blast
qed

subsection \<open>The relative Lindenbaum construction\<close>

definition CEV_axiom_relative_locally_maximal_consistent ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S \<longleftrightarrow>
    typed_theory \<Gamma> S \<and>
    CEV_axiom_relative_consistent \<Gamma> T S \<and>
    CEV_negation_complete \<Gamma> S"

definition CEV_axiom_relative_lindenbaum_step ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_axiom_relative_lindenbaum_step \<Gamma> T A S =
    (if \<Gamma> \<turnstile> A : Prop then
      (if CEV_axiom_relative_consistent \<Gamma> T (insert A S)
       then insert A S else insert (Neg A) S)
     else S)"

primrec CEV_axiom_relative_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum 0 = S"
| "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n) =
    CEV_axiom_relative_lindenbaum_step \<Gamma> T (enum n)
      (CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"

definition CEV_axiom_relative_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum =
    (\<Union>n. CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"

lemma CEV_axiom_relative_lindenbaum_step_extends:
  "S \<subseteq> CEV_axiom_relative_lindenbaum_step \<Gamma> T A S"
  unfolding CEV_axiom_relative_lindenbaum_step_def by auto

lemma CEV_axiom_relative_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_lindenbaum_step \<Gamma> T A S)"
  using assms
  unfolding CEV_axiom_relative_lindenbaum_step_def typed_theory_def by auto

lemma CEV_axiom_relative_lindenbaum_step_consistent:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_lindenbaum_step \<Gamma> T A S)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding CEV_axiom_relative_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "CEV_axiom_relative_consistent \<Gamma> T (insert A S)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close>
      unfolding CEV_axiom_relative_lindenbaum_step_def by simp
  next
    case False
    have "CEV_axiom_relative_consistent \<Gamma> T (insert (Neg A) S)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule CEV_axiom_relative_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      unfolding CEV_axiom_relative_lindenbaum_step_def by simp
  qed
qed

lemma CEV_axiom_relative_lindenbaum_chain_step:
  "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n \<subseteq>
    CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n)"
  using CEV_axiom_relative_lindenbaum_step_extends[
    of "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n" \<Gamma> T "enum n"]
  by simp

lemma CEV_axiom_relative_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_axiom_relative_lindenbaum_step_typed)
qed

lemma CEV_axiom_relative_lindenbaum_chain_consistent:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_axiom_relative_lindenbaum_step_consistent)
qed

lemma CEV_axiom_relative_lindenbaum_extension_extends:
  "S \<subseteq> CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum"
proof
  fix A
  assume "A \<in> S"
  then have "A \<in> CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum 0"
    by simp
  then show "A \<in> CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum"
    unfolding CEV_axiom_relative_lindenbaum_extension_def by blast
qed

lemma CEV_axiom_relative_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
proof -
  have "\<And>n. typed_theory \<Gamma>
      (CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"
    using assms by (rule CEV_axiom_relative_lindenbaum_chain_typed)
  then show ?thesis
    unfolding CEV_axiom_relative_lindenbaum_extension_def
    by (rule typed_theory_nat_union)
qed

lemma CEV_axiom_relative_lindenbaum_extension_consistent:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
proof (unfold CEV_axiom_relative_consistent_def, intro notI)
  assume d_false:
    "\<Gamma> ; T ; CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub:
      "U \<subseteq> CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum"
    and d_U: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_false by (rule CEV_axiom_from_finite_support)
  have U_sub_union:
    "U \<subseteq> (\<Union>n. CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"
    using U_sub unfolding CEV_axiom_relative_lindenbaum_extension_def .
  have step: "\<And>n.
      CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n \<subseteq>
      CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n)"
    by (rule CEV_axiom_relative_lindenbaum_chain_step)
  obtain n where U_sub_chain:
    "U \<subseteq> CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have "\<Gamma> ; T ;
      CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_axiom_from_mono)
  moreover have "CEV_axiom_relative_consistent \<Gamma> T
      (CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n)"
    using assms by (rule CEV_axiom_relative_lindenbaum_chain_consistent)
  ultimately show False
    unfolding CEV_axiom_relative_consistent_def by blast
qed

lemma CEV_axiom_relative_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "CEV_negation_complete \<Gamma>
    (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
proof (unfold CEV_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?U = "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum n"
  have step_eq:
    "CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n) =
      CEV_axiom_relative_lindenbaum_step \<Gamma> T A ?U"
    using enum_n by simp
  have "A \<in> CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n) \<or>
      Neg A \<in> CEV_axiom_relative_lindenbaum_chain \<Gamma> T S enum (Suc n)"
  proof (cases "CEV_axiom_relative_consistent \<Gamma> T (insert A ?U)")
    case True
    have "A \<in> CEV_axiom_relative_lindenbaum_step \<Gamma> T A ?U"
      using A_type True
      unfolding CEV_axiom_relative_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> CEV_axiom_relative_lindenbaum_step \<Gamma> T A ?U"
      using A_type False
      unfolding CEV_axiom_relative_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum \<or>
      Neg A \<in> CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum"
    unfolding CEV_axiom_relative_lindenbaum_extension_def by blast
qed

theorem CEV_axiom_relative_lindenbaum_extension_locally_maximal_consistent:
  assumes "typed_theory \<Gamma> S"
    and "CEV_axiom_relative_consistent \<Gamma> T S"
    and "enumerates_formulas \<Gamma> enum"
  shows "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T
    (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
proof -
  have typed: "typed_theory \<Gamma>
      (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
    using assms(1) by (rule CEV_axiom_relative_lindenbaum_extension_typed)
  have consistent: "CEV_axiom_relative_consistent \<Gamma> T
      (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
    using assms(2) by (rule CEV_axiom_relative_lindenbaum_extension_consistent)
  have complete: "CEV_negation_complete \<Gamma>
      (CEV_axiom_relative_lindenbaum_extension \<Gamma> T S enum)"
    using assms(3)
    by (rule CEV_axiom_relative_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CEV_axiom_relative_locally_maximal_consistent_def by simp
qed

subsection \<open>Closure and containment of the extended theory\<close>

lemma CEV_axiom_relative_locally_maximal_consistent_deductively_closed:
  assumes "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S"
    and "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "A \<in> S"
proof (cases "A \<in> S")
  case True
  then show ?thesis .
next
  case False
  have consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    using assms(1)
    unfolding CEV_axiom_relative_locally_maximal_consistent_def by blast
  have complete: "CEV_negation_complete \<Gamma> S"
    using assms(1)
    unfolding CEV_axiom_relative_locally_maximal_consistent_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule CEV_axiom_from_formula)
  have neg_in: "Neg A \<in> S"
    using complete A_type False unfolding CEV_negation_complete_def by blast
  have d_neg: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    using neg_in A_type by (intro CEV_axiom_from.Assumption) auto
  have d_false: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using assms(2) d_neg by (rule CEV_axiom_from_contradiction)
  then show ?thesis
    using consistent
    unfolding CEV_axiom_relative_consistent_def by blast
qed

lemma CEV_axiom_relative_locally_maximal_consistent_contains_theorems:
  assumes "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "A \<in> S"
proof -
  have d_A: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using assms(2) by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using assms(1) d_A
    by (rule CEV_axiom_relative_locally_maximal_consistent_deductively_closed)
qed

theorem CEV_axiom_consistent_has_relative_lindenbaum_extension:
  assumes consistent: "CEV_axiom_consistent \<Gamma> T"
    and enum: "enumerates_formulas \<Gamma> enum"
  defines "S \<equiv> CEV_axiom_relative_lindenbaum_extension \<Gamma> T {} enum"
  shows "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S"
    and "\<And>A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> S"
proof -
  have empty_typed: "typed_theory \<Gamma> {}"
    unfolding typed_theory_def by simp
  have empty_consistent: "CEV_axiom_relative_consistent \<Gamma> T {}"
    using consistent CEV_axiom_consistent_iff_empty_relative_consistent
    by blast
  have maximal: "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T
      (CEV_axiom_relative_lindenbaum_extension \<Gamma> T {} enum)"
    using empty_typed empty_consistent enum
    by (rule CEV_axiom_relative_lindenbaum_extension_locally_maximal_consistent)
  show "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S"
    using maximal unfolding S_def .
  fix A
  assume d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  show "A \<in> S"
    using maximal d_A
    unfolding S_def
    by (rule CEV_axiom_relative_locally_maximal_consistent_contains_theorems)
qed

end
