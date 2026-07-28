theory Bacon_PP_Fresh_Relative_Henkin_Completion
  imports Bacon_CEV_Axiom_Relative_Henkin
    Bacon_Classicism.Bacon_Clean_Completeness
begin

section \<open>A clean Henkin theory for all consequences of added principles\<close>

text \<open>
  We iterate the fresh-witness step while keeping the added principles in the
  axiom position of CEV+.  At the final Lindenbaum stage they remain available
  to Generalization, Instantiation, and vector Equivalence.  Thus the completed
  theory contains every CEV+ consequence, rather than merely an arbitrary
  finite selection of them.
\<close>

primrec CEV_axiom_relative_staged_henkin_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum 0 = S"
| "CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum (Suc n) =
    CEV_axiom_relative_staged_henkin_step \<Gamma> T (enum n)
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"

definition CEV_axiom_relative_staged_henkin_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> oterm set" where
  "CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum =
    (\<Union>n. CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"

lemma CEV_axiom_relative_staged_henkin_step_extends:
  "S \<subseteq> CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S"
  unfolding CEV_axiom_relative_staged_henkin_step_def
  by (cases spec) auto

lemma CEV_axiom_relative_staged_henkin_step_adds:
  assumes "spec = (\<sigma>, A)"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "henkin_witness_axiom
      (fresh_const_for_stage (T \<union> S) A) \<sigma> A
    \<in> CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S"
  using assms unfolding CEV_axiom_relative_staged_henkin_step_def by simp

lemma CEV_axiom_relative_staged_henkin_chain_step:
  "CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n \<subseteq>
    CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum (Suc n)"
  using CEV_axiom_relative_staged_henkin_step_extends[
    of "CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n"
      \<Gamma> T "enum n"]
  by simp

lemma CEV_axiom_relative_staged_henkin_chain_finite:
  assumes "finite S"
  shows "finite
    (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_axiom_relative_staged_henkin_step_finite)
qed

lemma CEV_axiom_relative_staged_henkin_chain_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_axiom_relative_staged_henkin_step_typed)
qed

lemma CEV_axiom_relative_staged_henkin_chain_consistent_finite_vocabulary:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have finite_n: "finite
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using Suc.prems(2)
    by (rule CEV_axiom_relative_staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma>
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using Suc.prems(3)
    by (rule CEV_axiom_relative_staged_henkin_chain_typed)
  have consistent_n: "CEV_axiom_relative_consistent \<Gamma> T
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1) finite_n typed_n consistent_n Suc.prems(5)
    by (simp add:
      CEV_axiom_relative_staged_henkin_step_consistent_finite_vocabulary)
qed

lemma CEV_axiom_relative_staged_henkin_chain_consistent:
  assumes finite_T: "finite T"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
proof -
  have finite_consts_T: "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  show ?thesis
    using finite_consts_T finite_S typed_S consistent closed
    by (rule
      CEV_axiom_relative_staged_henkin_chain_consistent_finite_vocabulary)
qed

lemma CEV_axiom_relative_staged_henkin_extension_extends:
  "S \<subseteq>
    CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum"
proof
  fix A
  assume "A \<in> S"
  then have "A \<in>
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum 0"
    by simp
  then show "A \<in>
      CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum"
    unfolding CEV_axiom_relative_staged_henkin_extension_def by blast
qed

lemma CEV_axiom_relative_staged_henkin_extension_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum)"
proof -
  have "\<And>n. typed_theory \<Gamma>
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using assms by (rule CEV_axiom_relative_staged_henkin_chain_typed)
  then show ?thesis
    unfolding CEV_axiom_relative_staged_henkin_extension_def
    by (rule typed_theory_nat_union)
qed

lemma CEV_axiom_relative_staged_henkin_extension_consistent_finite_vocabulary:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum)"
proof (unfold CEV_axiom_relative_consistent_def, intro notI)
  assume d_false:
    "\<Gamma> ; T ;
      CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub:
      "U \<subseteq>
        CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum"
    and d_U: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_false by (rule CEV_axiom_from_finite_support)
  have U_sub_union:
    "U \<subseteq> (\<Union>n.
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using U_sub
    unfolding CEV_axiom_relative_staged_henkin_extension_def .
  have step: "\<And>n.
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n \<subseteq>
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum (Suc n)"
    by (rule CEV_axiom_relative_staged_henkin_chain_step)
  obtain n where U_sub_chain:
    "U \<subseteq>
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have "\<Gamma> ; T ;
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_axiom_from_mono)
  moreover have "CEV_axiom_relative_consistent \<Gamma> T
      (CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n)"
    using assms
    by (rule
      CEV_axiom_relative_staged_henkin_chain_consistent_finite_vocabulary)
  ultimately show False
    unfolding CEV_axiom_relative_consistent_def by blast
qed

lemma CEV_axiom_relative_staged_henkin_extension_consistent:
  assumes finite_T: "finite T"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum)"
proof -
  have finite_consts_T: "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  show ?thesis
    using finite_consts_T finite_S typed_S consistent closed
    by (rule
      CEV_axiom_relative_staged_henkin_extension_consistent_finite_vocabulary)
qed

lemma CEV_axiom_relative_staged_henkin_extension_witness_axioms_available:
  assumes "enumerates_witness_bodies \<Gamma> enum"
  shows "Henkin_witness_axioms_available \<Gamma>
    (CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum)"
proof (unfold Henkin_witness_axioms_available_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = (\<sigma>, A)"
    using assms A_type unfolding enumerates_witness_bodies_def by blast
  let ?Sn =
    "CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum n"
  let ?c = "fresh_const_for_stage (T \<union> ?Sn) A"
  have ax_in_next:
    "henkin_witness_axiom ?c \<sigma> A \<in>
      CEV_axiom_relative_staged_henkin_chain \<Gamma> T S enum (Suc n)"
    using CEV_axiom_relative_staged_henkin_step_adds[
      OF enum_n A_type, of T ?Sn]
    by simp
  have "henkin_witness_axiom ?c \<sigma> A \<in>
      CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum"
    unfolding CEV_axiom_relative_staged_henkin_extension_def
    using ax_in_next by blast
  then show "\<exists>c. henkin_witness_axiom c \<sigma> A \<in>
      CEV_axiom_relative_staged_henkin_extension \<Gamma> T S enum"
    by blast
qed

subsection \<open>From relative maximality to an ordinary clean Henkin theory\<close>

lemma CEV_set_derivable_into_CEV_axiom_from:
  assumes "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A S \<Gamma>)
  then show ?case by (rule CEV_axiom_from.Assumption)
next
  case (Theorem \<Gamma> A S)
  then show ?case
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
next
  case (Derive_MP \<Gamma> S A B)
  show ?case
    using Derive_MP.IH(1) Derive_MP.IH(2)
    by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_relative_consistent_imp_CEV_consistent:
  assumes "CEV_axiom_relative_consistent \<Gamma> T S"
  shows "CEV_consistent \<Gamma> S"
proof (unfold CEV_consistent_def, intro notI)
  assume "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then have "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    by (rule CEV_set_derivable_into_CEV_axiom_from)
  then show False
    using assms unfolding CEV_axiom_relative_consistent_def by blast
qed

lemma CEV_axiom_relative_locally_maximal_imp_CEV_locally_maximal:
  assumes "CEV_axiom_relative_locally_maximal_consistent \<Gamma> T S"
  shows "CEV_locally_maximal_consistent \<Gamma> S"
proof -
  have typed: "typed_theory \<Gamma> S"
    and relative: "CEV_axiom_relative_consistent \<Gamma> T S"
    and complete: "CEV_negation_complete \<Gamma> S"
    using assms
    unfolding CEV_axiom_relative_locally_maximal_consistent_def by blast+
  have consistent: "CEV_consistent \<Gamma> S"
    using relative by (rule CEV_axiom_relative_consistent_imp_CEV_consistent)
  show ?thesis
    using typed consistent complete
    unfolding CEV_locally_maximal_consistent_def by blast
qed

theorem typed_CEV_axiom_stock_with_finite_vocabulary_has_clean_Henkin_extension:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and typed_T: "typed_theory [] T"
    and consistent_T: "CEV_axiom_consistent [] T"
  obtains U where
    "CEV_clean_Henkin_theory [] U"
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> U"
    "T \<subseteq> U"
proof -
  obtain body_enum where body_enum:
      "enumerates_witness_bodies [] body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?H =
    "CEV_axiom_relative_staged_henkin_extension [] T {} body_enum"
  have empty_relative: "CEV_axiom_relative_consistent [] T {}"
    using consistent_T
    unfolding CEV_axiom_consistent_iff_empty_relative_consistent .
  have closed_T: "CEV_closed_axiom_stock T"
    using typed_T by (rule typed_theory_empty_imp_CEV_closed_axiom_stock)
  have empty_typed: "typed_theory [] {}"
    unfolding typed_theory_def by simp
  have typed_H: "typed_theory [] ?H"
    using empty_typed
    by (rule CEV_axiom_relative_staged_henkin_extension_typed)
  have consistent_H: "CEV_axiom_relative_consistent [] T ?H"
    using finite_consts_T finite.emptyI empty_typed empty_relative closed_T
    by (rule
      CEV_axiom_relative_staged_henkin_extension_consistent_finite_vocabulary)
  have available_H: "Henkin_witness_axioms_available [] ?H"
    using body_enum
    by (rule
      CEV_axiom_relative_staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum:
      "enumerates_formulas [] formula_enum"
    using enumerates_formulas_exists by blast
  let ?U =
    "CEV_axiom_relative_lindenbaum_extension [] T ?H formula_enum"
  have H_sub_U: "?H \<subseteq> ?U"
    by (rule CEV_axiom_relative_lindenbaum_extension_extends)
  have relative_U:
      "CEV_axiom_relative_locally_maximal_consistent [] T ?U"
    using typed_H consistent_H formula_enum
    by (rule
      CEV_axiom_relative_lindenbaum_extension_locally_maximal_consistent)
  have local_U: "CEV_locally_maximal_consistent [] ?U"
    using relative_U
    by (rule CEV_axiom_relative_locally_maximal_imp_CEV_locally_maximal)
  have available_U: "Henkin_witness_axioms_available [] ?U"
    using available_H H_sub_U
    by (rule Henkin_witness_axioms_available_mono)
  have witnessed_U: "Henkin_witnessed [] ?U"
    using local_U available_U
    by (rule Henkin_witnessed_of_CEV_local_maximal_available_clean)
  have clean_U: "CEV_clean_Henkin_theory [] ?U"
    using local_U witnessed_U
    unfolding CEV_clean_Henkin_theory_def by blast
  have consequence_in:
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> ?U"
    using relative_U
    by (rule
      CEV_axiom_relative_locally_maximal_consistent_contains_theorems)
  have T_sub_U: "T \<subseteq> ?U"
  proof
    fix A
    assume A_in: "A \<in> T"
    have A_type: "[] \<turnstile> A : Prop"
      using typed_T A_in unfolding typed_theory_def by blast
    have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
      using A_in A_type by (rule CEV_axiom_proves.Axiom)
    then show "A \<in> ?U"
      by (rule consequence_in)
  qed
  show ?thesis
    using that clean_U consequence_in T_sub_U by blast
qed

corollary finite_typed_CEV_axiom_stock_has_clean_Henkin_extension:
  assumes finite_T: "finite T"
    and typed_T: "typed_theory [] T"
    and consistent_T: "CEV_axiom_consistent [] T"
  obtains U where
    "CEV_clean_Henkin_theory [] U"
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> U"
    "T \<subseteq> U"
proof -
  have finite_consts_T: "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  show ?thesis
    using finite_consts_T typed_T consistent_T that
    by (rule
      typed_CEV_axiom_stock_with_finite_vocabulary_has_clean_Henkin_extension)
qed

text \<open>
  The theorem is deliberately stated for closed added principles.  At the empty
  context this follows from their typing.  The restriction is what permits a
  fresh witness constant to be abstracted out without changing any of the
  added principles.
\<close>

end
