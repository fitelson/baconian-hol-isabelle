theory Bacon_PP_Fresh_CEVplus_Canonical_Semantics
  imports Bacon_PP_Fresh_Relative_Henkin_Completion
begin

section \<open>Canonical satisfaction for CEV with added principles\<close>

text \<open>
  The clean canonical construction presently represents a world by a maximal
  Henkin theory.  Satisfaction at that world is membership.  We therefore call
  a clean Henkin theory a CEV+ canonical world for \<open>T\<close> when it contains
  every consequence obtainable with \<open>T\<close> in the axiom position.
\<close>

definition CEV_axiom_clean_canonical_world ::
    "oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_axiom_clean_canonical_world T U \<longleftrightarrow>
    CEV_clean_Henkin_theory [] U \<and>
    (\<forall>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<longrightarrow> A \<in> U)"

definition CEV_axiom_canonical_truth ::
    "oterm set \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_axiom_canonical_truth T U A \<longleftrightarrow>
    CEV_axiom_clean_canonical_world T U \<and>
    [] \<turnstile> A : Prop \<and> A \<in> U"

definition CEV_axiom_clean_canonical_valid ::
    "oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_axiom_clean_canonical_valid T A \<longleftrightarrow>
    [] \<turnstile> A : Prop \<and>
    (\<forall>U. CEV_axiom_clean_canonical_world T U \<longrightarrow> A \<in> U)"

subsection \<open>Existence and relative completeness\<close>

theorem CEV_axiom_clean_canonical_world_extension:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and finite_S: "finite S"
    and typed_S: "typed_theory [] S"
    and consistent_S: "CEV_axiom_relative_consistent [] T S"
    and typed_T: "typed_theory [] T"
  obtains U where
    "CEV_axiom_clean_canonical_world T U"
    "S \<subseteq> U"
proof -
  obtain body_enum where body_enum:
      "enumerates_witness_bodies [] body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?H =
    "CEV_axiom_relative_staged_henkin_extension [] T S body_enum"
  have closed_T: "CEV_closed_axiom_stock T"
    using typed_T by (rule typed_theory_empty_imp_CEV_closed_axiom_stock)
  have S_sub_H: "S \<subseteq> ?H"
    by (rule CEV_axiom_relative_staged_henkin_extension_extends)
  have typed_H: "typed_theory [] ?H"
    using typed_S
    by (rule CEV_axiom_relative_staged_henkin_extension_typed)
  have consistent_H: "CEV_axiom_relative_consistent [] T ?H"
    using finite_consts_T finite_S typed_S consistent_S closed_T
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
  have world_U: "CEV_axiom_clean_canonical_world T ?U"
    using clean_U consequence_in
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have S_sub_U: "S \<subseteq> ?U"
    using S_sub_H H_sub_U by blast
  show ?thesis
    using that world_U S_sub_U by blast
qed

corollary typed_consistent_CEV_axiom_stock_with_finite_vocabulary_has_canonical_world:
  assumes "finite (consts_of_set T)"
    and "typed_theory [] T"
    and "CEV_axiom_consistent [] T"
  obtains U where
    "CEV_axiom_clean_canonical_world T U"
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      CEV_axiom_canonical_truth T U A"
    "\<And>A. A \<in> T \<Longrightarrow> CEV_axiom_canonical_truth T U A"
proof -
  have empty_typed: "typed_theory [] {}"
    unfolding typed_theory_def by simp
  have empty_relative: "CEV_axiom_relative_consistent [] T {}"
    using assms(3)
    unfolding CEV_axiom_consistent_iff_empty_relative_consistent .
  obtain U where world: "CEV_axiom_clean_canonical_world T U"
    using assms(1) finite.emptyI empty_typed empty_relative assms(2)
    by (rule CEV_axiom_clean_canonical_world_extension)
  have consequence_truth:
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      CEV_axiom_canonical_truth T U A"
  proof -
    fix A
    assume d_A: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    have A_type: "[] \<turnstile> A : Prop"
      using d_A by (rule CEV_axiom_proves_formula)
    have A_in: "A \<in> U"
      using world d_A
      unfolding CEV_axiom_clean_canonical_world_def by blast
    show "CEV_axiom_canonical_truth T U A"
      using world A_type A_in
      unfolding CEV_axiom_canonical_truth_def by blast
  qed
  have axiom_truth:
    "\<And>A. A \<in> T \<Longrightarrow> CEV_axiom_canonical_truth T U A"
  proof -
    fix A
    assume A_in: "A \<in> T"
    have A_type: "[] \<turnstile> A : Prop"
      using assms(2) A_in unfolding typed_theory_def by blast
    have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
      using A_in A_type by (rule CEV_axiom_proves.Axiom)
    then show "CEV_axiom_canonical_truth T U A"
      by (rule consequence_truth)
  qed
  show ?thesis
    using that world consequence_truth axiom_truth by blast
qed

corollary finite_typed_consistent_CEV_axiom_stock_has_canonical_world:
  assumes finite_T: "finite T"
    and typed_T: "typed_theory [] T"
    and consistent_T: "CEV_axiom_consistent [] T"
  obtains U where
    "CEV_axiom_clean_canonical_world T U"
    "\<And>A. [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      CEV_axiom_canonical_truth T U A"
    "\<And>A. A \<in> T \<Longrightarrow> CEV_axiom_canonical_truth T U A"
proof -
  have finite_consts_T: "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  show ?thesis
    using finite_consts_T typed_T consistent_T that
    by (rule
      typed_consistent_CEV_axiom_stock_with_finite_vocabulary_has_canonical_world)
qed

lemma CEV_axiom_relative_consistent_singleton_neg:
  assumes A_type: "[] \<turnstile> A : Prop"
    and not_proves: "\<not> [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "CEV_axiom_relative_consistent [] T {Neg A}"
proof (unfold CEV_axiom_relative_consistent_def, intro notI)
  assume d_false:
    "[] ; T ; {Neg A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  have neg_type: "[] \<turnstile> Neg A : Prop"
    using A_type by auto
  have d_imp_false:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule CEV_axiom_from_singleton_imp)
  have d_recover:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Imp (Neg A) ObjFalse) A"
    using CEV_proves_imp_neg_false_to_formula[OF A_type]
    by (rule CEV_axiom_proves.Base)
  have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    using d_imp_false d_recover by (rule CEV_axiom_proves.MP)
  then show False
    using not_proves by blast
qed

theorem CEV_axiom_clean_canonical_valid_iff_proves_finite_vocabulary:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and typed_T: "typed_theory [] T"
    and consistent_T: "CEV_axiom_consistent [] T"
  shows "CEV_axiom_clean_canonical_valid T A \<longleftrightarrow>
    [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof
  assume valid: "CEV_axiom_clean_canonical_valid T A"
  have A_type: "[] \<turnstile> A : Prop"
    using valid unfolding CEV_axiom_clean_canonical_valid_def by blast
  show "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  proof (rule ccontr)
    assume not_proves: "\<not> [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    have neg_typed: "typed_theory [] {Neg A}"
      using A_type unfolding typed_theory_def by auto
    have neg_consistent:
      "CEV_axiom_relative_consistent [] T {Neg A}"
      using A_type not_proves
      by (rule CEV_axiom_relative_consistent_singleton_neg)
    have finite_neg: "finite {Neg A}"
      by simp
    obtain U where world: "CEV_axiom_clean_canonical_world T U"
      and neg_in: "{Neg A} \<subseteq> U"
      using finite_consts_T finite_neg neg_typed neg_consistent typed_T
      by (rule CEV_axiom_clean_canonical_world_extension)
    have clean: "CEV_clean_Henkin_theory [] U"
      using world unfolding CEV_axiom_clean_canonical_world_def by blast
    have local: "CEV_locally_maximal_consistent [] U"
      using clean unfolding CEV_clean_Henkin_theory_def by blast
    have consistent: "CEV_consistent [] U"
      using local unfolding CEV_locally_maximal_consistent_def by blast
    have A_notin: "A \<notin> U"
    proof
      assume A_in: "A \<in> U"
      have d_A: "[] ; U \<turnstile>\<^sub>CEV\<^sub>s A"
        using A_in A_type by (rule CEV_set_derivable.Assumption)
      have neg_A_in: "Neg A \<in> U"
        using neg_in by simp
      have "[] ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
        using d_A neg_A_in
        by (rule CEV_set_derives_ObjFalse_of_formula_and_neg)
      then show False
        using consistent unfolding CEV_consistent_def by blast
    qed
    have "A \<in> U"
      using valid world
      unfolding CEV_axiom_clean_canonical_valid_def by blast
    then show False
      using A_notin by blast
  qed
next
  assume proves: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  have A_type: "[] \<turnstile> A : Prop"
    using proves by (rule CEV_axiom_proves_formula)
  have all_worlds:
    "\<And>U. CEV_axiom_clean_canonical_world T U \<Longrightarrow> A \<in> U"
    using proves unfolding CEV_axiom_clean_canonical_world_def by blast
  show "CEV_axiom_clean_canonical_valid T A"
    using A_type all_worlds
    unfolding CEV_axiom_clean_canonical_valid_def by blast
qed

corollary CEV_axiom_clean_canonical_valid_iff_proves:
  assumes finite_T: "finite T"
    and typed_T: "typed_theory [] T"
    and consistent_T: "CEV_axiom_consistent [] T"
  shows "CEV_axiom_clean_canonical_valid T A \<longleftrightarrow>
    [] ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof -
  have finite_consts_T: "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  show ?thesis
    using finite_consts_T typed_T consistent_T
    by (rule
      CEV_axiom_clean_canonical_valid_iff_proves_finite_vocabulary)
qed

subsection \<open>Truth clauses at the canonical world\<close>

lemma C_derivable_into_CEV_set_derivable:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and "set \<Delta> \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by (intro CEV_set_derivable.Assumption) blast+
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by (intro CEV_set_derivable.Theorem CEV_proves.CE CE_proves.C)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  show ?case
    using Derive_MP.IH(1)[OF Derive_MP.prems]
      Derive_MP.IH(2)[OF Derive_MP.prems]
    by (rule CEV_set_derivable.Derive_MP)
qed

lemma C_set_derivable_into_CEV_set_derivable:
  assumes "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
proof -
  obtain \<Delta> where derivation: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and support: "set \<Delta> \<subseteq> U"
    using assms unfolding C_set_derivable_def by blast
  show ?thesis
    using derivation support by (rule C_derivable_into_CEV_set_derivable)
qed

lemma CEV_consistent_imp_C_consistent:
  assumes "CEV_consistent \<Gamma> U"
  shows "C_consistent \<Gamma> U"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  then have "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    by (rule C_set_derivable_into_CEV_set_derivable)
  then show False
    using assms unfolding CEV_consistent_def by blast
qed

lemma CEV_clean_Henkin_imp_C_Henkin:
  assumes "CEV_clean_Henkin_theory \<Gamma> U"
  shows "C_Henkin_theory \<Gamma> U"
proof -
  have local: "CEV_locally_maximal_consistent \<Gamma> U"
    and witnessed: "Henkin_witnessed \<Gamma> U"
    using assms unfolding CEV_clean_Henkin_theory_def by blast+
  have typed: "typed_theory \<Gamma> U"
    and cev_consistent: "CEV_consistent \<Gamma> U"
    and cev_complete: "CEV_negation_complete \<Gamma> U"
    using local unfolding CEV_locally_maximal_consistent_def by blast+
  have c_consistent: "C_consistent \<Gamma> U"
    using cev_consistent by (rule CEV_consistent_imp_C_consistent)
  have c_complete: "C_negation_complete \<Gamma> U"
    using cev_complete
    unfolding CEV_negation_complete_def C_negation_complete_def .
  have c_maximal: "C_maximal_consistent \<Gamma> U"
    using typed c_consistent c_complete
    unfolding C_maximal_consistent_def by blast
  show ?thesis
    using c_maximal witnessed unfolding C_Henkin_theory_def by blast
qed

lemma CEV_axiom_canonical_truth_iff_C_truth:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
  shows "CEV_axiom_canonical_truth T U A \<longleftrightarrow>
    C_canonical_truth [] U A"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  show ?thesis
    using world A_type c_henkin
    unfolding CEV_axiom_canonical_truth_def C_canonical_truth_def by blast
qed

lemma CEV_axiom_canonical_truth_neg_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
  shows "CEV_axiom_canonical_truth T U (Neg A) \<longleftrightarrow>
    \<not> CEV_axiom_canonical_truth T U A"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  show ?thesis
    using C_canonical_truth_neg_iff[OF c_henkin A_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world A_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world, of "Neg A"]
      A_type
    by auto
qed

lemma CEV_axiom_canonical_truth_imp_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
    and B_type: "[] \<turnstile> B : Prop"
  shows "CEV_axiom_canonical_truth T U (Imp A B) \<longleftrightarrow>
    (CEV_axiom_canonical_truth T U A \<longrightarrow>
      CEV_axiom_canonical_truth T U B)"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  show ?thesis
    using C_canonical_truth_imp_iff[OF c_henkin A_type B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world A_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world, of "Imp A B"]
      A_type B_type
    by auto
qed

lemma CEV_axiom_canonical_truth_conj_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
    and B_type: "[] \<turnstile> B : Prop"
  shows "CEV_axiom_canonical_truth T U (Conj A B) \<longleftrightarrow>
    CEV_axiom_canonical_truth T U A \<and>
    CEV_axiom_canonical_truth T U B"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  show ?thesis
    using C_canonical_truth_conj_iff[OF c_henkin A_type B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world A_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world, of "Conj A B"]
      A_type B_type
    by auto
qed

lemma CEV_axiom_canonical_truth_disj_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
    and B_type: "[] \<turnstile> B : Prop"
  shows "CEV_axiom_canonical_truth T U (Disj A B) \<longleftrightarrow>
    CEV_axiom_canonical_truth T U A \<or>
    CEV_axiom_canonical_truth T U B"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  show ?thesis
    using C_canonical_truth_disj_iff[OF c_henkin A_type B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world A_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world B_type]
      CEV_axiom_canonical_truth_iff_C_truth[OF world, of "Disj A B"]
      A_type B_type
    by auto
qed

lemma CEV_axiom_canonical_truth_forall_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  shows "CEV_axiom_canonical_truth T U (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow>
      CEV_axiom_canonical_truth T U (subst0 W A))"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have clause:
    "Forall \<sigma> A \<in> U \<longleftrightarrow>
      (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> U)"
    using c_henkin A_type by (rule C_Henkin_forall_mem_iff)
  show ?thesis
    unfolding CEV_axiom_canonical_truth_def
    using world A_type clause subst0_preserves_typing by auto
qed

lemma CEV_axiom_canonical_truth_exists_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  shows "CEV_axiom_canonical_truth T U (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. [] \<turnstile> W : \<sigma> \<and>
      CEV_axiom_canonical_truth T U (subst0 W A))"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have clause:
    "Exists \<sigma> A \<in> U \<longleftrightarrow>
      (\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U)"
    using c_henkin A_type by (rule C_Henkin_exists_mem_iff)
  show ?thesis
    unfolding CEV_axiom_canonical_truth_def
    using world A_type clause subst0_preserves_typing by auto
qed

lemma CEV_axiom_canonical_truth_equality_refl:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and M_type: "[] \<turnstile> M : \<sigma>"
  shows "CEV_axiom_canonical_truth T U (Eq \<sigma> M M)"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have "C_canonical_truth [] U (Eq \<sigma> M M)"
    using c_henkin M_type by (rule C_canonical_truth_refl)
  then show ?thesis
    using world c_henkin M_type
    unfolding CEV_axiom_canonical_truth_def C_canonical_truth_def by auto
qed

lemma CEV_axiom_canonical_truth_equality_subst:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and eq_truth: "CEV_axiom_canonical_truth T U (Eq \<sigma> M N)"
    and app_truth: "CEV_axiom_canonical_truth T U (App F M)"
    and M_type: "[] \<turnstile> M : \<sigma>"
    and N_type: "[] \<turnstile> N : \<sigma>"
    and F_type: "[] \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "CEV_axiom_canonical_truth T U (App F N)"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have eq_c: "C_canonical_truth [] U (Eq \<sigma> M N)"
    using eq_truth c_henkin
    unfolding CEV_axiom_canonical_truth_def C_canonical_truth_def by blast
  have app_c: "C_canonical_truth [] U (App F M)"
    using app_truth c_henkin
    unfolding CEV_axiom_canonical_truth_def C_canonical_truth_def by blast
  have result: "C_canonical_truth [] U (App F N)"
    using c_henkin eq_c app_c M_type N_type F_type
    by (rule C_canonical_truth_leibniz)
  show ?thesis
    using result world
    unfolding CEV_axiom_canonical_truth_def C_canonical_truth_def by blast
qed

lemma CEV_axiom_canonical_truth_beta_eta_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and equiv: "beta_eta_equiv [] Prop A B"
  shows "CEV_axiom_canonical_truth T U A \<longleftrightarrow>
    CEV_axiom_canonical_truth T U B"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using world CEV_clean_Henkin_imp_C_Henkin
    unfolding CEV_axiom_clean_canonical_world_def by blast
  have clause:
    "C_canonical_truth [] U A \<longleftrightarrow> C_canonical_truth [] U B"
    using c_henkin equiv by (rule C_canonical_truth_beta_eta_iff)
  have A_type: "[] \<turnstile> A : Prop"
    using equiv by (rule beta_eta_equiv_left_type)
  have B_type: "[] \<turnstile> B : Prop"
    using equiv by (rule beta_eta_equiv_right_type)
  have mem_clause: "A \<in> U \<longleftrightarrow> B \<in> U"
    using clause c_henkin A_type B_type
    unfolding C_canonical_truth_def by simp
  show ?thesis
    unfolding CEV_axiom_canonical_truth_def
    using world mem_clause A_type B_type by blast
qed

subsection \<open>The vocabulary of Goodman's axiom stocks\<close>

text \<open>
  Goodman's stocks are infinite because the Purity and application principles
  are schemas over types and terms.  Their nonlogical vocabulary is nonetheless
  finite: every instance uses only \<open>Pure\<close> and \<open>Fun\<close>.  This is exactly the
  hypothesis used by the strengthened fresh-witness construction above.
\<close>

lemma pp_purity_schema_finite_vocabulary:
  assumes "A \<in> pp_purity_schema"
  shows "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
  using assms
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
    pp_pure_def pp_Pure_def
  by auto

lemma pp_application_closure_schema_finite_vocabulary:
  assumes "A \<in> pp_application_closure_schema"
  shows "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
  using assms
  unfolding pp_application_closure_schema_def pp_application_closure_def
    pp_pure_def pp_Pure_def
  by auto

lemma pp_no_other_fundamentals_schema_finite_vocabulary:
  assumes "A \<in> pp_no_other_fundamentals_schema"
  shows "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
  using assms
  unfolding pp_no_other_fundamentals_schema_def pp_no_fundamentals_def
    pp_fun_def pp_Fun_def
  by auto

lemma pp_persistence_schema_finite_vocabulary:
  assumes "A \<in> pp_persistence_schema"
  shows "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
  using assms
  unfolding pp_persistence_schema_def pp_persistence_def
    pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def
  by auto

lemma pp_recombination_PP_axioms_vocabulary_subset:
  "consts_of_set pp_recombination_PP_axioms
    \<subseteq> {pp_pure_name, pp_fun_name}"
proof
  fix c
  assume "c \<in> consts_of_set pp_recombination_PP_axioms"
  then obtain A where A_in: "A \<in> pp_recombination_PP_axioms"
    and c_in: "c \<in> consts_of A"
    by (rule consts_of_setD)
  have "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
    using A_in pp_purity_schema_finite_vocabulary
      pp_application_closure_schema_finite_vocabulary
      pp_no_other_fundamentals_schema_finite_vocabulary
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
      pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def
      pp_unique_fundamental_def pp_fun_def pp_Fun_def
      pp_zeroary_recombination_def pp_unary_recombination_def
      ObjBox_def ObjTrue_def
    by auto
  then show "c \<in> {pp_pure_name, pp_fun_name}"
    using c_in by blast
qed

theorem pp_recombination_PP_axioms_has_finite_vocabulary:
  "finite (consts_of_set pp_recombination_PP_axioms)"
  using pp_recombination_PP_axioms_vocabulary_subset
  by (rule finite_subset) simp

lemma pp_full_QLN_PP_persistence_axioms_vocabulary_subset:
  "consts_of_set pp_full_QLN_PP_persistence_axioms
    \<subseteq> {pp_pure_name, pp_fun_name}"
proof
  fix c
  assume "c \<in> consts_of_set pp_full_QLN_PP_persistence_axioms"
  then obtain A where A_in: "A \<in> pp_full_QLN_PP_persistence_axioms"
    and c_in: "c \<in> consts_of A"
    by (rule consts_of_setD)
  have "consts_of A \<subseteq> {pp_pure_name, pp_fun_name}"
  proof (cases "A \<in> pp_persistence_schema")
    case True
    then show ?thesis
      by (rule pp_persistence_schema_finite_vocabulary)
  next
    case False
    have A_main: "A \<in> pp_full_QLN_PP_axioms"
      using A_in False
      unfolding pp_full_QLN_PP_persistence_axioms_def by blast
    show ?thesis
      using A_main pp_purity_schema_finite_vocabulary
        pp_application_closure_schema_finite_vocabulary
        pp_no_other_fundamentals_schema_finite_vocabulary
      unfolding pp_full_QLN_PP_axioms_def pp_full_QLN_background_axioms_def
        pp_recombination_background_axioms_def pp_exhaustion_axioms_def
        pp_background_axioms_def
        pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def
        pp_unique_fundamental_def pp_fun_def pp_Fun_def
        pp_zeroary_recombination_def pp_unary_recombination_def
        pp_zeroary_exhaustion_def pp_unary_exhaustion_def
        ObjBox_def ObjTrue_def
      by auto
  qed
  then show "c \<in> {pp_pure_name, pp_fun_name}"
    using c_in by blast
qed

theorem pp_full_QLN_PP_persistence_axioms_has_finite_vocabulary:
  "finite (consts_of_set pp_full_QLN_PP_persistence_axioms)"
  using pp_full_QLN_PP_persistence_axioms_vocabulary_subset
  by (rule finite_subset) simp

text \<open>
  These are exact truth clauses for the syntactic canonical semantics:
  Boolean operations and quantifiers have their intended clauses over closed
  terms, identity is reflexive and Leibnizian, and beta-eta conversion
  preserves truth.  The foundational clean development does not package the
  term quotients as an instance of the abstract applicative-structure locale.
  Consequently this theorem is not yet the existence of a set-theoretic
  applicative or action model; that requires explicit quotient domains,
  application, abstraction, and a truth lemma connecting evaluation with the
  membership relation proved here.
\<close>

end
