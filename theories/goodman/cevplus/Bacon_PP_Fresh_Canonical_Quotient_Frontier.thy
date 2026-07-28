theory Bacon_PP_Fresh_Canonical_Quotient_Frontier
  imports Bacon_PP_Fresh_CEVplus_Canonical_Semantics
    Bacon_Classicism.Bacon_Intended_Quotient
begin

section \<open>The local quotient at a CEV+ canonical world\<close>

text \<open>
  The intended-quotient development already supplies equivalence classes,
  application on those classes, and a well-defined truth predicate for
  propositions.  We collect the exact consequences needed from the CEV+
  canonical world constructed above.
\<close>

lemma CEV_local_domain_nonempty:
  "CEV_local_domain \<Gamma> U \<sigma> \<noteq> {}"
proof -
  have type: "\<Gamma> \<turnstile> Const ''canonical'' \<sigma> : \<sigma>"
    by (rule has_type.Const)
  have "CEV_local_term_class \<Gamma> U \<sigma> (Const ''canonical'' \<sigma>)
      \<in> CEV_local_domain \<Gamma> U \<sigma>"
    using type by (rule CEV_local_domainI)
  then show ?thesis
    by blast
qed

lemma CEV_local_constant_in_domain:
  "CEV_local_term_class \<Gamma> U \<sigma> (Const c \<sigma>)
    \<in> CEV_local_domain \<Gamma> U \<sigma>"
  by (rule CEV_local_domainI) auto

theorem CEV_axiom_canonical_quotient_basic_operations:
  assumes world: "CEV_axiom_clean_canonical_world T U"
  shows
    "CEV_local_domain [] U \<sigma> \<noteq> {}"
    "CEV_local_term_class [] U \<sigma> (Const c \<sigma>)
      \<in> CEV_local_domain [] U \<sigma>"
    "\<And>X Y. X \<in> CEV_local_domain [] U (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow>
      Y \<in> CEV_local_domain [] U \<sigma> \<Longrightarrow>
      CEV_local_app [] U \<sigma> \<tau> X Y
        \<in> CEV_local_domain [] U \<tau>"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  show "CEV_local_domain [] U \<sigma> \<noteq> {}"
    by (rule CEV_local_domain_nonempty)
  show "CEV_local_term_class [] U \<sigma> (Const c \<sigma>)
      \<in> CEV_local_domain [] U \<sigma>"
    by (rule CEV_local_constant_in_domain)
  fix X Y
  assume X_dom: "X \<in> CEV_local_domain [] U (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and Y_dom: "Y \<in> CEV_local_domain [] U \<sigma>"
  show "CEV_local_app [] U \<sigma> \<tau> X Y
      \<in> CEV_local_domain [] U \<tau>"
    using clean X_dom Y_dom by (rule CEV_local_app_closed)
qed

theorem CEV_axiom_canonical_closed_truth_lemma:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and A_type: "[] \<turnstile> A : Prop"
  shows "CEV_local_holds [] U
      (CEV_local_term_class [] U Prop A)
    \<longleftrightarrow> CEV_axiom_canonical_truth T U A"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have quotient:
    "CEV_local_holds [] U (CEV_local_term_class [] U Prop A)
      \<longleftrightarrow> A \<in> U"
    using clean A_type by (rule CEV_local_holds_class_iff)
  show ?thesis
    using world A_type quotient
    unfolding CEV_axiom_canonical_truth_def by blast
qed

subsection \<open>Boolean operations on quotient propositions\<close>

lemma CEV_local_holds_neg_iff:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "[] \<turnstile> A : Prop"
  shows "CEV_local_holds [] U
      (CEV_local_term_class [] U Prop (Neg A))
    \<longleftrightarrow>
    \<not> CEV_local_holds [] U
      (CEV_local_term_class [] U Prop A)"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  have neg_type: "[] \<turnstile> Neg A : Prop"
    using A_type by auto
  have neg_clause: "Neg A \<in> U \<longleftrightarrow> A \<notin> U"
    using c_henkin A_type by (rule C_Henkin_neg_mem_iff)
  have holds_A:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop A) \<longleftrightarrow> A \<in> U"
    using clean A_type by (rule CEV_local_holds_class_iff)
  have holds_neg:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop (Neg A)) \<longleftrightarrow>
        Neg A \<in> U"
    using clean neg_type by (rule CEV_local_holds_class_iff)
  show ?thesis
    using holds_A holds_neg neg_clause by blast
qed

lemma CEV_local_holds_imp_iff:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "[] \<turnstile> A : Prop"
    and B_type: "[] \<turnstile> B : Prop"
  shows "CEV_local_holds [] U
      (CEV_local_term_class [] U Prop (Imp A B))
    \<longleftrightarrow>
    (CEV_local_holds [] U (CEV_local_term_class [] U Prop A)
      \<longrightarrow>
     CEV_local_holds [] U (CEV_local_term_class [] U Prop B))"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  have imp_type: "[] \<turnstile> Imp A B : Prop"
    using A_type B_type by auto
  have imp_clause:
      "Imp A B \<in> U \<longleftrightarrow> (A \<in> U \<longrightarrow> B \<in> U)"
    using c_henkin A_type B_type by (rule C_Henkin_imp_mem_iff)
  have holds_A:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop A) \<longleftrightarrow> A \<in> U"
    using clean A_type by (rule CEV_local_holds_class_iff)
  have holds_B:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop B) \<longleftrightarrow> B \<in> U"
    using clean B_type by (rule CEV_local_holds_class_iff)
  have holds_imp:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop (Imp A B)) \<longleftrightarrow>
        Imp A B \<in> U"
    using clean imp_type by (rule CEV_local_holds_class_iff)
  show ?thesis
    using holds_A holds_B holds_imp imp_clause by blast
qed

subsection \<open>Term-denotable abstraction at propositional result type\<close>

lemma CEV_local_prop_beta_equiv:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
    and W_type: "[] \<turnstile> W : \<sigma>"
  shows "CEV_local_term_equiv [] U Prop
    (App (Lam \<sigma> A) W) (subst0 W A)"
proof -
  have app_type: "[] \<turnstile> App (Lam \<sigma> A) W : Prop"
    using A_type W_type by auto
  have subst_type: "[] \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  have beta_step:
      "compatible_step beta_contract
        (App (Lam \<sigma> A) W) (subst0 W A)"
    by (intro compatible_step.root beta_contract.beta)
  have bicond:
      "[] \<turnstile>\<^sub>H
        (App (Lam \<sigma> A) W \<longleftrightarrow>\<^sub>o subst0 W A)"
    using app_type subst_type beta_step by (rule H_proves.Beta)
  have identity:
      "[] \<turnstile>\<^sub>CEV
        Eq Prop (App (Lam \<sigma> A) W) (subst0 W A)"
    using app_type subst_type bicond
    by (intro CEV_proves.CE CE_proves.PropEquivalence
        CE_proves.C C_proves.H)
  have identity_in:
      "Eq Prop (App (Lam \<sigma> A) W) (subst0 W A) \<in> U"
    using clean identity by (rule CEV_clean_Henkin_contains_theorems)
  show ?thesis
    using app_type subst_type identity_in
    unfolding CEV_local_term_equiv_def by blast
qed

lemma CEV_local_prop_beta_class:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
    and W_type: "[] \<turnstile> W : \<sigma>"
  shows "CEV_local_app [] U \<sigma> Prop
      (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A))
      (CEV_local_term_class [] U \<sigma> W)
    = CEV_local_term_class [] U Prop (subst0 W A)"
proof -
  have lam_type: "[] \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o Prop"
    using A_type by auto
  have app_type: "[] \<turnstile> App (Lam \<sigma> A) W : Prop"
    using lam_type W_type by auto
  have subst_type: "[] \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  have app_class:
      "CEV_local_app [] U \<sigma> Prop
        (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A))
        (CEV_local_term_class [] U \<sigma> W)
       = CEV_local_term_class [] U Prop (App (Lam \<sigma> A) W)"
    using clean lam_type W_type by (rule CEV_local_app_class)
  have beta_equiv:
      "CEV_local_term_equiv [] U Prop
        (App (Lam \<sigma> A) W) (subst0 W A)"
    using clean A_type W_type by (rule CEV_local_prop_beta_equiv)
  have class_eq:
      "CEV_local_term_class [] U Prop (App (Lam \<sigma> A) W) =
        CEV_local_term_class [] U Prop (subst0 W A)"
    using CEV_local_term_class_eq[
      OF clean app_type subst_type] beta_equiv by blast
  show ?thesis
    using app_class class_eq by simp
qed

lemma CEV_local_body_application_holds_iff:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
    and W_type: "[] \<turnstile> W : \<sigma>"
  shows "CEV_local_holds [] U
      (CEV_local_app [] U \<sigma> Prop
        (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A))
        (CEV_local_term_class [] U \<sigma> W))
    \<longleftrightarrow> subst0 W A \<in> U"
  using CEV_local_prop_beta_class[OF assms]
    CEV_local_holds_class_iff[OF clean
      subst0_preserves_typing[OF A_type W_type]]
  by simp

lemma CEV_local_holds_forall_iff:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  shows "CEV_local_holds [] U
      (CEV_local_term_class [] U Prop (Forall \<sigma> A))
    \<longleftrightarrow>
    (\<forall>X \<in> CEV_local_domain [] U \<sigma>.
      CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X))"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  have forall_mem:
      "Forall \<sigma> A \<in> U \<longleftrightarrow>
        (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> U)"
    using c_henkin A_type by (rule C_Henkin_forall_mem_iff)
  have quotient_forall:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop (Forall \<sigma> A))
       \<longleftrightarrow> Forall \<sigma> A \<in> U"
  proof -
    have forall_type: "[] \<turnstile> Forall \<sigma> A : Prop"
      using A_type by auto
    show ?thesis
      using clean forall_type by (rule CEV_local_holds_class_iff)
  qed
  have domain_clause:
      "(\<forall>X \<in> CEV_local_domain [] U \<sigma>.
        CEV_local_holds [] U
          (CEV_local_app [] U \<sigma> Prop
            (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
              (Lam \<sigma> A)) X))
       \<longleftrightarrow>
       (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> U)"
  proof
    assume all_X:
      "\<forall>X \<in> CEV_local_domain [] U \<sigma>.
        CEV_local_holds [] U
          (CEV_local_app [] U \<sigma> Prop
            (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
              (Lam \<sigma> A)) X)"
    show "\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> U"
    proof (intro allI impI)
      fix W
      assume W_type: "[] \<turnstile> W : \<sigma>"
      have class_dom:
          "CEV_local_term_class [] U \<sigma> W
            \<in> CEV_local_domain [] U \<sigma>"
        using W_type by (rule CEV_local_domainI)
      have holds:
        "CEV_local_holds [] U
          (CEV_local_app [] U \<sigma> Prop
            (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
              (Lam \<sigma> A))
            (CEV_local_term_class [] U \<sigma> W))"
        using all_X class_dom by blast
      show "subst0 W A \<in> U"
        using holds
          CEV_local_body_application_holds_iff[OF clean A_type W_type]
        by blast
    qed
  next
    assume all_W:
      "\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> U"
    show "\<forall>X \<in> CEV_local_domain [] U \<sigma>.
      CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X)"
    proof (intro ballI)
      fix X
      assume X_dom: "X \<in> CEV_local_domain [] U \<sigma>"
      obtain W where W_type: "[] \<turnstile> W : \<sigma>"
        and X_def: "X = CEV_local_term_class [] U \<sigma> W"
        using X_dom unfolding CEV_local_domain_def by blast
      have subst_in: "subst0 W A \<in> U"
        using all_W W_type by blast
      show "CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X)"
        unfolding X_def
        using subst_in
          CEV_local_body_application_holds_iff[OF clean A_type W_type]
        by blast
    qed
  qed
  show ?thesis
    using quotient_forall forall_mem domain_clause by blast
qed

lemma CEV_local_holds_exists_iff:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  shows "CEV_local_holds [] U
      (CEV_local_term_class [] U Prop (Exists \<sigma> A))
    \<longleftrightarrow>
    (\<exists>X \<in> CEV_local_domain [] U \<sigma>.
      CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X))"
proof -
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  have exists_mem:
      "Exists \<sigma> A \<in> U \<longleftrightarrow>
        (\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U)"
    using c_henkin A_type by (rule C_Henkin_exists_mem_iff)
  have quotient_exists:
      "CEV_local_holds [] U
        (CEV_local_term_class [] U Prop (Exists \<sigma> A))
       \<longleftrightarrow> Exists \<sigma> A \<in> U"
  proof -
    have exists_type: "[] \<turnstile> Exists \<sigma> A : Prop"
      using A_type by auto
    show ?thesis
      using clean exists_type by (rule CEV_local_holds_class_iff)
  qed
  have domain_clause:
      "(\<exists>X \<in> CEV_local_domain [] U \<sigma>.
        CEV_local_holds [] U
          (CEV_local_app [] U \<sigma> Prop
            (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
              (Lam \<sigma> A)) X))
       \<longleftrightarrow>
       (\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U)"
  proof
    assume "\<exists>X \<in> CEV_local_domain [] U \<sigma>.
      CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X)"
    then obtain X where X_dom: "X \<in> CEV_local_domain [] U \<sigma>"
      and holds:
        "CEV_local_holds [] U
          (CEV_local_app [] U \<sigma> Prop
            (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
              (Lam \<sigma> A)) X)"
      by blast
    obtain W where W_type: "[] \<turnstile> W : \<sigma>"
      and X_def: "X = CEV_local_term_class [] U \<sigma> W"
      using X_dom unfolding CEV_local_domain_def by blast
    have subst_in: "subst0 W A \<in> U"
      using holds
        CEV_local_body_application_holds_iff[OF clean A_type W_type]
      unfolding X_def by blast
    show "\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U"
      using W_type subst_in by blast
  next
    assume "\<exists>W. [] \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U"
    then obtain W where W_type: "[] \<turnstile> W : \<sigma>"
      and subst_in: "subst0 W A \<in> U"
      by blast
    have class_dom:
        "CEV_local_term_class [] U \<sigma> W
          \<in> CEV_local_domain [] U \<sigma>"
      using W_type by (rule CEV_local_domainI)
    have holds:
      "CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A))
          (CEV_local_term_class [] U \<sigma> W))"
      using subst_in
        CEV_local_body_application_holds_iff[OF clean A_type W_type]
      by blast
    show "\<exists>X \<in> CEV_local_domain [] U \<sigma>.
      CEV_local_holds [] U
        (CEV_local_app [] U \<sigma> Prop
          (CEV_local_term_class [] U (\<sigma> \<rightarrow>\<^sub>o Prop)
            (Lam \<sigma> A)) X)"
      using class_dom holds by blast
  qed
  show ?thesis
    using quotient_exists exists_mem domain_clause by blast
qed

section \<open>Open formulas under typed substitutions\<close>

text \<open>
  The canonical development already contains the open-formula induction at
  the level of term representatives.  The following consequences record that
  it applies without change at each CEV+ canonical world.
\<close>

lemma CEV_axiom_canonical_substitution_neg_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and s_typed: "term_subst_typed \<Delta> [] s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> [] U s (Neg A) \<longleftrightarrow>
    \<not> C_subst_truth \<Delta> [] U s A"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  show ?thesis
    using c_henkin s_typed A_type by (rule C_subst_truth_neg_iff)
qed

lemma CEV_axiom_canonical_substitution_imp_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and s_typed: "term_subst_typed \<Delta> [] s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "C_subst_truth \<Delta> [] U s (Imp A B) \<longleftrightarrow>
    (C_subst_truth \<Delta> [] U s A \<longrightarrow>
      C_subst_truth \<Delta> [] U s B)"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  show ?thesis
    using c_henkin s_typed A_type B_type
    by (rule C_subst_truth_imp_iff)
qed

lemma CEV_axiom_canonical_substitution_forall_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and s_typed: "term_subst_typed \<Delta> [] s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> [] U s (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. [] \<turnstile> W : \<sigma> \<longrightarrow>
      C_subst_truth (\<sigma> # \<Delta>) [] U (case_nat W s) A)"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  show ?thesis
    using c_henkin s_typed A_type
    by (rule C_subst_truth_forall_iff)
qed

lemma CEV_axiom_canonical_substitution_exists_iff:
  assumes world: "CEV_axiom_clean_canonical_world T U"
    and s_typed: "term_subst_typed \<Delta> [] s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> [] U s (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. [] \<turnstile> W : \<sigma> \<and>
      C_subst_truth (\<sigma> # \<Delta>) [] U (case_nat W s) A)"
proof -
  have clean: "CEV_clean_Henkin_theory [] U"
    using world unfolding CEV_axiom_clean_canonical_world_def by blast
  have c_henkin: "C_Henkin_theory [] U"
    using clean by (rule CEV_clean_Henkin_imp_C_Henkin)
  show ?thesis
    using c_henkin s_typed A_type
    by (rule C_subst_truth_exists_iff)
qed

section \<open>The exact remaining abstraction obligations\<close>

definition CEV_local_beta_complete ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_local_beta_complete \<Gamma> U \<longleftrightarrow>
    (\<forall>\<sigma> \<tau> A W.
      \<sigma> # \<Gamma> \<turnstile> A : \<tau> \<longrightarrow> \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow>
      CEV_local_term_class \<Gamma> U \<tau> (App (Lam \<sigma> A) W) =
        CEV_local_term_class \<Gamma> U \<tau> (subst0 W A))"

definition CEV_local_function_extensional ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_local_function_extensional \<Gamma> U \<longleftrightarrow>
    (\<forall>\<sigma> \<tau> F G.
      \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<longrightarrow>
      \<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau> \<longrightarrow>
      (\<forall>X \<in> CEV_local_domain \<Gamma> U \<sigma>.
        CEV_local_app \<Gamma> U \<sigma> \<tau>
          (CEV_local_term_class \<Gamma> U (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) X =
        CEV_local_app \<Gamma> U \<sigma> \<tau>
          (CEV_local_term_class \<Gamma> U (\<sigma> \<rightarrow>\<^sub>o \<tau>) G) X)
      \<longrightarrow>
      CEV_local_term_class \<Gamma> U (\<sigma> \<rightarrow>\<^sub>o \<tau>) F =
        CEV_local_term_class \<Gamma> U (\<sigma> \<rightarrow>\<^sub>o \<tau>) G)"

definition CEV_local_full_abstraction ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_local_full_abstraction \<Gamma> U \<longleftrightarrow>
    (\<forall>\<sigma> \<tau> f.
      (\<forall>X \<in> CEV_local_domain \<Gamma> U \<sigma>.
        f X \<in> CEV_local_domain \<Gamma> U \<tau>)
      \<longrightarrow>
      (\<exists>F. \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<and>
        (\<forall>X \<in> CEV_local_domain \<Gamma> U \<sigma>.
          CEV_local_app \<Gamma> U \<sigma> \<tau>
            (CEV_local_term_class \<Gamma> U (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) X =
          f X)))"

lemma CEV_local_beta_complete_prop:
  assumes clean: "CEV_clean_Henkin_theory [] U"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
    and W_type: "[] \<turnstile> W : \<sigma>"
  shows "CEV_local_term_class [] U Prop (App (Lam \<sigma> A) W) =
    CEV_local_term_class [] U Prop (subst0 W A)"
proof -
  have app_type: "[] \<turnstile> App (Lam \<sigma> A) W : Prop"
    using A_type W_type by auto
  have subst_type: "[] \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  have equiv: "CEV_local_term_equiv [] U Prop
      (App (Lam \<sigma> A) W) (subst0 W A)"
    using clean A_type W_type by (rule CEV_local_prop_beta_equiv)
  show ?thesis
    using CEV_local_term_class_eq[OF clean app_type subst_type] equiv
    by blast
qed

text \<open>
  The quotient therefore supplies nonempty type domains, constants,
  well-defined application, the closed truth lemma, and the full Boolean and
  quantifier clauses at propositional result type.  Two different semantic
  interfaces stop at different precise points.

  The original \<open>applicative_structure\<close> asks for an abstraction denotation
  for every meta-level function between domains.  This is exactly
  \<open>CEV_local_full_abstraction\<close>, together with
  \<open>CEV_local_function_extensional\<close> for congruence.  Neither follows from
  Henkin witnesses: the local domains contain only term-denotable operations.
  Moreover, \<open>CEV_local_beta_complete\<close> is presently proved above only when
  the result type is \<open>Prop\<close>, because the certified beta rule is a rule for
  proposition-level biconditionals.

  The foundational canonical development already proves the Boolean,
  quantifier, identity, and conversion clauses for \<open>C_subst_truth\<close> under an
  arbitrary typed substitution of terms for the free variables.  Thus the
  remaining step toward the denotable-function action-model interface is more
  specific: convert an environment of quotient classes to a typed substitution
  by choosing representatives, prove that the resulting denotation and truth
  value do not depend on those choices, and package the resulting typed
  evaluator as the interface's single untyped \<open>den\<close> operation.  For
  Goodman's question one must then add a category of worlds on which every
  principle in the proposed stock is globally true, together with base and
  vector-equivalence soundness.  The present theorems provide the one-world
  quotient truth and application clauses needed by that construction; they do
  not by themselves supply the environment quotient, global validity, or the
  required world-and-arrow system.
\<close>

end
