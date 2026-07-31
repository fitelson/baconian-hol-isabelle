theory Bacon_PP_Fresh_Finite_Core_Search
  imports Bacon_PP_Fresh_Finite_Fragment
begin

section \<open>Certified support for bounded finite-core search\<close>

text \<open>
  The external search enumerates finite stocks of displayed instances.  It is
  allowed to propose a contradiction, but it is not trusted to certify one.
  This theory supplies the small introduction lemmas used by a generated
  Isabelle replay.  A proposed stock counts as an inconsistent core only after
  Isabelle proves both that it is contained in the selected Goodman stock and
  that it derives \<open>ObjFalse\<close> in the exact \<open>CEV\<^sup>+\<close> calculus.
\<close>

subsection \<open>A finite enumeration of simple types\<close>

fun finite_core_type_depth :: "otype \<Rightarrow> nat" where
  "finite_core_type_depth Ind = 0"
| "finite_core_type_depth Prop = 0"
| "finite_core_type_depth (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Suc (max (finite_core_type_depth \<sigma>) (finite_core_type_depth \<tau>))"

fun finite_core_types :: "nat \<Rightarrow> otype list" where
  "finite_core_types 0 = [Ind, Prop]"
| "finite_core_types (Suc n) =
    remdups
      (finite_core_types n @
        concat
          (map
            (\<lambda>\<sigma>. map (Arr \<sigma>) (finite_core_types n))
            (finite_core_types n)))"

lemma finite_set_finite_core_types:
  "finite (set (finite_core_types n))"
  by simp

lemma finite_core_types_mono:
  "set (finite_core_types n) \<subseteq> set (finite_core_types (Suc n))"
  by simp

lemma finite_core_types_depth_bound:
  assumes "\<sigma> \<in> set (finite_core_types n)"
  shows "finite_core_type_depth \<sigma> \<le> n"
  using assms
proof (induction n arbitrary: \<sigma>)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
    by (auto dest: Suc.IH intro: le_SucI)
qed

lemma finite_core_types_complete:
  assumes "finite_core_type_depth \<sigma> \<le> n"
  shows "\<sigma> \<in> set (finite_core_types n)"
  using assms
proof (induction \<sigma> arbitrary: n)
  case Ind
  then show ?case
    by (induction n) auto
next
  case Prop
  then show ?case
    by (induction n) auto
next
  case (Arr \<sigma> \<tau>)
  then obtain m where n_def: "n = Suc m"
    by (cases n) auto
  have \<sigma>_in: "\<sigma> \<in> set (finite_core_types m)"
    using Arr.prems n_def Arr.IH(1) by auto
  have \<tau>_in: "\<tau> \<in> set (finite_core_types m)"
    using Arr.prems n_def Arr.IH(2) by auto
  show ?case
    using \<sigma>_in \<tau>_in n_def by auto
qed

theorem finite_core_types_iff:
  "\<sigma> \<in> set (finite_core_types n) \<longleftrightarrow>
    finite_core_type_depth \<sigma> \<le> n"
  using finite_core_types_depth_bound finite_core_types_complete by blast

subsection \<open>Machine-checkable schema introduction\<close>

lemma finite_core_purity_schemaI:
  assumes type_check: "infer_type [] M = Some \<sigma>"
    and logical: "consts_of M = {}"
  shows "pp_pure \<sigma> M \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
  using infer_type_sound[OF type_check] logical by blast

lemma finite_core_application_closure_schemaI:
  "pp_application_closure \<sigma> \<tau> \<in> pp_application_closure_schema"
  unfolding pp_application_closure_schema_def by blast

lemma finite_core_no_other_fundamentals_schemaI:
  assumes "\<sigma> \<noteq> Prop"
  shows "pp_no_fundamentals \<sigma> \<in> pp_no_other_fundamentals_schema"
  using assms unfolding pp_no_other_fundamentals_schema_def by blast

lemma finite_core_modalized_functionality_schemaI:
  "fresh_modalized_functionality \<sigma> \<tau>
    \<in> fresh_modalized_functionality_schema"
  unfolding fresh_modalized_functionality_schema_def by blast

subsection \<open>The three search profiles\<close>

datatype finite_core_profile =
    Recombination_Only
  | Repaired_Zeroary_Exhaustion
  | Full_QLN
  | Full_QLN_Modalized_Functionality

text \<open>
  The two constructor names containing \<open>Full_QLN\<close> are retained for stable
  search manifests.  In this exactly-one-fundamental setting they denote the
  complete zeroary-and-unary package, not a generic all-arity encoding.
\<close>

fun finite_core_profile_axioms :: "finite_core_profile \<Rightarrow> oterm set" where
  "finite_core_profile_axioms Recombination_Only =
    pp_recombination_PP_axioms"
| "finite_core_profile_axioms Repaired_Zeroary_Exhaustion =
    insert pp_zeroary_exhaustion pp_recombination_PP_axioms"
| "finite_core_profile_axioms Full_QLN =
    pp_full_QLN_PP_axioms"
| "finite_core_profile_axioms Full_QLN_Modalized_Functionality =
    fresh_goodman_axioms"

lemma finite_core_recombination_subset_full_QLN:
  "finite_core_profile_axioms Recombination_Only
    \<subseteq> finite_core_profile_axioms Full_QLN"
  unfolding pp_recombination_PP_axioms_def
    pp_full_QLN_PP_axioms_def pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def pp_exhaustion_axioms_def
    finite_core_profile_axioms.simps
  by blast

lemma finite_core_recombination_subset_repaired:
  "finite_core_profile_axioms Recombination_Only
    \<subseteq> finite_core_profile_axioms Repaired_Zeroary_Exhaustion"
  unfolding finite_core_profile_axioms.simps
  by blast

lemma finite_core_repaired_subset_full_QLN:
  "finite_core_profile_axioms Repaired_Zeroary_Exhaustion
    \<subseteq> finite_core_profile_axioms Full_QLN"
  unfolding pp_recombination_PP_axioms_def
    pp_full_QLN_PP_axioms_def pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def pp_exhaustion_axioms_def
    finite_core_profile_axioms.simps
  by blast

lemma finite_core_full_QLN_subset_modalized:
  "finite_core_profile_axioms Full_QLN
    \<subseteq> finite_core_profile_axioms Full_QLN_Modalized_Functionality"
  unfolding fresh_goodman_axioms_def fresh_goodman_background_axioms_def
    pp_full_QLN_PP_axioms_def finite_core_profile_axioms.simps
  by blast

lemma finite_core_target_PP_in_profile:
  "pp_target_PP \<in> finite_core_profile_axioms profile"
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

lemma finite_core_unique_fundamental_in_profile:
  "pp_unique_fundamental Prop \<in> finite_core_profile_axioms profile"
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

lemma finite_core_purity_in_profile:
  assumes "A \<in> pp_purity_schema"
  shows "A \<in> finite_core_profile_axioms profile"
  using assms
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

lemma finite_core_application_closure_in_profile:
  "pp_application_closure \<sigma> \<tau>
    \<in> finite_core_profile_axioms profile"
  using finite_core_application_closure_schemaI
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

lemma finite_core_no_fundamentals_in_profile:
  assumes "\<sigma> \<noteq> Prop"
  shows "pp_no_fundamentals \<sigma>
    \<in> finite_core_profile_axioms profile"
  using finite_core_no_other_fundamentals_schemaI[OF assms]
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def)

lemma finite_core_zeroary_recombination_in_profile:
  "pp_zeroary_recombination \<in> finite_core_profile_axioms profile"
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def)

lemma finite_core_unary_recombination_in_profile:
  "pp_unary_recombination \<in> finite_core_profile_axioms profile"
  by (cases profile)
    (auto simp: pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def)

lemma finite_core_zeroary_exhaustion_in_profile:
  assumes "profile \<noteq> Recombination_Only"
  shows "pp_zeroary_exhaustion \<in> finite_core_profile_axioms profile"
  using assms
  by (cases profile)
    (auto simp: pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def pp_exhaustion_axioms_def)

lemma finite_core_unary_exhaustion_in_profile:
  assumes "profile = Full_QLN \<or>
    profile = Full_QLN_Modalized_Functionality"
  shows "pp_unary_exhaustion \<in> finite_core_profile_axioms profile"
  using assms
  by (cases profile)
    (auto simp: pp_full_QLN_PP_axioms_def fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def pp_exhaustion_axioms_def)

lemma finite_core_modalized_functionality_in_profile:
  assumes "profile = Full_QLN_Modalized_Functionality"
  shows "fresh_modalized_functionality \<sigma> \<tau>
    \<in> finite_core_profile_axioms profile"
  using assms finite_core_modalized_functionality_schemaI[of \<sigma> \<tau>]
  by (simp add: fresh_goodman_axioms_def fresh_goodman_background_axioms_def)

subsection \<open>Purity of enumerated diagonal operators\<close>

lemma finite_core_application_closed:
  assumes closure: "pp_application_closure \<sigma> \<tau> \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and pure_F:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    and pure_X:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> X"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<tau> (App F X)"
proof -
  have closure_type:
    "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_application_closure_def pp_pure_def pp_Pure_def
        lookup_def)
  have d_closure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_application_closure \<sigma> \<tau>"
    using closure closure_type by (rule CEV_axiom_proves.Axiom)
  have d_outer_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 F
        (Forall \<sigma>
          (Imp
            (Conj
              (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
              (pp_pure \<sigma> (Var 0)))
            (pp_pure \<tau> (App (Var 1) (Var 0)))))"
  proof (rule CEV_axiom_UI_typed)
    show "\<Gamma> \<turnstile>
        Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (Forall \<sigma>
            (Imp
              (Conj
                (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
                (pp_pure \<sigma> (Var 0)))
              (pp_pure \<tau> (App (Var 1) (Var 0))))) : Prop"
      using closure_type
      unfolding pp_application_closure_def .
  next
    show "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
      by (rule F_type)
  next
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (Forall \<sigma>
            (Imp
              (Conj
                (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
                (pp_pure \<sigma> (Var 0)))
              (pp_pure \<tau> (App (Var 1) (Var 0)))))"
      using d_closure
      unfolding pp_application_closure_def .
  qed
  have d_outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0))))"
    using d_outer_raw
    by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0)))) : Prop"
    using CEV_axiom_proves_formula[OF d_outer] .
  have d_inner_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 X
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0))))"
    using outer_type X_type d_outer by (rule CEV_axiom_UI_typed)
  have d_inner:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
          (pp_pure \<sigma> X))
        (pp_pure \<tau> (App F X))"
  proof -
    have subst_shift:
      "subst (case_nat X Var) (rename Suc F) = F"
      using subst0_shift[of X F]
      unfolding subst0_def shift_def .
    show ?thesis
      using d_inner_raw
      by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def
          subst_shift)
  qed
  have d_pair:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (pp_pure \<sigma> X)"
    using pure_F pure_X by (rule CEV_axiom_conj_intro)
  show ?thesis
    using d_pair d_inner by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_pure_logical_builder_application:
  assumes builder_type:
      "infer_type [] B =
        Some ((((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)))"
    and logical: "consts_of B = {}"
  shows
    "[] ; finite_core_profile_axioms profile
      \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          (App B (pp_Pure (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  have B_type:
    "[] \<turnstile> B :
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"
    using builder_type by (rule infer_type_sound)
  have B_purity_member:
    "pp_pure
        (((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)) B
      \<in> finite_core_profile_axioms profile"
    using finite_core_purity_schemaI[OF builder_type logical]
    by (rule finite_core_purity_in_profile)
  have B_pure:
    "[] ; finite_core_profile_axioms profile
      \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure
          (((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
            \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)) B"
    using B_purity_member typed_pp_pure[OF B_type]
    by (rule CEV_axiom_proves.Axiom)
  have classifier_pure:
    "[] ; finite_core_profile_axioms profile
      \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure
          ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
          (pp_Pure (Prop \<rightarrow>\<^sub>o Prop))"
  proof -
    have target_type: "[] \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def
          pp_Pure_def lookup_def)
    have target:
      "[] ; finite_core_profile_axioms profile
        \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using finite_core_target_PP_in_profile target_type
      by (rule CEV_axiom_proves.Axiom)
    show ?thesis
      using target
      by (simp add: pp_target_PP_def pp_purity_of_pure_def)
  qed
  have classifier_type:
    "[] \<turnstile> pp_Pure (Prop \<rightarrow>\<^sub>o Prop) :
      (Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop"
    using typed_pp_Pure[of "[]" "Prop \<rightarrow>\<^sub>o Prop"]
    by simp
  show ?thesis
    using finite_core_application_closure_in_profile
      B_type classifier_type B_pure classifier_pure
    by (rule finite_core_application_closed)
qed

subsection \<open>Certification boundary\<close>

definition finite_core_certified ::
    "finite_core_profile \<Rightarrow> oterm set \<Rightarrow> bool"
where
  "finite_core_certified profile U \<longleftrightarrow>
    finite U \<and>
    U \<subseteq> finite_core_profile_axioms profile \<and>
    [] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"

theorem finite_core_certified_negative_answer:
  assumes "finite_core_certified profile U"
  shows "\<not> CEV_axiom_consistent []
    (finite_core_profile_axioms profile)"
proof -
  have U_sub:
    "U \<subseteq> finite_core_profile_axioms profile"
    using assms unfolding finite_core_certified_def by blast
  have false_U: "[] ; U \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using assms unfolding finite_core_certified_def by blast
  have "[] ; finite_core_profile_axioms profile
      \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using false_U U_sub by (rule CEV_axiom_proves_mono)
  then show ?thesis
    unfolding CEV_axiom_consistent_def by blast
qed

subsection \<open>Replay macros\<close>

lemma finite_core_ObjTrue:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
  by (rule CEV_axiom_proves_ObjTrue)

lemma finite_core_reflexivity:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> M M"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.Ref)

lemma finite_core_conj_left:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    using CEV_axiom_proves_formula[OF assms]
    by (auto elim: has_type.cases)+
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) A"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_left)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj A B) A"
    using taut by (rule CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_conj_right:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    using CEV_axiom_proves_formula[OF assms]
    by (auto elim: has_type.cases)+
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) B"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_right)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj A B) B"
    using taut by (rule CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_double_negation:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Neg A)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using CEV_axiom_proves_formula[OF assms]
    by (auto elim: has_type.cases)
  have taut_raw: "prop_tautology \<Gamma> (Imp (Neg (Neg A)) A)"
    using A_type
    unfolding prop_tautology_def by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg (Neg A)) A"
    using taut_raw
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg (Neg A)) A"
    using taut by (rule CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_double_negation_intro:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Neg A)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule CEV_axiom_proves_formula)
  have taut_raw: "prop_tautology \<Gamma> (Imp A (Neg (Neg A)))"
    using A_type
    unfolding prop_tautology_def by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Neg (Neg A))"
    using taut_raw
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Neg (Neg A))"
    using taut by (rule CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_contradiction:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_axiom_proves_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule CEV_axiom_proves.Base)
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CEV_axiom_proves.MP)
  show ?thesis
    using assms(2) step by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Replay support for the context-indexed tranche\<close>

lemma finite_core_prop_tautology:
  assumes "prop_tautology \<Gamma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)

lemma finite_core_existential_generalization:
  assumes body_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and derived_instance:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst0 M A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Exists \<sigma> A"
proof -
  have eg:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp (subst0 M A) (Exists \<sigma> A)"
    using body_type term_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have d_eg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (subst0 M A) (Exists \<sigma> A)"
    using eg by (rule CEV_axiom_proves.Base)
  show ?thesis
    using derived_instance d_eg by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_leibniz:
  assumes left_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and right_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and predicate_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and identity: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A B"
    and left: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App F A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App F B"
proof -
  have ll:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))"
    using left_type right_type predicate_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have d_ll:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))"
    using ll by (rule CEV_axiom_proves.Base)
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App F A) (App F B)"
    using identity d_ll by (rule CEV_axiom_proves.MP)
  show ?thesis
    using left step by (rule CEV_axiom_proves.MP)
qed

lemma finite_core_beta:
  assumes left_type: "\<Gamma> \<turnstile> A : Prop"
    and right_type: "\<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step beta_contract A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.Beta)

lemma finite_core_eta:
  assumes left_type: "\<Gamma> \<turnstile> A : Prop"
    and right_type: "\<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step eta_contract A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.Eta)

lemma finite_core_generalization:
  assumes antecedent_type: "\<Gamma> \<turnstile> P : Prop"
    and consequent_type: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and premise:
      "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (Forall \<sigma> Q)"
  using assms by (rule CEV_axiom_proves.Gen)

lemma finite_core_instantiation:
  assumes antecedent_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and consequent_type: "\<Gamma> \<turnstile> Q : Prop"
    and premise:
      "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> P) Q"
  using assms by (rule CEV_axiom_proves.Inst)

lemma finite_core_unary_vector_equivalence:
  assumes left_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and right_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and premise:
      "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o
          App (shift G) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G"
proof -
  have zeta:
    "[\<sigma>] @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body [\<sigma>] F G"
    using premise
    by (simp add: zeta_body_def fresh_vars_def shift_by_1)
  have
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq (arrow_type [\<sigma>] Prop) F G"
  proof (rule CEV_axiom_proves.VectorEquivalence[
      where \<sigma>s = "[\<sigma>]" and F = F and G = G])
    show "\<Gamma> \<turnstile> F : arrow_type [\<sigma>] Prop"
      using left_type by simp
  next
    show "\<Gamma> \<turnstile> G : arrow_type [\<sigma>] Prop"
      using right_type by simp
  next
    show "[\<sigma>] @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body [\<sigma>] F G"
      using zeta .
  qed
  then show ?thesis
    by simp
qed

lemma finite_core_boolean_identity:
  assumes "A \<in> set all_boolean_identities"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.BooleanIdentity)

lemma finite_core_classic_identity_identity:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ classic_identity_identity \<sigma>"
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.IdentityIdentity)

lemma finite_core_classic_absorb_disj_forall:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ classic_absorb_disj_forall \<sigma>"
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.AbsorbDisjForall)

lemma finite_core_classic_dist_disj_forall:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ classic_dist_disj_forall \<sigma>"
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.DistDisjForall)

lemma finite_core_classic_absorb_conj_exists:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ classic_absorb_conj_exists \<sigma>"
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.AbsorbConjExists)

lemma finite_core_classic_dist_conj_exists:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ classic_dist_conj_exists \<sigma>"
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.DistConjExists)

text \<open>
  No external proof-search status implies \<open>finite_core_certified\<close>.  In
  particular, a Vampire refutation and a bounded forward-search trace remain
  candidates until a generated replay establishes this predicate.
\<close>

end
