theory PPScratch
  imports Higher_Order_Metaphysics.Bacon_PP
begin

section \<open>Turn-6 scratch: the PP contradiction over the current CEV\<close>

subsection \<open>The collapse lemma (re-verified from turn 4)\<close>

lemma CEV_truth_implies_box:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A (\<box>\<^sub>o A)"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have taut: "prop_tautology \<Gamma>
      (Imp ObjTrue (Imp A (A \<longleftrightarrow>\<^sub>o ObjTrue)))"
    unfolding prop_tautology_def
    using assms true_type by auto
  have imp_taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjTrue (Imp A (A \<longleftrightarrow>\<^sub>o ObjTrue))"
    using taut by (rule CEV_prop_tautology)
  have body: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (A \<longleftrightarrow>\<^sub>o ObjTrue)"
    by (rule CEV_proves.MP[OF CEV_proves_ObjTrue imp_taut])
  have prem: "[] @ \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift_by (length ([] :: otype list)) A) (zeta_body [] A ObjTrue)"
    using body by (simp add: zeta_body_def fresh_vars_def)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (arrow_type [] Prop) A ObjTrue)"
    by (rule CEV_proves.ContextVectorEquivalence
        [where \<sigma>s = "[]" and A = A and F = A and G = ObjTrue])
       (use assms true_type prem in simp_all)
  then show ?thesis
    by (simp add: ObjBox_def)
qed


subsection \<open>The complement operator is logically pure\<close>

definition prop_neg :: oterm where
  "prop_neg = Lam Prop (Neg (Var 0))"

lemma typed_prop_neg: "\<Gamma> \<turnstile> prop_neg : Prop \<rightarrow>\<^sub>o Prop"
  unfolding prop_neg_def
  by (rule has_type.Lam, rule has_type.Neg, rule has_type.Var, simp)

lemma prop_neg_has_pure_vocabulary: "pp_logical_vocabulary prop_neg"
  by (simp add: pp_logical_vocabulary_def prop_neg_def)

lemma pp_pure_prop_neg_in_schema:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg \<in> pp_purity_schema"
  unfolding pp_purity_schema_def
  using typed_prop_neg[of "[]"] prop_neg_has_pure_vocabulary
  by blast

lemma CEV_beta_prop_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App prop_neg A \<longleftrightarrow>\<^sub>o Neg A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_neg A : Prop"
    using assms typed_prop_neg by auto
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms by auto
  have step: "compatible_step beta_contract (App prop_neg A) (Neg A)"
  proof -
    have "beta_contract (App (Lam Prop (Neg (Var 0))) A)
            (subst0 A (Neg (Var 0)))"
      by (rule beta_contract.beta)
    then show ?thesis
      unfolding prop_neg_def subst0_def by auto
  qed
  show ?thesis
    using app_type neg_type step by (rule CEV_beta_step)
qed


subsection \<open>Derivability of the two purity instances\<close>

lemma pp_r_derives_pure_prop_id:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id"
  using pp_full_QLN_derives_pure_prop_id
  by (rule CEV_set_derivable_mono)
    (auto simp: pp_full_QLN_r_axioms_def)

lemma pp_r_derives_pure_prop_neg:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg"
proof -
  have membership:
      "pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg \<in> pp_full_QLN_r_axioms"
    using pp_pure_prop_neg_in_schema
    by (simp add: pp_full_QLN_r_axioms_def pp_full_QLN_axioms_def
        pp_core_axioms_def)
  show ?thesis
    using membership pp_purity_schema_typed[OF pp_pure_prop_neg_in_schema]
    by (rule CEV_set_derivable.Assumption)
qed


subsection \<open>The two unary QLN instances\<close>

lemma pp_r_QLN_instance_prop_id:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    Imp (Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id) (pp_fun Prop pp_r))
      ((\<box>\<^sub>o (App prop_id pp_r)) \<longleftrightarrow>\<^sub>o
        Forall Prop (App prop_id (Var 0)))"
proof -
  have qln_member: "pp_unary_QLN \<in> pp_full_QLN_r_axioms"
    by (simp add: pp_full_QLN_r_axioms_def pp_full_QLN_axioms_def)
  have qln: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s pp_unary_QLN"
    using qln_member typed_pp_unary_QLN
    by (rule CEV_set_derivable.Assumption)
  have first_raw:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        subst0 prop_id
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
                Forall Prop (App (Var 2) (Var 0)))))"
    using qln typed_prop_id
    unfolding pp_unary_QLN_def
    by (rule CEV_set_forall_elim)
  have first:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id)
              (pp_fun Prop (Var 0)))
            ((\<box>\<^sub>o (App prop_id (Var 0))) \<longleftrightarrow>\<^sub>o
              Forall Prop (App prop_id (Var 0))))"
    using first_raw
    by (simp add: subst0_def prop_id_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def shift_def
        eval_nat_numeral)
  have second_raw:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        subst0 pp_r
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id)
              (pp_fun Prop (Var 0)))
            ((\<box>\<^sub>o (App prop_id (Var 0))) \<longleftrightarrow>\<^sub>o
              Forall Prop (App prop_id (Var 0))))"
    using first typed_pp_r
    by (rule CEV_set_forall_elim)
  show ?thesis
    using second_raw
    by (simp add: prop_id_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
        pp_r_def ObjBox_def ObjTrue_def subst0_def subst_lift_shift shift_def)
qed

lemma pp_r_QLN_instance_prop_neg:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    Imp (Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg) (pp_fun Prop pp_r))
      ((\<box>\<^sub>o (App prop_neg pp_r)) \<longleftrightarrow>\<^sub>o
        Forall Prop (App prop_neg (Var 0)))"
proof -
  have qln_member: "pp_unary_QLN \<in> pp_full_QLN_r_axioms"
    by (simp add: pp_full_QLN_r_axioms_def pp_full_QLN_axioms_def)
  have qln: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s pp_unary_QLN"
    using qln_member typed_pp_unary_QLN
    by (rule CEV_set_derivable.Assumption)
  have first_raw:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        subst0 prop_neg
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
                Forall Prop (App (Var 2) (Var 0)))))"
    using qln typed_prop_neg
    unfolding pp_unary_QLN_def
    by (rule CEV_set_forall_elim)
  have first:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg)
              (pp_fun Prop (Var 0)))
            ((\<box>\<^sub>o (App prop_neg (Var 0))) \<longleftrightarrow>\<^sub>o
              Forall Prop (App prop_neg (Var 0))))"
    using first_raw
    by (simp add: subst0_def prop_neg_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def shift_def
        eval_nat_numeral)
  have second_raw:
      "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
        subst0 pp_r
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg)
              (pp_fun Prop (Var 0)))
            ((\<box>\<^sub>o (App prop_neg (Var 0))) \<longleftrightarrow>\<^sub>o
              Forall Prop (App prop_neg (Var 0))))"
    using first typed_pp_r
    by (rule CEV_set_forall_elim)
  show ?thesis
    using second_raw
    by (simp add: prop_neg_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
        pp_r_def ObjBox_def ObjTrue_def subst0_def subst_lift_shift shift_def)
qed


subsection \<open>Propositional plumbing\<close>

lemma CEV_set_conj_left:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop" and B_type: "\<Gamma> \<turnstile> B : Prop"
    using d by (auto dest: CEV_set_derivable_formula elim: has_type.cases)
  have taut: "prop_tautology \<Gamma> (Imp (Conj A B) A)"
    unfolding prop_tautology_def using A_type B_type by auto
  show ?thesis
    using d CEV_set_prop_tautology[OF taut]
    by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_set_conj_right:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop" and B_type: "\<Gamma> \<turnstile> B : Prop"
    using d by (auto dest: CEV_set_derivable_formula elim: has_type.cases)
  have taut: "prop_tautology \<Gamma> (Imp (Conj A B) B)"
    unfolding prop_tautology_def using A_type B_type by auto
  show ?thesis
    using d CEV_set_prop_tautology[OF taut]
    by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_set_imp_trans:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
    and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp B C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A C"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop" and B_type: "\<Gamma> \<turnstile> B : Prop"
    using d1 by (auto dest: CEV_set_derivable_formula elim: has_type.cases)
  have C_type: "\<Gamma> \<turnstile> C : Prop"
    using d2 by (auto dest: CEV_set_derivable_formula elim: has_type.cases)
  have taut:
      "prop_tautology \<Gamma> (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
    unfolding prop_tautology_def using A_type B_type C_type by auto
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Imp B C) (Imp A C)"
    using d1 CEV_set_prop_tautology[OF taut]
    by (rule CEV_set_derivable.Derive_MP)
  show ?thesis
    using d2 step by (rule CEV_set_derivable.Derive_MP)
qed

lemma typed_ObjFalse': "\<Gamma> \<turnstile> ObjFalse : Prop"
  unfolding ObjFalse_def by (rule has_type.Neg, rule typed_ObjTrue)

lemma CEV_set_ObjTrue:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjTrue"
  using CEV_proves_ObjTrue by (rule CEV_set_derivable.Theorem)


subsection \<open>Refuting the two universal claims\<close>

definition prop_id_universal :: oterm where
  "prop_id_universal = Forall Prop (App prop_id (Var 0))"

definition prop_neg_universal :: oterm where
  "prop_neg_universal = Forall Prop (App prop_neg (Var 0))"

lemma CEV_prop_id_universal_imp_false:
  "[] \<turnstile>\<^sub>CEV Imp prop_id_universal (App prop_id ObjFalse)"
proof -
  have body_type: "Prop # [] \<turnstile> App prop_id (Var 0) : Prop"
    by (rule has_type.App[OF typed_prop_id]) simp
  have ui:
      "[] \<turnstile>\<^sub>CEV
        Imp (Forall Prop (App prop_id (Var 0)))
          (subst0 ObjFalse (App prop_id (Var 0)))"
    using body_type typed_ObjFalse'
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  show ?thesis
    using ui
    by (simp add: prop_id_universal_def subst0_def prop_id_def
        subst_lift_shift)
qed

lemma CEV_prop_neg_universal_imp_neg_true:
  "[] \<turnstile>\<^sub>CEV Imp prop_neg_universal (App prop_neg ObjTrue)"
proof -
  have body_type: "Prop # [] \<turnstile> App prop_neg (Var 0) : Prop"
    by (rule has_type.App[OF typed_prop_neg]) simp
  have ui:
      "[] \<turnstile>\<^sub>CEV
        Imp (Forall Prop (App prop_neg (Var 0)))
          (subst0 ObjTrue (App prop_neg (Var 0)))"
    using body_type typed_ObjTrue
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  show ?thesis
    using ui
    by (simp add: prop_neg_universal_def subst0_def prop_neg_def
        subst_lift_shift)
qed

lemma pp_r_derives_not_prop_id_universal:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg prop_id_universal"
proof -
  have d1: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp prop_id_universal (App prop_id ObjFalse)"
    using CEV_prop_id_universal_imp_false
    by (rule CEV_set_derivable.Theorem)
  have beta: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      (App prop_id ObjFalse \<longleftrightarrow>\<^sub>o ObjFalse)"
    using CEV_beta_prop_id[OF typed_ObjFalse']
    by (rule CEV_set_derivable.Theorem)
  have d2: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (App prop_id ObjFalse) ObjFalse"
    using beta by (rule CEV_set_conj_left)
  have chain: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp prop_id_universal (Neg ObjTrue)"
    using CEV_set_imp_trans[OF d1 d2] by (simp add: ObjFalse_def)
  show ?thesis
    using CEV_set_ObjTrue chain by (rule CEV_set_modus_tollens)
qed

lemma pp_r_derives_not_prop_neg_universal:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg prop_neg_universal"
proof -
  have d1: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp prop_neg_universal (App prop_neg ObjTrue)"
    using CEV_prop_neg_universal_imp_neg_true
    by (rule CEV_set_derivable.Theorem)
  have beta: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      (App prop_neg ObjTrue \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using CEV_beta_prop_neg[OF typed_ObjTrue]
    by (rule CEV_set_derivable.Theorem)
  have d2: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (App prop_neg ObjTrue) (Neg ObjTrue)"
    using beta by (rule CEV_set_conj_left)
  have chain: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp prop_neg_universal (Neg ObjTrue)"
    by (rule CEV_set_imp_trans[OF d1 d2])
  show ?thesis
    using CEV_set_ObjTrue chain by (rule CEV_set_modus_tollens)
qed


subsection \<open>The contradiction\<close>

lemma pp_r_derives_not_box_id:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    Neg (\<box>\<^sub>o (App prop_id pp_r))"
proof -
  have fun_r: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s pp_fun Prop pp_r"
    using typed_pp_fun[OF typed_pp_r]
    by (intro CEV_set_derivable.Assumption)
      (simp add: pp_full_QLN_r_axioms_def)
  have conj: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id) (pp_fun Prop pp_r)"
    using pp_r_derives_pure_prop_id fun_r by (rule CEV_set_conj_intro)
  have bicond: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      ((\<box>\<^sub>o (App prop_id pp_r)) \<longleftrightarrow>\<^sub>o prop_id_universal)"
    using conj pp_r_QLN_instance_prop_id
    by (simp only: prop_id_universal_def)
      (rule CEV_set_derivable.Derive_MP)
  have forward: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (\<box>\<^sub>o (App prop_id pp_r)) prop_id_universal"
    using bicond by (rule CEV_set_conj_left)
  show ?thesis
    using pp_r_derives_not_prop_id_universal forward
    by (rule CEV_set_modus_tollens_neg)
qed

lemma pp_r_derives_not_box_neg:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
    Neg (\<box>\<^sub>o (App prop_neg pp_r))"
proof -
  have fun_r: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s pp_fun Prop pp_r"
    using typed_pp_fun[OF typed_pp_r]
    by (intro CEV_set_derivable.Assumption)
      (simp add: pp_full_QLN_r_axioms_def)
  have conj: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_neg) (pp_fun Prop pp_r)"
    using pp_r_derives_pure_prop_neg fun_r by (rule CEV_set_conj_intro)
  have bicond: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      ((\<box>\<^sub>o (App prop_neg pp_r)) \<longleftrightarrow>\<^sub>o prop_neg_universal)"
    using conj pp_r_QLN_instance_prop_neg
    by (simp only: prop_neg_universal_def)
      (rule CEV_set_derivable.Derive_MP)
  have forward: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (\<box>\<^sub>o (App prop_neg pp_r)) prop_neg_universal"
    using bicond by (rule CEV_set_conj_left)
  show ?thesis
    using pp_r_derives_not_prop_neg_universal forward
    by (rule CEV_set_modus_tollens_neg)
qed

theorem pp_full_QLN_r_derives_ObjFalse:
  "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  have id_app_type: "[] \<turnstile> App prop_id pp_r : Prop"
    using typed_prop_id typed_pp_r by auto
  have neg_app_type: "[] \<turnstile> App prop_neg pp_r : Prop"
    using typed_prop_neg typed_pp_r by auto
  \<comment> \<open>the collapse lemma, applied to both operator values\<close>
  have coll_id: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (App prop_id pp_r) (\<box>\<^sub>o (App prop_id pp_r))"
    using CEV_truth_implies_box[OF id_app_type]
    by (rule CEV_set_derivable.Theorem)
  have coll_neg: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (App prop_neg pp_r) (\<box>\<^sub>o (App prop_neg pp_r))"
    using CEV_truth_implies_box[OF neg_app_type]
    by (rule CEV_set_derivable.Theorem)
  have not_id_app: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Neg (App prop_id pp_r)"
    using pp_r_derives_not_box_id coll_id
    by (rule CEV_set_modus_tollens_neg)
  have not_neg_app: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Neg (App prop_neg pp_r)"
    using pp_r_derives_not_box_neg coll_neg
    by (rule CEV_set_modus_tollens_neg)
  \<comment> \<open>beta bridges back to \<open>r\<close> and \<open>Neg r\<close>\<close>
  have beta_id: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      (App prop_id pp_r \<longleftrightarrow>\<^sub>o pp_r)"
    using CEV_beta_prop_id[OF typed_pp_r]
    by (rule CEV_set_derivable.Theorem)
  have beta_neg: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      (App prop_neg pp_r \<longleftrightarrow>\<^sub>o Neg pp_r)"
    using CEV_beta_prop_neg[OF typed_pp_r]
    by (rule CEV_set_derivable.Theorem)
  have imp_r_id: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp pp_r (App prop_id pp_r)"
    using beta_id by (rule CEV_set_conj_right)
  have imp_negr: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (Neg pp_r) (App prop_neg pp_r)"
    using beta_neg by (rule CEV_set_conj_right)
  have not_r: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg pp_r"
    using not_id_app imp_r_id by (rule CEV_set_modus_tollens_neg)
  have not_not_r: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg (Neg pp_r)"
    using not_neg_app imp_negr by (rule CEV_set_modus_tollens_neg)
  have r_type: "[] \<turnstile> pp_r : Prop" by (rule typed_pp_r)
  have t_type: "[] \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  have taut_type:
      "[] \<turnstile> Imp (Neg pp_r) (Imp (Neg (Neg pp_r)) (Neg ObjTrue)) : Prop"
    by (rule has_type.Imp[OF has_type.Neg[OF r_type]
          has_type.Imp[OF has_type.Neg[OF has_type.Neg[OF r_type]]
            has_type.Neg[OF t_type]]])
  have taut: "prop_tautology []
      (Imp (Neg pp_r) (Imp (Neg (Neg pp_r)) ObjFalse))"
    unfolding prop_tautology_def ObjFalse_def
    using taut_type by auto
  have step: "[] ; pp_full_QLN_r_axioms \<turnstile>\<^sub>CEV\<^sub>s
      Imp (Neg (Neg pp_r)) ObjFalse"
    using not_r CEV_set_prop_tautology[OF taut]
    by (rule CEV_set_derivable.Derive_MP)
  show ?thesis
    using not_not_r step by (rule CEV_set_derivable.Derive_MP)
qed

end
