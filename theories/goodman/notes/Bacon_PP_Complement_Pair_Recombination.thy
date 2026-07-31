theory Bacon_PP_Complement_Pair_Recombination
  imports Bacon_PP_QSS_Recombination_Bridge
begin

section \<open>The complement-pair operator is not pure at a fundamental proposition\<close>

text \<open>
  For a proposition \<open>p\<close>, let \<open>B\<^sup>\<plusminus>(p)\<close> be the unary operator
  \[
    B^\pm(p)(q) =
      \Box(q \longleftrightarrow p)
      \mathbin{\lor}
      \Box(q \longleftrightarrow \neg p).
  \]
  Unary Recombination alone rules out the purity of this operator whenever
  \<open>p\<close> is fundamental.  Neither PP, Exhaustion, QSS, nor uniqueness of the
  fundamental proposition is used.
\<close>

definition pp_complement_pair_operator :: "oterm \<Rightarrow> oterm" where
  "pp_complement_pair_operator p =
    Lam Prop
      (Disj
        (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (shift p)))
        (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (shift p)))))"

definition pp_complement_pair_builder :: oterm where
  "pp_complement_pair_builder =
    Lam Prop
      (Lam Prop
        (Disj
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (Var 1))))))"

lemma typed_pp_complement_pair_builder:
  "\<Gamma> \<turnstile> pp_complement_pair_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_complement_pair_builder_def pp_unary_ty_def
      ObjBox_def ObjTrue_def lookup_def)

lemma pp_complement_pair_builder_constant_free:
  "consts_of pp_complement_pair_builder = {}"
  by (simp add: pp_complement_pair_builder_def ObjBox_def ObjTrue_def)

lemma typed_pp_complement_pair_operator:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_complement_pair_operator p : pp_unary_ty"
  unfolding pp_complement_pair_operator_def pp_unary_ty_def
proof (rule has_type.Lam)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have p_shift: "Prop # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  have np_shift: "Prop # \<Gamma> \<turnstile> Neg (shift p) : Prop"
    using p_shift by (rule has_type.Neg)
  show "Prop # \<Gamma> \<turnstile>
    Disj
      (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (shift p)))
      (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (shift p)))) :
      Prop"
    using q_type p_shift np_shift
    by (intro has_type.Disj typed_ObjBox has_type.Conj has_type.Imp)
qed

lemma pp_complement_pair_builder_apply_beta:
  "compatible_step beta_contract
    (App pp_complement_pair_builder p)
    (pp_complement_pair_operator p)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Lam Prop
            (Disj
              (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
              (\<box>\<^sub>o
                ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (Var 1)))))))
        p)
      (subst0 p
        (Lam Prop
          (Disj
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1)))
            (\<box>\<^sub>o
              ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (Var 1)))))))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App pp_complement_pair_builder p)
    (pp_complement_pair_operator p)"
    using step
    by (simp add: pp_complement_pair_builder_def
        pp_complement_pair_operator_def subst0_def shift_def
        ObjBox_def ObjTrue_def)
qed

lemma pp_complement_pair_operator_beta:
  "compatible_step beta_contract
    (App (pp_complement_pair_operator p) q)
    (Disj
      (\<box>\<^sub>o (q \<longleftrightarrow>\<^sub>o p))
      (\<box>\<^sub>o (q \<longleftrightarrow>\<^sub>o (Neg p))))"
proof -
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Disj
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (shift p)))
            (\<box>\<^sub>o
              ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (shift p))))))
        q)
      (subst0 q
        (Disj
          (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (shift p)))
          (\<box>\<^sub>o
            ((Var 0) \<longleftrightarrow>\<^sub>o (Neg (shift p))))))"
    by (rule beta_contract.beta)
  have exact:
    "beta_contract
      (App (pp_complement_pair_operator p) q)
      (Disj
        (\<box>\<^sub>o (q \<longleftrightarrow>\<^sub>o p))
        (\<box>\<^sub>o (q \<longleftrightarrow>\<^sub>o (Neg p))))"
    using step subst0_shift[of q p]
    by (simp add: pp_complement_pair_operator_def subst0_def shift_def
        ObjBox_def ObjTrue_def)
  show ?thesis
    using exact by (rule compatible_step.root)
qed

lemma pp_identity_purity_in_recombination_background:
  "pp_pure pp_unary_ty pp_identity_operator
    \<in> pp_recombination_background_axioms"
  unfolding pp_recombination_background_axioms_def pp_background_axioms_def
  using pp_identity_operator_purity_axiom by blast

lemma pp_negation_purity_in_recombination_background:
  "pp_pure pp_unary_ty pp_negation_operator
    \<in> pp_recombination_background_axioms"
  unfolding pp_recombination_background_axioms_def pp_background_axioms_def
  using pp_negation_operator_purity_axiom by blast

lemma pp_unary_recombination_in_recombination_background:
  "pp_unary_recombination \<in> pp_recombination_background_axioms"
  unfolding pp_recombination_background_axioms_def by blast

lemma pp_complement_pair_builder_purity_in_background:
  "pp_pure
      (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      pp_complement_pair_builder
    \<in> pp_recombination_background_axioms"
  unfolding pp_recombination_background_axioms_def
    pp_background_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
  using typed_pp_complement_pair_builder
    pp_complement_pair_builder_constant_free
  by blast

lemma pp_application_closure_in_recombination_background:
  "pp_application_closure \<sigma> \<tau>
    \<in> pp_recombination_background_axioms"
  unfolding pp_recombination_background_axioms_def
    pp_background_axioms_def pp_application_closure_schema_def
  by blast

lemma CEV_complement_pair_pure_if_parameter_pure:
  assumes background: "pp_recombination_background_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure Prop p)
      (pp_pure pp_unary_ty
        (pp_complement_pair_operator p))"
proof -
  let ?P = "pp_pure Prop p"
  let ?B = "App pp_complement_pair_builder p"
  let ?F = "pp_complement_pair_operator p"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using p_type by (rule typed_pp_pure)
  have B_type: "\<Gamma> \<turnstile> ?B : pp_unary_ty"
    using typed_pp_complement_pair_builder p_type
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using p_type by (rule typed_pp_complement_pair_operator)
  have d_P:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have builder_axiom:
    "pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_complement_pair_builder \<in> T"
    using background pp_complement_pair_builder_purity_in_background
    by blast
  have d_builder:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_complement_pair_builder"
    using builder_axiom
      typed_pp_pure[OF typed_pp_complement_pair_builder]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have closure: "pp_application_closure Prop pp_unary_ty \<in> T"
    using background
      pp_application_closure_in_recombination_background
    by blast
  have d_B:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?B"
    using closure typed_pp_complement_pair_builder p_type
      d_builder d_P
    by (rule pp_axiom_application_closed_from)
  have B_raw: "\<Gamma> \<turnstile> ?B : Prop \<rightarrow>\<^sub>o Prop"
    using B_type unfolding pp_unary_ty_def .
  have F_raw: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop"
    using F_type unfolding pp_unary_ty_def .
  have B_shift_type:
    "Prop # \<Gamma> \<turnstile> shift ?B : pp_unary_ty"
    using B_type by (rule typed_shift_ctx)
  have F_shift_type:
    "Prop # \<Gamma> \<turnstile> shift ?F : pp_unary_ty"
    using F_type by (rule typed_shift_ctx)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have left_type:
    "Prop # \<Gamma> \<turnstile> App (shift ?B) (Var 0) : Prop"
    using B_shift_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type:
    "Prop # \<Gamma> \<turnstile> App (shift ?F) (Var 0) : Prop"
    using F_shift_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have beta_step:
    "compatible_step beta_contract
      (App (shift ?B) (Var 0))
      (App (shift ?F) (Var 0))"
  proof -
    have unshifted:
      "compatible_step beta_contract
        ?B ?F"
      by (rule pp_complement_pair_builder_apply_beta)
    have shifted:
      "compatible_step beta_contract (shift ?B) (shift ?F)"
      using unshifted unfolding shift_def
      by (rule compatible_beta_rename)
    show ?thesis
      using shifted by (rule compatible_step.App_left)
  qed
  have pointwise:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift ?B) (Var 0)
        \<longleftrightarrow>\<^sub>o
       App (shift ?F) (Var 0))"
    using left_type right_type beta_step by (rule CEV_beta_step)
  have beta_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq pp_unary_ty ?B ?F"
    using B_raw F_raw pointwise
    unfolding pp_unary_ty_def
    by (rule CEV_unary_equivalence)
  have beta_eq_local:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?B ?F"
    using beta_eq
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_F:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?F"
    using B_type F_type d_B beta_eq_local
    by (rule CEV_axiom_from_pure_eq_transport)
  show ?thesis
    using P_type d_F by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_from_box_of_unary_beta:
  assumes O_type: "\<Gamma> \<turnstile> OPR : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and R_type: "\<Gamma> \<turnstile> R : Prop"
    and beta: "compatible_step beta_contract (App OPR q) R"
    and box_R:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o R"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    \<box>\<^sub>o (App OPR q)"
proof -
  have app_type: "\<Gamma> \<turnstile> App OPR q : Prop"
    using O_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have equiv:
    "\<Gamma> \<turnstile>\<^sub>CEV (App OPR q \<longleftrightarrow>\<^sub>o R)"
    using app_type R_type beta by (rule CEV_beta_step)
  have reverse: "\<Gamma> \<turnstile>\<^sub>CEV Imp R (App OPR q)"
    using app_type R_type equiv by (rule CEV_beta_right_imp)
  have box_reverse:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp R (App OPR q))"
    using CEV_axiom_necessitation[
      OF CEV_axiom_proves.Base[OF reverse]]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using R_type app_type box_reverse box_R
    by (rule CEV_axiom_from_box_MP)
qed

lemma CEV_axiom_from_fundamental_not_box:
  assumes background: "pp_recombination_background_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and fundamental:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (\<box>\<^sub>o r)"
proof -
  let ?A = "\<box>\<^sub>o r"
  let ?U =
    "Forall Prop
      (App (shift pp_identity_operator) (Var 0))"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using r_type by (rule typed_ObjBox)
  have sub: "S \<subseteq> insert ?A S" by blast
  have d_A:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
    using fundamental sub by (rule CEV_axiom_from_mono)
  have pure_axiom:
    "pp_pure pp_unary_ty pp_identity_operator \<in> T"
    using background pp_identity_purity_in_recombination_background
    by blast
  have d_pure:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_identity_operator"
    using pure_axiom typed_pp_pure[OF typed_pp_identity_operator]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have pair:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty pp_identity_operator)
        (pp_fun Prop r)"
    using d_pure d_fun by (rule CEV_axiom_from_conj_intro)
  have recombination:
    "pp_unary_recombination \<in> T"
    using background pp_unary_recombination_in_recombination_background
    by blast
  have rec_rule:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty pp_identity_operator)
          (pp_fun Prop r))
        (Imp
          (\<box>\<^sub>o (App pp_identity_operator r))
          ?U)"
    using CEV_axiom_unary_recombination_instance[
      OF recombination typed_pp_identity_operator r_type]
    by (rule CEV_axiom_from.Theorem)
  have rec_tail:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o (App pp_identity_operator r)) ?U"
    using pair rec_rule by (rule CEV_axiom_from.MP)
  have box_app:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (App pp_identity_operator r)"
    using typed_pp_identity_operator r_type r_type
      pp_identity_apply_beta d_A
    by (rule CEV_axiom_from_box_of_unary_beta)
  have d_U:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
    using box_app rec_tail by (rule CEV_axiom_from.MP)
  have U_type: "\<Gamma> \<turnstile> ?U : Prop"
    using d_U by (rule CEV_axiom_from_formula)
  have d_false_app_raw:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 ObjFalse
        (App (shift pp_identity_operator) (Var 0))"
    using U_type typed_ObjFalse d_U
    by (rule CEV_axiom_from_UI_typed)
  have d_false_app:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_identity_operator ObjFalse"
    using d_false_app_raw
    by (simp add: pp_identity_operator_def subst0_def shift_def)
  have false_imp:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (App pp_identity_operator ObjFalse) ObjFalse"
  proof -
    have app_false_type:
      "\<Gamma> \<turnstile> App pp_identity_operator ObjFalse : Prop"
      using typed_pp_identity_operator typed_ObjFalse
      unfolding pp_unary_ty_def by (rule has_type.App)
    show ?thesis
      using app_false_type typed_ObjFalse
        CEV_pp_identity_apply[OF typed_ObjFalse]
    by (rule CEV_beta_left_imp)
  qed
  have d_false:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_false_app
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF false_imp]]
    by (rule CEV_axiom_from.MP)
  have A_imp_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?A ObjFalse"
    using A_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using A_imp_false to_neg by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_fundamental_not_box_neg:
  assumes background: "pp_recombination_background_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and fundamental:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (\<box>\<^sub>o (Neg r))"
proof -
  let ?nr = "Neg r"
  let ?A = "\<box>\<^sub>o ?nr"
  let ?U =
    "Forall Prop
      (App (shift pp_negation_operator) (Var 0))"
  have nr_type: "\<Gamma> \<turnstile> ?nr : Prop"
    using r_type by (rule has_type.Neg)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using nr_type by (rule typed_ObjBox)
  have sub: "S \<subseteq> insert ?A S" by blast
  have d_A:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
    using fundamental sub by (rule CEV_axiom_from_mono)
  have pure_axiom:
    "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    using background pp_negation_purity_in_recombination_background
    by blast
  have d_pure:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_negation_operator"
    using pure_axiom typed_pp_pure[OF typed_pp_negation_operator]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have pair:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty pp_negation_operator)
        (pp_fun Prop r)"
    using d_pure d_fun by (rule CEV_axiom_from_conj_intro)
  have recombination:
    "pp_unary_recombination \<in> T"
    using background pp_unary_recombination_in_recombination_background
    by blast
  have rec_rule:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty pp_negation_operator)
          (pp_fun Prop r))
        (Imp
          (\<box>\<^sub>o (App pp_negation_operator r))
          ?U)"
    using CEV_axiom_unary_recombination_instance[
      OF recombination typed_pp_negation_operator r_type]
    by (rule CEV_axiom_from.Theorem)
  have rec_tail:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o (App pp_negation_operator r)) ?U"
    using pair rec_rule by (rule CEV_axiom_from.MP)
  have box_app:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (App pp_negation_operator r)"
    using typed_pp_negation_operator r_type nr_type
      pp_negation_apply_beta d_A
    by (rule CEV_axiom_from_box_of_unary_beta)
  have d_U:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
    using box_app rec_tail by (rule CEV_axiom_from.MP)
  have U_type: "\<Gamma> \<turnstile> ?U : Prop"
    using d_U by (rule CEV_axiom_from_formula)
  have d_neg_true_raw:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 ObjTrue
        (App (shift pp_negation_operator) (Var 0))"
    using U_type typed_ObjTrue d_U
    by (rule CEV_axiom_from_UI_typed)
  have d_neg_true_app:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_negation_operator ObjTrue"
    using d_neg_true_raw
    by (simp add: pp_negation_operator_def subst0_def shift_def)
  have app_imp_neg:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (App pp_negation_operator ObjTrue) (Neg ObjTrue)"
  proof -
    have app_true_type:
      "\<Gamma> \<turnstile> App pp_negation_operator ObjTrue : Prop"
      using typed_pp_negation_operator typed_ObjTrue
      unfolding pp_unary_ty_def by (rule has_type.App)
    have neg_true_type: "\<Gamma> \<turnstile> Neg ObjTrue : Prop"
      using typed_ObjTrue by (rule has_type.Neg)
    have equiv:
      "\<Gamma> \<turnstile>\<^sub>CEV
        (App pp_negation_operator ObjTrue
          \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
      using app_true_type neg_true_type pp_negation_apply_beta
      by (rule CEV_beta_step)
    show ?thesis
      using app_true_type neg_true_type equiv
      by (rule CEV_beta_left_imp)
  qed
  have d_neg_true:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ObjTrue"
    using d_neg_true_app
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF app_imp_neg]]
    by (rule CEV_axiom_from.MP)
  have d_true:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    using CEV_axiom_proves_ObjTrue by (rule CEV_axiom_from.Theorem)
  have d_false:
    "\<Gamma> ; T ; insert ?A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_true d_neg_true by (rule CEV_axiom_from_contradiction)
  have A_imp_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?A ObjFalse"
    using A_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using A_imp_false to_neg by (rule CEV_axiom_from.MP)
qed

lemma CEV_complement_pair_reflexive_box:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    \<box>\<^sub>o (App (pp_complement_pair_operator r) r)"
proof -
  let ?F = "pp_complement_pair_operator r"
  let ?L = "\<box>\<^sub>o (r \<longleftrightarrow>\<^sub>o r)"
  let ?R = "\<box>\<^sub>o (r \<longleftrightarrow>\<^sub>o (Neg r))"
  let ?B = "Disj ?L ?R"
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using r_type by (rule typed_pp_complement_pair_operator)
  have app_type: "\<Gamma> \<turnstile> App ?F r : Prop"
    using F_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have iff_type: "\<Gamma> \<turnstile> (r \<longleftrightarrow>\<^sub>o r) : Prop"
    using r_type by (intro has_type.Conj has_type.Imp)
  have refl: "\<Gamma> \<turnstile>\<^sub>CEV (r \<longleftrightarrow>\<^sub>o r)"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    show "prop_tautology \<Gamma> (r \<longleftrightarrow>\<^sub>o r)"
      unfolding prop_tautology_def
      using r_type by (auto simp: prop_eval.simps)
  qed
  have box_refl: "\<Gamma> \<turnstile>\<^sub>CEV ?L"
    using refl by (rule CEV_necessitation)
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using iff_type by (rule typed_ObjBox)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type
    by (intro typed_ObjBox has_type.Conj has_type.Imp has_type.Neg)
  have intro: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?L ?B"
    using L_type R_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_disj_left_intro)
  have body: "\<Gamma> \<turnstile>\<^sub>CEV ?B"
    using box_refl intro by (rule CEV_proves.MP)
  have beta:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?F r \<longleftrightarrow>\<^sub>o ?B)"
    using app_type has_type.Disj[OF L_type R_type]
      pp_complement_pair_operator_beta
    by (rule CEV_beta_step)
  have body_to_app: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?B (App ?F r)"
    using app_type has_type.Disj[OF L_type R_type] beta
    by (rule CEV_beta_right_imp)
  have app: "\<Gamma> \<turnstile>\<^sub>CEV App ?F r"
    using body body_to_app by (rule CEV_proves.MP)
  show ?thesis
    using CEV_axiom_proves.Base[OF app]
    by (rule CEV_axiom_necessitation)
qed

theorem CEV_complement_pair_not_pure_at_fundamental:
  assumes background: "pp_recombination_background_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop r)
      (Neg
        (pp_pure pp_unary_ty
          (pp_complement_pair_operator r)))"
proof -
  let ?F = "pp_complement_pair_operator r"
  let ?P = "pp_pure pp_unary_ty ?F"
  let ?R = "pp_fun Prop r"
  let ?S = "{?P, ?R}"
  let ?L = "\<box>\<^sub>o (ObjTrue \<longleftrightarrow>\<^sub>o r)"
  let ?Q = "\<box>\<^sub>o (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r))"
  let ?B = "Disj ?L ?Q"
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using r_type by (rule typed_pp_complement_pair_operator)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using F_type by (rule typed_pp_pure)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_fun)
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_R:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using R_type by (intro CEV_axiom_from.Assumption) simp
  have pair:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?P ?R"
    using d_P d_R by (rule CEV_axiom_from_conj_intro)
  have recombination:
    "pp_unary_recombination \<in> T"
    using background pp_unary_recombination_in_recombination_background
    by blast
  have rec_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj ?P ?R)
        (Imp
          (\<box>\<^sub>o (App ?F r))
          (Forall Prop (App (shift ?F) (Var 0))))"
    using CEV_axiom_unary_recombination_instance[
      OF recombination F_type r_type]
    by (rule CEV_axiom_from.Theorem)
  have rec_tail:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (\<box>\<^sub>o (App ?F r))
        (Forall Prop (App (shift ?F) (Var 0)))"
    using pair rec_rule by (rule CEV_axiom_from.MP)
  have box_at_r:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (App ?F r)"
    using CEV_complement_pair_reflexive_box[OF r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_all:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop (App (shift ?F) (Var 0))"
    using box_at_r rec_tail by (rule CEV_axiom_from.MP)
  have all_type:
    "\<Gamma> \<turnstile> Forall Prop (App (shift ?F) (Var 0)) : Prop"
    using d_all by (rule CEV_axiom_from_formula)
  have d_true_raw:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 ObjTrue (App (shift ?F) (Var 0))"
    using all_type typed_ObjTrue d_all
    by (rule CEV_axiom_from_UI_typed)
  have cancel_F:
    "subst (case_nat ObjTrue Var) (shift ?F) = ?F"
    using subst0_shift[of ObjTrue ?F]
    unfolding subst0_def .
  have d_at_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App ?F ObjTrue"
    using d_true_raw cancel_F by (simp add: subst0_def)
  have true_iff_r_type:
    "\<Gamma> \<turnstile> (ObjTrue \<longleftrightarrow>\<^sub>o r) : Prop"
    using typed_ObjTrue r_type
    by (intro has_type.Conj has_type.Imp)
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using true_iff_r_type by (rule typed_ObjBox)
  have nr_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have true_iff_nr_type:
    "\<Gamma> \<turnstile> (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r)) : Prop"
    using typed_ObjTrue nr_type
    by (intro has_type.Conj has_type.Imp)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using true_iff_nr_type by (rule typed_ObjBox)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using L_type Q_type by (rule has_type.Disj)
  have app_true_type: "\<Gamma> \<turnstile> App ?F ObjTrue : Prop"
    using F_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have beta:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?F ObjTrue \<longleftrightarrow>\<^sub>o ?B)"
    using app_true_type B_type pp_complement_pair_operator_beta
    by (rule CEV_beta_step)
  have app_to_body:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?F ObjTrue) ?B"
    using app_true_type B_type beta by (rule CEV_beta_left_imp)
  have d_B:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
    using d_at_true
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF app_to_body]]
    by (rule CEV_axiom_from.MP)
  have not_box_r:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (\<box>\<^sub>o r)"
    using background r_type d_R
    by (rule CEV_axiom_from_fundamental_not_box)
  have not_box_nr:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (\<box>\<^sub>o (Neg r))"
    using background r_type d_R
    by (rule CEV_axiom_from_fundamental_not_box_neg)
  have left_to_r:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r"
  proof -
    have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ObjTrue
          (Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r)"
    proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
      show "prop_tautology \<Gamma>
        (Imp ObjTrue
          (Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r))"
      proof -
        have formula_type:
          "\<Gamma> \<turnstile>
            Imp ObjTrue
              (Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r) : Prop"
          using typed_ObjTrue r_type
          by (intro has_type.Imp has_type.Conj)
        moreover have
          "\<forall>v. prop_eval v
            (Imp ObjTrue
              (Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r))"
          by (simp only: prop_eval.simps) blast
        ultimately show ?thesis
          unfolding prop_tautology_def by blast
      qed
    qed
    show ?thesis
      using CEV_proves_ObjTrue taut by (rule CEV_proves.MP)
  qed
  have box_left_to_r:
    "\<Gamma> ; T ; insert ?L ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp (ObjTrue \<longleftrightarrow>\<^sub>o r) r)"
    using CEV_axiom_necessitation[
      OF CEV_axiom_proves.Base[OF left_to_r]]
    by (rule CEV_axiom_from.Theorem)
  have d_L:
    "\<Gamma> ; T ; insert ?L ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?L"
    using L_type by (intro CEV_axiom_from.Assumption) simp
  have box_r_left:
    "\<Gamma> ; T ; insert ?L ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o r"
    using
      true_iff_r_type
      r_type box_left_to_r d_L
    by (rule CEV_axiom_from_box_MP)
  have not_box_r_left:
    "\<Gamma> ; T ; insert ?L ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (\<box>\<^sub>o r)"
    using not_box_r by (rule CEV_axiom_from_mono) blast
  have false_left:
    "\<Gamma> ; T ; insert ?L ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using box_r_left not_box_r_left
    by (rule CEV_axiom_from_contradiction)
  have right_to_nr:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r)) (Neg r)"
  proof -
    have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ObjTrue
          (Imp
            (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r))
            (Neg r))"
    proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
      show "prop_tautology \<Gamma>
        (Imp ObjTrue
          (Imp
            (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r))
            (Neg r)))"
      proof -
        have formula_type:
          "\<Gamma> \<turnstile>
            Imp ObjTrue
              (Imp
                (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r))
                (Neg r)) : Prop"
          using typed_ObjTrue r_type
          by (intro has_type.Imp has_type.Conj has_type.Neg)
        moreover have
          "\<forall>v. prop_eval v
            (Imp ObjTrue
              (Imp
                (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r))
                (Neg r)))"
          by (simp only: prop_eval.simps) blast
        ultimately show ?thesis
          unfolding prop_tautology_def by blast
      qed
    qed
    show ?thesis
      using CEV_proves_ObjTrue taut by (rule CEV_proves.MP)
  qed
  have box_right_to_nr:
    "\<Gamma> ; T ; insert ?Q ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o
        (Imp (ObjTrue \<longleftrightarrow>\<^sub>o (Neg r)) (Neg r))"
    using CEV_axiom_necessitation[
      OF CEV_axiom_proves.Base[OF right_to_nr]]
    by (rule CEV_axiom_from.Theorem)
  have d_Q:
    "\<Gamma> ; T ; insert ?Q ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
    using Q_type by (intro CEV_axiom_from.Assumption) simp
  have box_nr_right:
    "\<Gamma> ; T ; insert ?Q ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Neg r)"
    using
      true_iff_nr_type
      nr_type box_right_to_nr d_Q
    by (rule CEV_axiom_from_box_MP)
  have not_box_nr_right:
    "\<Gamma> ; T ; insert ?Q ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (\<box>\<^sub>o (Neg r))"
    using not_box_nr by (rule CEV_axiom_from_mono) blast
  have false_right:
    "\<Gamma> ; T ; insert ?Q ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using box_nr_right not_box_nr_right
    by (rule CEV_axiom_from_contradiction)
  have d_false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using L_type Q_type typed_ObjFalse d_B false_left false_right
    by (rule CEV_axiom_from_T5_disj_cases)
  have under_P:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ObjFalse"
    using P_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?P ObjFalse) (Neg ?P)"
    using CEV_proves_imp_false_to_neg[OF P_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_not_P:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using under_P to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using R_type d_not_P by (rule CEV_axiom_from_singleton_imp)
qed

corollary CEV_recombination_complement_pair_not_pure:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; pp_recombination_background_axioms
      \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop r)
      (Neg
        (pp_pure pp_unary_ty
          (pp_complement_pair_operator r)))"
  using subset_refl r_type
  by (rule CEV_complement_pair_not_pure_at_fundamental)

subsection \<open>What the full CEV+ theory adds\<close>

text \<open>
  The full zeroary-and-unary QLN theory with PP gets strictly closer to the
  forbidden purity premise.  QSS is derivable there; hence every fundamental
  proposition is \<open>fun\<acute>\<close>.  Goodman T2d then makes the fundamental
  proposition possibly pure.  Since the complement-pair construction is a
  closed logical builder, possible purity lifts to possible purity of
  \<open>B\<^sup>\<plusminus>(r)\<close>.  Recombination nevertheless proves that this operator is not
  actually pure.  Thus the exact profile delivered by the full theory is
  \[
    Fun(r) \longrightarrow
      \bigl(\neg Pure(B^\pm(r))
        \mathbin{\land} \Diamond Pure(B^\pm(r))\bigr).
  \]
\<close>

lemma pp_recombination_background_subset_full_QLN_PP:
  "pp_recombination_background_axioms
    \<subseteq> pp_full_QLN_PP_axioms"
  unfolding pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def by blast

lemma pp_recombination_zeroary_exhaustion_subset_full_QLN_PP:
  "pp_recombination_zeroary_exhaustion_axioms
    \<subseteq> pp_full_QLN_PP_axioms"
  unfolding pp_recombination_zeroary_exhaustion_axioms_def
    pp_recombination_PP_axioms_def pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def pp_exhaustion_axioms_def
  by blast

lemma pp_T6_core_subset_full_QLN_PP:
  "pp_T6_core_PP_axioms \<subseteq> pp_full_QLN_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
  by blast

theorem CEV_full_QLN_complement_pair_profile:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop r)
      (Conj
        (Neg
          (pp_pure pp_unary_ty
            (pp_complement_pair_operator r)))
        (\<diamond>\<^sub>o
          (pp_pure pp_unary_ty
            (pp_complement_pair_operator r))))"
proof -
  let ?T = pp_full_QLN_PP_axioms
  let ?R = "pp_fun Prop r"
  let ?PR = "pp_pure Prop r"
  let ?F = "pp_complement_pair_operator r"
  let ?PF = "pp_pure pp_unary_ty ?F"
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_fun)
  have PR_type: "\<Gamma> \<turnstile> ?PR : Prop"
    using r_type by (rule typed_pp_pure)
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using r_type by (rule typed_pp_complement_pair_operator)
  have PF_type: "\<Gamma> \<turnstile> ?PF : Prop"
    using F_type by (rule typed_pp_pure)
  have d_R:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using R_type by (intro CEV_axiom_from.Assumption) simp
  have qss:
    "\<And>\<Delta>. \<Delta> ; ?T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
  proof -
    fix \<Delta>
    show "\<Delta> ; ?T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
      using
        CEV_QSS_from_recombination_with_zeroary_exhaustion[
          where \<Gamma> = \<Delta>]
        pp_recombination_zeroary_exhaustion_subset_full_QLN_PP
      by (rule CEV_axiom_proves_mono)
  qed
  have fun_prime_rule:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_fun Prop r) (pp_fun_prime r)"
    using CEV_fun_prime_from_contextual_QSS[OF qss r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_fun_prime:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
    using d_R fun_prime_rule by (rule CEV_axiom_from.MP)
  have possibly_pure_rule:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_fun_prime r) (\<diamond>\<^sub>o ?PR)"
    using CEV_Goodman_T2d[
      OF pp_T6_core_subset_full_QLN_PP r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_possibly_pure_r:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?PR"
    using d_fun_prime possibly_pure_rule
    by (rule CEV_axiom_from.MP)
  have pure_bridge:
    "\<Gamma> ; ?T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?PR ?PF"
    using pp_recombination_background_subset_full_QLN_PP r_type
    by (rule CEV_complement_pair_pure_if_parameter_pure)
  have diamond_bridge:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<diamond>\<^sub>o ?PR) (\<diamond>\<^sub>o ?PF)"
    using CEV_axiom_diamond_mono[
      OF PR_type PF_type pure_bridge]
    by (rule CEV_axiom_from.Theorem)
  have d_possibly_pure_F:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?PF"
    using d_possibly_pure_r diamond_bridge
    by (rule CEV_axiom_from.MP)
  have not_pure_rule:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?R (Neg ?PF)"
    using CEV_complement_pair_not_pure_at_fundamental[
      OF pp_recombination_background_subset_full_QLN_PP r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_not_pure_F:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?PF"
    using d_R not_pure_rule by (rule CEV_axiom_from.MP)
  have profile:
    "\<Gamma> ; ?T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (Neg ?PF) (\<diamond>\<^sub>o ?PF)"
    using d_not_pure_F d_possibly_pure_F
    by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using R_type profile by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_complement_pair_actual_purity_would_close:
  assumes background: "pp_recombination_background_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and purity_bridge:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun Prop r)
          (pp_pure pp_unary_ty
            (pp_complement_pair_operator r))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun Prop r) ObjFalse"
proof -
  let ?R = "pp_fun Prop r"
  let ?P =
    "pp_pure pp_unary_ty
      (pp_complement_pair_operator r)"
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_fun)
  have F_type:
    "\<Gamma> \<turnstile> pp_complement_pair_operator r : pp_unary_ty"
    using r_type by (rule typed_pp_complement_pair_operator)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using F_type by (rule typed_pp_pure)
  have d_R:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using R_type by (intro CEV_axiom_from.Assumption) simp
  have bridge_local:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?R ?P"
    using purity_bridge by (rule CEV_axiom_from.Theorem)
  have d_P:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using d_R bridge_local by (rule CEV_axiom_from.MP)
  have obstruction:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?R (Neg ?P)"
    using CEV_complement_pair_not_pure_at_fundamental[
      OF background r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_not_P:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using d_R obstruction by (rule CEV_axiom_from.MP)
  have d_false:
    "\<Gamma> ; T ; {?R} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_P d_not_P by (rule CEV_axiom_from_contradiction)
  show ?thesis
    using R_type d_false by (rule CEV_axiom_from_singleton_imp)
qed

end
