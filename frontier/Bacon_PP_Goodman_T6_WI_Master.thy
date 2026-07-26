theory Bacon_PP_Goodman_T6_WI_Master
  imports Bacon_PP_Goodman_T6_WI
begin

section \<open>Goodman's advertised T6-WI master family\<close>

text \<open>
  Goodman writes \<open>d = Dr\<close> and, for pure propositions \<open>A\<close>,
  \<open>a\<^sub>A = D(d \<longleftrightarrow> A)\<close>.  The advertised master equation is

    \<open>a\<^sub>A \<longleftrightarrow> \<forall>C (Pure(C) \<longrightarrow>
      (a\<^sub>C \<longleftrightarrow> \<not>A))\<close>.

  We first isolate the logical content of that family for an arbitrary
  proposition-indexed operator \<open>a\<close>.  This keeps the propositional
  inconsistency separate from the harder derivation of the equation from
  WI, L2, and the liar matrix.
\<close>

definition pp_T6_WI_master_at ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_master_at a A =
    (App a A \<longleftrightarrow>\<^sub>o
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))))"

definition pp_T6_WI_master_family :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_master_family a =
    Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_master_at (shift a) (Var 0)))"

definition pp_T6_WI_a :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_a r A =
    App pp_T6_liar
      (App (pp_biconditional_operator A)
        (App pp_T6_liar r))"

definition pp_T6_WI_a_operator :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_a_operator r =
    Lam Prop (pp_T6_WI_a (shift r) (Var 0))"

definition pp_T6_WI_advertised_master :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_advertised_master r =
    pp_T6_WI_master_family (pp_T6_WI_a_operator r)"

lemma typed_pp_T6_WI_master_at:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_master_at a A : Prop"
proof -
  have aA_type: "\<Gamma> \<turnstile> App a A : Prop"
    using a_type A_type by (rule has_type.App)
  have a_shift_type:
    "Prop # \<Gamma> \<turnstile> shift a : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have A_shift_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule typed_shift_ctx)
  have C_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have pure_C_type:
    "Prop # \<Gamma> \<turnstile> pp_pure Prop (Var 0) : Prop"
    using C_type by (rule typed_pp_pure)
  have aC_type: "Prop # \<Gamma> \<turnstile> App (shift a) (Var 0) : Prop"
    using a_shift_type C_type by (rule has_type.App)
  have matrix_type:
    "Prop # \<Gamma> \<turnstile>
      Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift A)) : Prop"
    using pure_C_type aC_type A_shift_type
    by (intro has_type.Imp has_type.Conj has_type.Neg)
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))) : Prop"
    using matrix_type by (rule has_type.Forall)
  show ?thesis
    unfolding pp_T6_WI_master_at_def
    using aA_type rhs_type
    by (intro has_type.Conj has_type.Imp)
qed

lemma typed_pp_T6_WI_master_family:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_master_family a : Prop"
proof -
  have a_shift_type:
    "Prop # \<Gamma> \<turnstile> shift a : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T6_WI_master_family_def
    using typed_pp_pure[OF A_type]
      typed_pp_T6_WI_master_at[OF a_shift_type A_type]
    by (intro has_type.Forall has_type.Imp)
qed

lemma typed_pp_T6_WI_a:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_a r A : Prop"
proof -
  have D_type: "\<Gamma> \<turnstile> pp_T6_liar : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> App pp_T6_liar r : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have B_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator A : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have Bd_type:
    "\<Gamma> \<turnstile>
      App (pp_biconditional_operator A) (App pp_T6_liar r) : Prop"
    using B_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T6_WI_a_def
    using D_type Bd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
qed

lemma typed_pp_T6_WI_a_operator:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_a_operator r : Prop \<rightarrow>\<^sub>o Prop"
proof -
  have r_shift_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T6_WI_a_operator_def
    using typed_pp_T6_WI_a[OF r_shift_type A_type]
    by (rule has_type.Lam)
qed

lemma typed_pp_T6_WI_advertised_master:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_advertised_master r : Prop"
  unfolding pp_T6_WI_advertised_master_def
  using typed_pp_T6_WI_a_operator[OF r_type]
  by (rule typed_pp_T6_WI_master_family)

lemma subst_pp_T6_WI_master_at[simp]:
  "subst s (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (subst s a) (subst s A)"
  by (simp add: pp_T6_WI_master_at_def subst_lift_shift)

lemma rename_pp_T6_WI_master_at[simp]:
  "rename r (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (rename r a) (rename r A)"
  by (simp add: pp_T6_WI_master_at_def shift_rename_lift)

lemma shift_pp_T6_WI_master_at[simp]:
  "shift (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (shift a) (shift A)"
  by (simp add: shift_def)

lemma rename_pp_T6_WI_master_family[simp]:
  "rename r (pp_T6_WI_master_family a) =
    pp_T6_WI_master_family (rename r a)"
  by (simp add: pp_T6_WI_master_family_def shift_rename_lift)

lemma shift_pp_T6_WI_master_family[simp]:
  "shift (pp_T6_WI_master_family a) =
    pp_T6_WI_master_family (shift a)"
  by (simp add: shift_def)

lemma CEV_axiom_master_family_instance:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T6_WI_master_at a A"
proof -
  have family_type:
    "\<Gamma> \<turnstile> pp_T6_WI_master_family a : Prop"
    using a_type by (rule typed_pp_T6_WI_master_family)
  have raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 A
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_master_at (shift a) (Var 0)))"
    using family_type A_type family
    unfolding pp_T6_WI_master_family_def
    by (rule CEV_axiom_from_UI_typed)
  have inst:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_pure Prop A) (pp_T6_WI_master_at a A)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of A a, unfolded subst0_def])
  show ?thesis
    using pure_A inst by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_master_rhs_instance:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and rhs:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
              Neg (shift A)))"
    and pure_C:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (App a C \<longleftrightarrow>\<^sub>o Neg A)"
proof -
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))) : Prop"
    using typed_pp_T6_WI_master_at[OF a_type A_type]
    unfolding pp_T6_WI_master_at_def
    by (auto elim: has_type.cases)
  have raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 C
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A)))"
    using rhs_type C_type rhs by (rule CEV_axiom_from_UI_typed)
  have inst:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_pure Prop C)
        (App a C \<longleftrightarrow>\<^sub>o Neg A)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of C a, unfolded subst0_def]
        subst0_shift[of C A, unfolded subst0_def])
  show ?thesis
    using pure_C inst by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_prop_tautology:
  assumes taut: "prop_tautology \<Gamma> A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  using CEV_prop_tautology[OF taut]
  by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)

lemma CEV_axiom_from_master_not_top:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (App a ObjTrue)"
proof -
  let ?aT = "App a ObjTrue"
  let ?RT =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift ObjTrue)))"
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have master_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a ObjTrue"
    using a_type typed_ObjTrue family pure_top
    by (rule CEV_axiom_master_family_instance)
  have aT_to_RT:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ?RT"
    using master_top
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_left)
  let ?S' = "insert ?aT S"
  have d_aT: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aT"
    using aT_type by (intro CEV_axiom_from.Assumption) simp
  have d_RT: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RT"
  proof -
    have d_imp:
      "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ?RT"
      using aT_to_RT by (rule CEV_axiom_from_mono) blast
    show ?thesis
      using d_aT d_imp by (rule CEV_axiom_from.MP)
  qed
  have pure_top':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
    using pure_top by (rule CEV_axiom_from_mono) blast
  have top_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aT \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using a_type typed_ObjTrue typed_ObjTrue d_RT pure_top'
    by (rule CEV_axiom_master_rhs_instance)
  have aT_to_not_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?aT (Neg ObjTrue)"
    using top_bicond by (rule CEV_axiom_from_conj_left)
  have not_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ObjTrue"
    using d_aT aT_to_not_true by (rule CEV_axiom_from.MP)
  have d_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves_ObjTrue)
  have d_false:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_true not_true by (rule CEV_axiom_from_contradiction)
  have aT_to_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ObjFalse"
    using aT_type d_false by (rule CEV_axiom_from_deduction)
  have convert:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?aT ObjFalse) (Neg ?aT)"
    using CEV_proves_imp_false_to_neg[OF aT_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using aT_to_false convert by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_master_not_a:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App a A)"
proof -
  let ?aA = "App a A"
  let ?aT = "App a ObjTrue"
  let ?RA =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift A)))"
  have aA_type: "\<Gamma> \<turnstile> ?aA : Prop"
    using a_type A_type by (rule has_type.App)
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have master_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a A"
    using a_type A_type family pure_A
    by (rule CEV_axiom_master_family_instance)
  have aA_to_RA:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ?RA"
    using master_A
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_left)
  have not_aT:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using a_type pure_top_in family
    by (rule CEV_axiom_from_master_not_top)
  let ?S' = "insert ?aA S"
  have d_aA: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aA"
    using aA_type by (intro CEV_axiom_from.Assumption) simp
  have d_RA: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RA"
  proof -
    have d_imp:
      "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ?RA"
      using aA_to_RA by (rule CEV_axiom_from_mono) blast
    show ?thesis
      using d_aA d_imp by (rule CEV_axiom_from.MP)
  qed
  have pure_top':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
    using pure_top by (rule CEV_axiom_from_mono) blast
  have pure_A':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
    using pure_A by (rule CEV_axiom_from_mono) blast
  have top_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aT \<longleftrightarrow>\<^sub>o Neg A)"
    using a_type A_type typed_ObjTrue d_RA pure_top'
    by (rule CEV_axiom_master_rhs_instance)
  have not_aT':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using not_aT by (rule CEV_axiom_from_mono) blast
  have recover_A_taut:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg ?aT)
        (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A)"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (Neg ?aT)
        (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp (Neg ?aT)
          (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A) : Prop"
        using aT_type A_type
        by (intro has_type.Imp has_type.Neg has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp (Neg ?aT)
          (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A))"
        by (simp add: prop_eval.simps)
    qed
  qed
  have recover_A_step:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A"
    using not_aT' recover_A_taut by (rule CEV_axiom_from.MP)
  have d_A: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using top_bicond recover_A_step by (rule CEV_axiom_from.MP)
  have self_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aA \<longleftrightarrow>\<^sub>o Neg A)"
    using a_type A_type A_type d_RA pure_A'
    by (rule CEV_axiom_master_rhs_instance)
  have aA_to_not_A:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA (Neg A)"
    using self_bicond by (rule CEV_axiom_from_conj_left)
  have not_A: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    using d_aA aA_to_not_A by (rule CEV_axiom_from.MP)
  have d_false:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_A not_A by (rule CEV_axiom_from_contradiction)
  have aA_to_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ObjFalse"
    using aA_type d_false by (rule CEV_axiom_from_deduction)
  have convert:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?aA ObjFalse) (Neg ?aA)"
    using CEV_proves_imp_false_to_neg[OF aA_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using aA_to_false convert by (rule CEV_axiom_from.MP)
qed

theorem CEV_T6_WI_master_family_inconsistent:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_T6_WI_master_family a"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?F = "pp_T6_WI_master_family a"
  let ?aT = "App a ObjTrue"
  let ?RT =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift ObjTrue)))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using a_type by (rule typed_pp_T6_WI_master_family)
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have family_local:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using family by (rule CEV_axiom_from.Theorem)
  have master_top:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a ObjTrue"
    using a_type typed_ObjTrue family_local pure_top
    by (rule CEV_axiom_master_family_instance)
  have RT_to_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?RT ?aT"
    using master_top
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_right)
  have not_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using a_type pure_top_in family_local
    by (rule CEV_axiom_from_master_not_top)

  let ?aS = "shift a"
  let ?FS = "shift ?F"
  let ?C = "Var 0"
  let ?PC = "pp_pure Prop ?C"
  let ?aC = "App ?aS ?C"
  let ?Q = "Imp ?PC (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
  have aS_type:
    "Prop # \<Gamma> \<turnstile> ?aS : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have C_type: "Prop # \<Gamma> \<turnstile> ?C : Prop"
    by (rule typed_var0)
  have PC_type: "Prop # \<Gamma> \<turnstile> ?PC : Prop"
    using C_type by (rule typed_pp_pure)
  have aC_type: "Prop # \<Gamma> \<turnstile> ?aC : Prop"
    using aS_type C_type by (rule has_type.App)
  have FS_type: "Prop # \<Gamma> \<turnstile> ?FS : Prop"
    using F_type by (rule typed_shift_ctx)
  have family_shift:
    "?FS = pp_T6_WI_master_family ?aS"
    by simp
  let ?S2 = "insert ?PC {?FS}"
  have d_FS:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_family ?aS"
  proof -
    have raw:
      "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FS"
      using FS_type by (intro CEV_axiom_from.Assumption) simp
    show ?thesis
      using raw family_shift by simp
  qed
  have d_PC:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have not_aC:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aC"
    using aS_type C_type pure_top_in d_FS d_PC
    by (rule CEV_axiom_from_master_not_a)
  have bicond_taut:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg ?aC)
        (Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue))"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp (Neg ?aC)
        (Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)))"
    proof (unfold prop_tautology_def, intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp (Neg ?aC)
          (Imp ObjTrue
            (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)) : Prop"
        using aC_type typed_ObjTrue
        by (intro has_type.Imp has_type.Neg has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp (Neg ?aC)
          (Imp ObjTrue
            (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)))"
        by (simp add: prop_eval.simps)
    qed
  qed
  have bicond_step:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using not_aC bicond_taut by (rule CEV_axiom_from.MP)
  have d_true:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves_ObjTrue)
  have d_bicond:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using d_true bicond_step by (rule CEV_axiom_from.MP)
  have under_FS:
    "Prop # \<Gamma> ; T ; {?FS} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?PC : Prop"
      by (rule PC_type)
    show "Prop # \<Gamma> ; T ; insert ?PC {?FS}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
      by (rule d_bicond)
  qed
  have empty_local:
    "Prop # \<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?FS ?Q"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?FS : Prop"
      by (rule FS_type)
    show "Prop # \<Gamma> ; T ; insert ?FS {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
      using under_FS by simp
  qed
  have shifted_guard:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?F) ?Q"
    using empty_local CEV_axiom_from_empty_iff by blast
  have rhs_guard:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Forall Prop ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?F : Prop" by (rule F_type)
    show "Prop # \<Gamma> \<turnstile> ?Q : Prop"
      using PC_type aC_type typed_ObjTrue
      by (intro has_type.Imp has_type.Conj has_type.Neg)
    show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?F) ?Q"
      by (rule shifted_guard)
  qed
  have d_RT_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?Q"
    using family rhs_guard by (rule CEV_axiom_proves.MP)
  have d_RT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RT"
    using d_RT_raw
    by (intro CEV_axiom_from.Theorem)
      (simp add: shift_def ObjTrue_def)
  have d_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aT"
    using d_RT RT_to_aT by (rule CEV_axiom_from.MP)
  have d_false:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_aT not_aT by (rule CEV_axiom_from_contradiction)
  show ?thesis
    using d_false CEV_axiom_from_empty_iff by blast
qed

corollary CEV_T6_WI_advertised_master_inconsistent:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and core: "pp_T6_core_PP_axioms \<subseteq> T"
    and master:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_T6_WI_advertised_master r"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  have pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    using pp_ObjTrue_purity_axiom core
    unfolding pp_T6_core_PP_axioms_def by blast
  have a_type:
    "\<Gamma> \<turnstile> pp_T6_WI_a_operator r : Prop \<rightarrow>\<^sub>o Prop"
    using r_type by (rule typed_pp_T6_WI_a_operator)
  have family:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_T6_WI_master_family (pp_T6_WI_a_operator r)"
    using master unfolding pp_T6_WI_advertised_master_def .
  show ?thesis
    using a_type pure_top_in family
    by (rule CEV_T6_WI_master_family_inconsistent)
qed

end
