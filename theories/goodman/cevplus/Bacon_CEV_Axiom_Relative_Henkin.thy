theory Bacon_CEV_Axiom_Relative_Henkin
  imports Bacon_PP_Fresh_Relative_Lindenbaum
begin

section \<open>Fresh witnesses above a fixed stock of added principles\<close>

text \<open>
  A Henkin witness may be added as a temporary assumption above a fixed
  stock of added principles only when its new constant is fresh from both
  stocks.  The proof also uses the fact that the added principles are closed
  formulas, so renaming the free variables of a derivation leaves them fixed.
\<close>

lemma rename_typed_term_if_fixed:
  assumes typed: "\<Gamma> \<turnstile> A : \<tau>"
    and fixed: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> r n = n"
  shows "rename r A = A"
  using typed fixed
proof (induction arbitrary: r rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case by simp
next
  case (Const \<Gamma> c \<tau>)
  then show ?case by simp
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  then show ?case by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have fixed_lift:
    "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_ren r n = n"
    using Lam.prems by (case_tac n; simp)
  have "rename (lift_ren r) M = M"
    using fixed_lift by (rule Lam.IH)
  then show ?case by simp
next
  case (Eq \<Gamma> M \<sigma> N)
  then show ?case by simp
next
  case (Neg \<Gamma> A)
  then show ?case by simp
next
  case (Conj \<Gamma> A B)
  then show ?case by simp
next
  case (Disj \<Gamma> A B)
  then show ?case by simp
next
  case (Imp \<Gamma> A B)
  then show ?case by simp
next
  case (Forall \<sigma> \<Gamma> A)
  have fixed_lift:
    "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_ren r n = n"
    using Forall.prems by (case_tac n; simp)
  have "rename (lift_ren r) A = A"
    using fixed_lift by (rule Forall.IH)
  then show ?case by simp
next
  case (Exists \<sigma> \<Gamma> A)
  have fixed_lift:
    "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_ren r n = n"
    using Exists.prems by (case_tac n; simp)
  have "rename (lift_ren r) A = A"
    using fixed_lift by (rule Exists.IH)
  then show ?case by simp
qed

lemma rename_typed_closed_term:
  assumes "[] \<turnstile> A : \<tau>"
  shows "rename r A = A"
proof (rule rename_typed_term_if_fixed[OF assms])
  fix n \<rho>
  assume "lookup [] n = Some \<rho>"
  then show "r n = n" by (simp add: lookup_def)
qed

definition CEV_closed_axiom_stock :: "oterm set \<Rightarrow> bool" where
  "CEV_closed_axiom_stock T \<longleftrightarrow>
    (\<forall>r A. A \<in> T \<longrightarrow> rename r A = A)"

lemma typed_theory_empty_imp_CEV_closed_axiom_stock:
  assumes "typed_theory [] T"
  shows "CEV_closed_axiom_stock T"
  using assms rename_typed_closed_term
  unfolding typed_theory_def CEV_closed_axiom_stock_def
  by blast

lemma CEV_axiom_proves_rename_closed:
  assumes derivation: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and mapping:
      "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
        lookup \<Delta> (r n) = Some \<tau>"
    and closed: "CEV_closed_axiom_stock T"
  shows "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ rename r A"
  using derivation mapping closed
proof (induction arbitrary: \<Delta> r rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  have stock_closed: "CEV_closed_axiom_stock T"
    using Axiom.prems by blast
  have all_fixed: "\<forall>q B. B \<in> T \<longrightarrow> rename q B = B"
    using stock_closed unfolding CEV_closed_axiom_stock_def by simp
  have A_fixed: "rename r A = A"
    using all_fixed Axiom.hyps(1) by blast
  have A_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Axiom.hyps(2) Axiom.prems(1)
    by (rule renaming_preserves_typing)
  show ?case
    using Axiom.hyps(1) A_type A_fixed
    by (intro CEV_axiom_proves.Axiom) simp_all
next
  case (Base \<Gamma> A T)
  have "\<Delta> \<turnstile>\<^sub>CEV rename r A"
    using Base.hyps Base.prems(1) by (rule CEV_proves_rename)
  then show ?case by (rule CEV_axiom_proves.Base)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  let ?r' = "prefix_ren (length \<sigma>s) r"
  have lift_rel:
    "\<And>n \<tau>. lookup (\<sigma>s @ \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<sigma>s @ \<Delta>) (?r' n) = Some \<tau>"
    using VectorEquivalence.prems(1)
    by (rule prefix_ren_preserves_lookup)
  have d_body:
    "\<sigma>s @ \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      rename ?r' (zeta_body \<sigma>s F G)"
    using lift_rel VectorEquivalence.prems(2)
    by (rule VectorEquivalence.IH)
  have F_type:
    "\<Delta> \<turnstile> rename r F : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(1) VectorEquivalence.prems(1)
    by (rule renaming_preserves_typing)
  have G_type:
    "\<Delta> \<turnstile> rename r G : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(2) VectorEquivalence.prems(1)
    by (rule renaming_preserves_typing)
  have d_zeta:
    "\<sigma>s @ \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      zeta_body \<sigma>s (rename r F) (rename r G)"
    using d_body by (simp add: rename_zeta_body_prefix)
  have "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq (arrow_type \<sigma>s Prop) (rename r F) (rename r G)"
    using F_type G_type d_zeta
    by (rule CEV_axiom_proves.VectorEquivalence)
  then show ?case by simp
next
  case (MP \<Gamma> T A B)
  have d_A: "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ rename r A"
    using MP.prems by (rule MP.IH(1))
  have d_imp_raw:
    "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have d_imp:
    "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (rename r A) (rename r B)"
    using d_imp_raw by simp
  show ?case using d_A d_imp by (rule CEV_axiom_proves.MP)
next
  case (Gen \<Gamma> P \<sigma> Q T)
  have lift_rel:
    "\<And>n \<tau>. lookup (\<sigma> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Gen.prems(1) by (rule lookup_lift_ren)
  have d_ext_raw:
    "\<sigma> # \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      rename (lift_ren r) (Imp (shift P) Q)"
    using lift_rel Gen.prems(2) by (rule Gen.IH)
  have d_ext:
    "\<sigma> # \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (rename r P)) (rename (lift_ren r) Q)"
    using d_ext_raw by (simp add: shift_rename_lift)
  have P_type: "\<Delta> \<turnstile> rename r P : Prop"
    using Gen.hyps(1) Gen.prems(1) by (rule renaming_preserves_typing)
  have Q_type: "\<sigma> # \<Delta> \<turnstile> rename (lift_ren r) Q : Prop"
    using Gen.hyps(2) lift_rel by (rule renaming_preserves_typing)
  have "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (rename r P) (Forall \<sigma> (rename (lift_ren r) Q))"
    using P_type Q_type d_ext by (rule CEV_axiom_proves.Gen)
  then show ?case by simp
next
  case (Inst \<sigma> \<Gamma> P Q T)
  have lift_rel:
    "\<And>n \<tau>. lookup (\<sigma> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Inst.prems(1) by (rule lookup_lift_ren)
  have d_ext_raw:
    "\<sigma> # \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      rename (lift_ren r) (Imp P (shift Q))"
    using lift_rel Inst.prems(2) by (rule Inst.IH)
  have d_ext:
    "\<sigma> # \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (rename (lift_ren r) P) (shift (rename r Q))"
    using d_ext_raw by (simp add: shift_rename_lift)
  have P_type: "\<sigma> # \<Delta> \<turnstile> rename (lift_ren r) P : Prop"
    using Inst.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have Q_type: "\<Delta> \<turnstile> rename r Q : Prop"
    using Inst.hyps(2) Inst.prems(1) by (rule renaming_preserves_typing)
  have "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists \<sigma> (rename (lift_ren r) P)) (rename r Q)"
    using P_type Q_type d_ext by (rule CEV_axiom_proves.Inst)
  then show ?case by simp
qed

lemma CEV_axiom_proves_subst_const_fresh_stock:
  assumes derivation: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and term_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and fresh: "c \<notin> consts_of_set T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst_const c \<sigma> N A"
  using derivation term_type fresh
proof (induction arbitrary: N \<sigma> c rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  have stock_fresh: "c \<notin> consts_of_set T"
    using Axiom.prems by blast
  have c_fresh_A: "c \<notin> consts_of A"
    using stock_fresh Axiom.hyps(1) consts_of_setI by blast
  have fixed: "subst_const c \<sigma> N A = A"
    using c_fresh_A by simp
  show ?case
    using Axiom.hyps(1,2) fixed
    by (metis CEV_axiom_proves.Axiom)
next
  case (Base \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N A"
    using Base.hyps Base.prems(1) by (rule CEV_proves_subst_const)
  then show ?case by (rule CEV_axiom_proves.Base)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  have shifted_N:
    "\<sigma>s @ \<Gamma> \<turnstile> shift_by (length \<sigma>s) N : \<sigma>"
    using VectorEquivalence.prems(1) by (rule shift_by_preserves_typing)
  have F_type:
    "\<Gamma> \<turnstile> subst_const c \<sigma> N F : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(1) VectorEquivalence.prems(1)
    by (rule subst_const_preserves_typing)
  have G_type:
    "\<Gamma> \<turnstile> subst_const c \<sigma> N G : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(2) VectorEquivalence.prems(1)
    by (rule subst_const_preserves_typing)
  have d_body_raw:
    "\<sigma>s @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst_const c \<sigma> (shift_by (length \<sigma>s) N)
        (zeta_body \<sigma>s F G)"
    using shifted_N VectorEquivalence.prems(2)
    by (rule VectorEquivalence.IH)
  have d_body:
    "\<sigma>s @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      zeta_body \<sigma>s (subst_const c \<sigma> N F)
        (subst_const c \<sigma> N G)"
    using d_body_raw by (simp add: subst_const_zeta_body)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq (arrow_type \<sigma>s Prop)
        (subst_const c \<sigma> N F) (subst_const c \<sigma> N G)"
    using F_type G_type d_body
    by (rule CEV_axiom_proves.VectorEquivalence)
  then show ?case by simp
next
  case (MP \<Gamma> T A B)
  have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have d_imp_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have d_imp:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using d_imp_raw by simp
  show ?case using d_A d_imp by (rule CEV_axiom_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q T)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Gen.prems(1) by (rule weakening_front)
  have P_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : Prop"
    using Gen.hyps(1) Gen.prems(1) by (rule subst_const_preserves_typing)
  have Q_type:
    "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) Q : Prop"
    using Gen.hyps(2) shifted_N by (rule subst_const_preserves_typing)
  have d_ext_raw:
    "\<rho> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst_const c \<sigma> (shift N) (Imp (shift P) Q)"
    using shifted_N Gen.prems(2) by (rule Gen.IH)
  have d_ext:
    "\<rho> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (subst_const c \<sigma> N P))
        (subst_const c \<sigma> (shift N) Q)"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (subst_const c \<sigma> N P)
        (Forall \<rho> (subst_const c \<sigma> (shift N) Q))"
    using P_type Q_type d_ext by (rule CEV_axiom_proves.Gen)
  then show ?case by simp
next
  case (Inst \<rho> \<Gamma> P Q T)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Inst.prems(1) by (rule weakening_front)
  have P_type:
    "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) P : Prop"
    using Inst.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have Q_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
    using Inst.hyps(2) Inst.prems(1) by (rule subst_const_preserves_typing)
  have d_ext_raw:
    "\<rho> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst_const c \<sigma> (shift N) (Imp P (shift Q))"
    using shifted_N Inst.prems(2) by (rule Inst.IH)
  have d_ext:
    "\<rho> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (subst_const c \<sigma> (shift N) P)
        (shift (subst_const c \<sigma> N Q))"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists \<rho> (subst_const c \<sigma> (shift N) P))
        (subst_const c \<sigma> N Q)"
    using P_type Q_type d_ext by (rule CEV_axiom_proves.Inst)
  then show ?case by simp
qed

lemma CEV_axiom_from_rename_closed:
  assumes derivation:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and mapping:
      "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
        lookup \<Delta> (r n) = Some \<tau>"
    and closed: "CEV_closed_axiom_stock T"
  shows "\<Delta> ; T ; rename r ` S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s rename r A"
  using derivation mapping closed
proof (induction arbitrary: \<Delta> r rule: CEV_axiom_from.induct)
  case (Assumption A S \<Gamma> T)
  have A_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Assumption.hyps(2) Assumption.prems(1)
    by (rule renaming_preserves_typing)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CEV_axiom_from.Assumption) auto
next
  case (Theorem \<Gamma> T A S)
  have "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ rename r A"
    using Theorem.hyps Theorem.prems
    by (rule CEV_axiom_proves_rename_closed)
  then show ?case by (rule CEV_axiom_from.Theorem)
next
  case (MP \<Gamma> T S A B)
  have d_A:
    "\<Delta> ; T ; rename r ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s rename r A"
    using MP.prems by (rule MP.IH(1))
  have d_imp_raw:
    "\<Delta> ; T ; rename r ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have d_imp:
    "\<Delta> ; T ; rename r ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (rename r A) (rename r B)"
    using d_imp_raw by simp
  show ?case using d_A d_imp by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_shift_closed:
  assumes derivation:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and closed: "CEV_closed_axiom_stock T"
  shows "\<sigma> # \<Gamma> ; T ; shift ` S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift A"
proof -
  have mapping:
    "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
      lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<tau>"
    by simp
  have "\<sigma> # \<Gamma> ; T ; rename Suc ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s rename Suc A"
    using derivation mapping closed
    by (rule CEV_axiom_from_rename_closed)
  then show ?thesis unfolding shift_def .
qed

lemma CEV_axiom_from_subst_const_fresh_stock:
  assumes derivation:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and term_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and fresh: "c \<notin> consts_of_set T"
  shows "\<Gamma> ; T ; subst_const c \<sigma> N ` S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst_const c \<sigma> N A"
  using derivation term_type fresh
proof (induction arbitrary: N \<sigma> c rule: CEV_axiom_from.induct)
  case (Assumption A S \<Gamma> T)
  have A_type:
    "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems(1)
    by (rule subst_const_preserves_typing)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CEV_axiom_from.Assumption) auto
next
  case (Theorem \<Gamma> T A S)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems
    by (rule CEV_axiom_proves_subst_const_fresh_stock)
  then show ?case by (rule CEV_axiom_from.Theorem)
next
  case (MP \<Gamma> T S A B)
  have d_A:
    "\<Gamma> ; T ; subst_const c \<sigma> N ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have d_imp_raw:
    "\<Gamma> ; T ; subst_const c \<sigma> N ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have d_imp:
    "\<Gamma> ; T ; subst_const c \<sigma> N ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using d_imp_raw by simp
  show ?case using d_A d_imp by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_abstract_const_fresh_stock:
  assumes derivation:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and closed: "CEV_closed_axiom_stock T"
    and fresh: "c \<notin> consts_of_set T"
  shows "\<sigma> # \<Gamma> ; T ; abstract_const c \<sigma> ` S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s abstract_const c \<sigma> A"
proof -
  have shifted:
    "\<sigma> # \<Gamma> ; T ; shift ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift A"
    using derivation closed by (rule CEV_axiom_from_shift_closed)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by simp
  have substituted:
    "\<sigma> # \<Gamma> ; T ;
      subst_const c \<sigma> (Var 0) ` (shift ` S)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        subst_const c \<sigma> (Var 0) (shift A)"
    using shifted var_type fresh
    by (rule CEV_axiom_from_subst_const_fresh_stock)
  have image_eq:
    "subst_const c \<sigma> (Var 0) ` (shift ` S) =
      abstract_const c \<sigma> ` S"
    unfolding abstract_const_def by auto
  show ?thesis
    using substituted image_eq unfolding abstract_const_def by simp
qed

lemma CEV_axiom_from_shifted_inst_list:
  assumes typed: "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and d:
      "\<sigma> # \<Gamma> ; T ; shift ` set \<Delta>
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T ; set \<Delta>
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Exists \<sigma> P) Q"
  using assms
proof (induction \<Delta> arbitrary: Q)
  case Nil
  have d_thm:
    "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
    using Nil.prems(2) CEV_axiom_from_empty_iff by simp
  have inst:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> P) Q"
    using Nil.prems(3,4) d_thm by (rule CEV_axiom_proves.Inst)
  then show ?case
    by (rule CEV_axiom_from.Theorem)
next
  case (Cons A \<Delta>)
  let ?E = "Exists \<sigma> P"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Cons.prems(1) by simp
  have tail_typed:
    "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(1) by simp
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Cons.prems(4) by (rule weakening_front)
  have d_cons:
    "\<sigma> # \<Gamma> ; T ; insert (shift A) (shift ` set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift Q)"
    using Cons.prems(2) by simp
  have d_deduct:
    "\<sigma> # \<Gamma> ; T ; shift ` set \<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (shift A) (Imp P (shift Q))"
    using shift_A_type d_cons by (rule CEV_axiom_from_deduction)
  have swap:
    "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type Cons.prems(3) shift_Q_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_swap:
    "\<sigma> # \<Gamma> ; T ; shift ` set \<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (Imp (shift A) (Imp P (shift Q)))
          (Imp P (Imp (shift A) (shift Q)))"
    using swap
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_swapped:
    "\<sigma> # \<Gamma> ; T ; shift ` set \<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift (Imp A Q))"
    using d_deduct d_swap unfolding shift_def
    by (auto intro: CEV_axiom_from.MP)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type Cons.prems(4) by auto
  have IH:
    "\<Gamma> ; T ; set \<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E (Imp A Q)"
    using tail_typed d_swapped Cons.prems(3) AQ_type
    by (rule Cons.IH)
  have lifted:
    "\<Gamma> ; T ; insert A (set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E (Imp A Q)"
    using IH by (rule CEV_axiom_from_mono) blast
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Cons.prems(3) by auto
  have reorder:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using E_type A_type Cons.prems(4)
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_reorder:
    "\<Gamma> ; T ; insert A (set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using reorder
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_A_to:
    "\<Gamma> ; T ; insert A (set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A (Imp ?E Q)"
    using lifted d_reorder by (rule CEV_axiom_from.MP)
  have d_A:
    "\<Gamma> ; T ; insert A (set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    by (rule CEV_axiom_from.Assumption) (simp_all add: A_type)
  have d_final:
    "\<Gamma> ; T ; insert A (set \<Delta>)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E Q"
    using d_A d_A_to by (rule CEV_axiom_from.MP)
  show ?case using d_final by simp
qed

lemma CEV_axiom_from_shifted_inst:
  assumes typed: "typed_theory \<Gamma> S"
    and d:
      "\<sigma> # \<Gamma> ; T ; shift ` S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T ; S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Exists \<sigma> P) Q"
proof -
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> shift ` S"
    and d_U:
      "\<sigma> # \<Gamma> ; T ; U
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift Q)"
    using assms(2) by (rule CEV_axiom_from_finite_support)
  define pre where "pre B = (SOME A. A \<in> S \<and> B = shift A)" for B
  have pre_prop:
    "\<And>B. B \<in> U \<Longrightarrow> pre B \<in> S \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> U"
    then have "\<exists>A. A \<in> S \<and> B = shift A"
      using U_sub by blast
    then show "pre B \<in> S \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  obtain Bs where set_Bs: "set Bs = U"
    using finite_U finite_list by blast
  let ?\<Delta> = "map pre Bs"
  have set_\<Delta>_sub: "set ?\<Delta> \<subseteq> S"
    using pre_prop set_Bs by auto
  have shift_set_\<Delta>: "shift ` set ?\<Delta> = U"
    using pre_prop set_Bs by auto
  have typed_\<Delta>:
    "\<And>A. A \<in> set ?\<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    using assms(1) set_\<Delta>_sub
    unfolding typed_theory_def by blast
  have d_\<Delta>:
    "\<sigma> # \<Gamma> ; T ; shift ` set ?\<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp P (shift Q)"
    using d_U shift_set_\<Delta> by simp
  have lower:
    "\<Gamma> ; T ; set ?\<Delta>
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Exists \<sigma> P) Q"
    using typed_\<Delta> d_\<Delta> assms(3,4)
    by (rule CEV_axiom_from_shifted_inst_list)
  show ?thesis
    using lower set_\<Delta>_sub by (rule CEV_axiom_from_mono)
qed

lemma CEV_axiom_from_abstract_fresh_witness_false:
  assumes d:
      "\<Gamma> ; T ; insert (henkin_witness_axiom c \<sigma> A) S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    and closed: "CEV_closed_axiom_stock T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_S: "c \<notin> consts_of_set S"
    and fresh_A: "c \<notin> consts_of A"
  shows "\<sigma> # \<Gamma> ; T ;
    insert (Imp (shift (Exists \<sigma> A)) A) (shift ` S)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d:
    "\<sigma> # \<Gamma> ; T ; abstract_const c \<sigma> ` insert ?W S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s abstract_const c \<sigma> ObjFalse"
    using d closed fresh_T
    by (rule CEV_axiom_from_abstract_const_fresh_stock)
  have abs_S: "abstract_const c \<sigma> ` S = shift ` S"
    using fresh_S by (rule abstract_const_image_fresh_set)
  have abs_W:
    "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using fresh_A by (rule abstract_const_henkin_witness_axiom_fresh)
  show ?thesis using abs_d abs_S abs_W by simp
qed

lemma CEV_axiom_from_fresh_witness_false:
  assumes typed_S: "typed_theory \<Gamma> S"
    and d:
      "\<Gamma> ; T ; insert (henkin_witness_axiom c \<sigma> A) S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    and closed: "CEV_closed_axiom_stock T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_S: "c \<notin> consts_of_set S"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type:
    "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_ext:
    "\<sigma> # \<Gamma> ; T ; insert ?P (shift ` S)
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d closed fresh_T fresh_S fresh_A
    by (rule CEV_axiom_from_abstract_fresh_witness_false)
  have d_imp_false:
    "\<sigma> # \<Gamma> ; T ; shift ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ObjFalse"
    using P_type d_ext by (rule CEV_axiom_from_deduction)
  have d_imp_shift_false:
    "\<sigma> # \<Gamma> ; T ; shift ` S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P (shift ObjFalse)"
    using d_imp_false by simp
  have lower:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?Q ObjFalse"
    using typed_S d_imp_shift_false P_type typed_ObjFalse
    by (rule CEV_axiom_from_shifted_inst)
  have Q_thm: "\<Gamma> \<turnstile>\<^sub>CEV ?Q"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H
        H_proves_exists_imp_shift_exists)
  have d_Q: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
    using Q_thm
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using d_Q lower by (rule CEV_axiom_from.MP)
qed

theorem CEV_axiom_relative_consistent_insert_fresh_witness:
  assumes typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_S: "c \<notin> consts_of_set S"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (insert (henkin_witness_axiom c \<sigma> A) S)"
proof (unfold CEV_axiom_relative_consistent_def, intro notI)
  assume d:
    "\<Gamma> ; T ; insert (henkin_witness_axiom c \<sigma> A) S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
  have "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using typed_S d closed fresh_T fresh_S fresh_A A_type
    by (rule CEV_axiom_from_fresh_witness_false)
  then show False
    using consistent unfolding CEV_axiom_relative_consistent_def by blast
qed

corollary CEV_axiom_relative_consistent_insert_fresh_witness_empty:
  assumes typed_T: "typed_theory [] T"
    and typed_S: "typed_theory [] S"
    and consistent: "CEV_axiom_relative_consistent [] T S"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_S: "c \<notin> consts_of_set S"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  shows "CEV_axiom_relative_consistent [] T
    (insert (henkin_witness_axiom c \<sigma> A) S)"
proof -
  have closed: "CEV_closed_axiom_stock T"
    using typed_T by (rule typed_theory_empty_imp_CEV_closed_axiom_stock)
  show ?thesis
    using typed_S consistent closed fresh_T fresh_S fresh_A A_type
    by (rule CEV_axiom_relative_consistent_insert_fresh_witness)
qed

theorem CEV_axiom_relative_fresh_witness_exists_empty:
  assumes finite_T: "finite T"
    and finite_S: "finite S"
    and typed_T: "typed_theory [] T"
    and typed_S: "typed_theory [] S"
    and consistent: "CEV_axiom_relative_consistent [] T S"
    and A_type: "\<sigma> # [] \<turnstile> A : Prop"
  obtains c where
    "c \<notin> consts_of_set T"
    "c \<notin> consts_of_set S"
    "c \<notin> consts_of A"
    "CEV_axiom_relative_consistent [] T
      (insert (henkin_witness_axiom c \<sigma> A) S)"
proof -
  have finite_union: "finite (T \<union> S)"
    using finite_T finite_S by simp
  obtain c where fresh_union: "fresh_const_for c (T \<union> S) A"
    using finite_union by (rule fresh_const_for_finite)
  have fresh_TS: "c \<notin> consts_of_set (T \<union> S)"
    and fresh_A: "c \<notin> consts_of A"
    using fresh_union unfolding fresh_const_for_def by blast+
  have fresh_T: "c \<notin> consts_of_set T"
  proof
    assume "c \<in> consts_of_set T"
    then obtain B where "B \<in> T" and "c \<in> consts_of B"
      by (rule consts_of_setD)
    then have "c \<in> consts_of_set (T \<union> S)"
      by (intro consts_of_setI) blast+
    then show False using fresh_TS by blast
  qed
  have fresh_S: "c \<notin> consts_of_set S"
  proof
    assume "c \<in> consts_of_set S"
    then obtain B where "B \<in> S" and "c \<in> consts_of B"
      by (rule consts_of_setD)
    then have "c \<in> consts_of_set (T \<union> S)"
      by (intro consts_of_setI) blast+
    then show False using fresh_TS by blast
  qed
  have preserved:
    "CEV_axiom_relative_consistent [] T
      (insert (henkin_witness_axiom c \<sigma> A) S)"
    using typed_T typed_S consistent fresh_T fresh_S fresh_A A_type
    by (rule CEV_axiom_relative_consistent_insert_fresh_witness_empty)
  show ?thesis
    using that[OF fresh_T fresh_S fresh_A preserved] .
qed

definition CEV_axiom_relative_staged_henkin_step ::
  "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<times> oterm \<Rightarrow>
    oterm set \<Rightarrow> oterm set" where
  "CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S =
    (case spec of (\<sigma>, A) \<Rightarrow>
      if \<sigma> # \<Gamma> \<turnstile> A : Prop
      then insert
        (henkin_witness_axiom
          (fresh_const_for_stage (T \<union> S) A) \<sigma> A) S
      else S)"

lemma CEV_axiom_relative_staged_henkin_step_finite:
  assumes "finite S"
  shows "finite (CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S)"
  using assms unfolding CEV_axiom_relative_staged_henkin_step_def
  by (cases spec) auto

lemma CEV_axiom_relative_staged_henkin_step_typed:
  assumes "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma>
    (CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have "typed_theory \<Gamma>
      (insert
        (henkin_witness_axiom
          (fresh_const_for_stage (T \<union> S) A) \<sigma> A) S)"
      using assms True
      by (rule typed_theory_insert_henkin_witness_axiom)
    then show ?thesis
      unfolding CEV_axiom_relative_staged_henkin_step_def spec_def
      using True by simp
  next
    case False
    then show ?thesis
      unfolding CEV_axiom_relative_staged_henkin_step_def spec_def
      using assms by simp
  qed
qed

lemma consts_of_set_Un:
  "consts_of_set (T \<union> S) = consts_of_set T \<union> consts_of_set S"
  unfolding consts_of_set_def by blast

lemma fresh_const_for_stage_fresh_finite_vocabulary:
  assumes "finite (consts_of_set T)"
  shows "fresh_const_for (fresh_const_for_stage T A) T A"
proof -
  have finite_support: "finite (consts_of_set T \<union> consts_of A)"
    using assms by simp
  have exists_fresh: "\<exists>c. fresh_const_for c T A"
  proof -
    obtain c where "c \<notin> consts_of_set T \<union> consts_of A"
      using fresh_string_finite[OF finite_support] by blast
    then show ?thesis
      unfolding fresh_const_for_def by blast
  qed
  show ?thesis
    unfolding fresh_const_for_stage_def
    using exists_fresh by (rule someI_ex)
qed

theorem CEV_axiom_relative_staged_henkin_step_consistent_finite_vocabulary:
  assumes finite_consts_T: "finite (consts_of_set T)"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    let ?c = "fresh_const_for_stage (T \<union> S) A"
    have finite_union: "finite (consts_of_set (T \<union> S))"
      using finite_consts_T finite_consts_of_set[OF finite_S]
      by (simp add: consts_of_set_Un)
    have fresh_union: "fresh_const_for ?c (T \<union> S) A"
      using finite_union
      by (rule fresh_const_for_stage_fresh_finite_vocabulary)
    have fresh_TS: "?c \<notin> consts_of_set (T \<union> S)"
      and fresh_A: "?c \<notin> consts_of A"
      using fresh_union unfolding fresh_const_for_def by blast+
    have fresh_T: "?c \<notin> consts_of_set T"
    proof
      assume "?c \<in> consts_of_set T"
      then obtain B where "B \<in> T" and "?c \<in> consts_of B"
        by (rule consts_of_setD)
      then have "?c \<in> consts_of_set (T \<union> S)"
        by (intro consts_of_setI) blast+
      then show False using fresh_TS by blast
    qed
    have fresh_S: "?c \<notin> consts_of_set S"
    proof
      assume "?c \<in> consts_of_set S"
      then obtain B where "B \<in> S" and "?c \<in> consts_of B"
        by (rule consts_of_setD)
      then have "?c \<in> consts_of_set (T \<union> S)"
        by (intro consts_of_setI) blast+
      then show False using fresh_TS by blast
    qed
    have preserved:
      "CEV_axiom_relative_consistent \<Gamma> T
        (insert (henkin_witness_axiom ?c \<sigma> A) S)"
      using typed_S consistent closed fresh_T fresh_S fresh_A True
      by (rule CEV_axiom_relative_consistent_insert_fresh_witness)
    show ?thesis
      unfolding CEV_axiom_relative_staged_henkin_step_def spec_def
      using True preserved by simp
  next
    case False
    then show ?thesis
      unfolding CEV_axiom_relative_staged_henkin_step_def spec_def
      using consistent by simp
  qed
qed

corollary CEV_axiom_relative_staged_henkin_step_consistent:
  assumes finite_T: "finite T"
    and finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent: "CEV_axiom_relative_consistent \<Gamma> T S"
    and closed: "CEV_closed_axiom_stock T"
  shows "CEV_axiom_relative_consistent \<Gamma> T
    (CEV_axiom_relative_staged_henkin_step \<Gamma> T spec S)"
proof -
  have "finite (consts_of_set T)"
    using finite_T by (rule finite_consts_of_set)
  then show ?thesis
    using finite_S typed_S consistent closed
    by (rule
      CEV_axiom_relative_staged_henkin_step_consistent_finite_vocabulary)
qed

corollary CEV_axiom_relative_staged_henkin_step_consistent_empty:
  assumes finite_T: "finite T"
    and finite_S: "finite S"
    and typed_T: "typed_theory [] T"
    and typed_S: "typed_theory [] S"
    and consistent: "CEV_axiom_relative_consistent [] T S"
  shows "CEV_axiom_relative_consistent [] T
    (CEV_axiom_relative_staged_henkin_step [] T spec S)"
proof -
  have closed: "CEV_closed_axiom_stock T"
    using typed_T by (rule typed_theory_empty_imp_CEV_closed_axiom_stock)
  show ?thesis
    using finite_T finite_S typed_S consistent closed
    by (rule CEV_axiom_relative_staged_henkin_step_consistent)
qed

end
