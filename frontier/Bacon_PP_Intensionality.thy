theory Bacon_PP_Intensionality
  imports "Higher_Order_Metaphysics.Bacon_S4"
begin

section \<open>Intensionality is a theorem of CEV\<close>

text \<open>
  Bacon--Dorr, \emph{Classicism} \<open>\<section>1.5\<close> (p.\ 17), states \<^bold>\<open>Intensionality\<close>

  \begin{center}
  \<open>\<box>\<forall>z\<^sub>1\<dots>z\<^sub>n (X z\<^sub>1\<dots>z\<^sub>n \<longleftrightarrow> Y z\<^sub>1\<dots>z\<^sub>n) \<longrightarrow> X = Y\<close>
  \end{center}

  and proves it a theorem of Classicism.  Footnote 18 (p.\ 16) records that \<open>C\<close> thereby
  includes Modalized Functionality.  This theory carries out the \<open>\<section>1.5\<close> derivation in
  the unary case, inside repo-\<open>CEV\<close>.

  The route.  \<open>\<zeta>\<close>-Equivalence is theorem-level, so it cannot be applied to the
  hypothesis \<open>\<forall>z. X z \<longleftrightarrow> Y z\<close> directly.  The trick is to build that very formula into
  both sides as a conjunct, which makes the pointwise biconditional an \<open>H\<close>-theorem; then
  use \<open>\<box>C\<close>, i.e.\ \<open>C = \<top>\<close>, to replace the conjunct by \<open>\<top>\<close> via Leibniz, and finally
  discharge \<open>\<top>\<close>.

  Stage one, below, is the discharge step, which also validates the beta bookkeeping.
\<close>

subsection \<open>The builder\<close>

definition intens_builder :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_builder \<sigma> X =
    Lam Prop (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))"

text \<open>
  Under the two binders \<open>Var 0\<close> is the argument of type \<open>\<sigma>\<close> and \<open>Var 1\<close> is the
  conjunct of type \<open>Prop\<close>; \<open>X\<close> is shifted past both.
\<close>

lemma typed_intens_builder:
  assumes "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> intens_builder \<sigma> X : Prop \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
  unfolding intens_builder_def
proof (intro has_type.Lam has_type.Conj has_type.App)
  have "[\<sigma>, Prop] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>, Prop]) X : \<sigma> \<rightarrow>\<^sub>o Prop"
    using assms by (rule shift_by_preserves_typing)
  then show "\<sigma> # Prop # \<Gamma> \<turnstile> shift_by 2 X : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (simp add: numeral_2_eq_2)
  show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  show "\<sigma> # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
qed

subsection \<open>The guarded operator, and the Leibniz predicate\<close>

text \<open>
  \<open>intens_conj \<sigma> X c\<close> is \<open>\<lambda>z. (X z \<and> c)\<close>, built at the meta level so that no beta step is
  needed to name it.  \<open>intens_pred\<close> is the object-level predicate in \<open>c\<close> that Leibniz
  will be applied to; one beta step turns \<open>intens_pred \<sigma> X Y c\<close> into the identity
  between the two guarded operators.
\<close>

definition intens_conj :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_conj \<sigma> X c =
    Lam \<sigma> (Conj (App (shift X) (Var 0)) (shift c))"

definition intens_pred :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "intens_pred \<sigma> X Y =
    Lam Prop
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
        (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))"

lemma typed_intens_conj:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma> \<rightarrow>\<^sub>o Prop"
    and c: "\<Gamma> \<turnstile> c : Prop"
  shows "\<Gamma> \<turnstile> intens_conj \<sigma> X c : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding intens_conj_def
proof (intro has_type.Lam has_type.Conj has_type.App)
  have "[\<sigma>] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>]) X : \<sigma> \<rightarrow>\<^sub>o Prop"
    using X by (rule shift_by_preserves_typing)
  then show "\<sigma> # \<Gamma> \<turnstile> shift X : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (simp add: shift_by_1)
  show "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) (simp add: lookup_def)
  have "[\<sigma>] @ \<Gamma> \<turnstile> shift_by (length [\<sigma>]) c : Prop"
    using c by (rule shift_by_preserves_typing)
  then show "\<sigma> # \<Gamma> \<turnstile> shift c : Prop"
    by (simp add: shift_by_1)
qed

text \<open>
  The beta computation.  This is the step Goodman's notes flag as the project's
  single largest source of corrected errors, so it is isolated and checked rather
  than performed inline.
\<close>

lemma subst_rename_to_rename:
  assumes "\<And>n. s (\<rho> n) = Var (\<tau> n)"
  shows "subst s (rename \<rho> M) = rename \<tau> M"
  using assms
proof (induction M arbitrary: s \<rho> \<tau>)
  case (Lam \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren \<rho>) M) = rename (lift_ren \<tau>) M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed (simp_all add: assms)

lemma subst_lift_shift_by_2:
  "subst (lift_subst (case_nat c Var)) (rename (shift_ren 2 0) M)
    = shift M"
proof -
  have "\<And>n. lift_subst (case_nat c Var) (shift_ren 2 0 n) = Var (Suc n)"
    by (simp add: shift_ren_def)
  then have "subst (lift_subst (case_nat c Var))
      (rename (shift_ren 2 0) M) = rename Suc M"
    by (rule subst_rename_to_rename)
  then show ?thesis by (simp add: shift_def)
qed

lemma intens_pred_beta:
  "beta_contract (App (intens_pred \<sigma> X Y) c)
    (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c))"
proof -
  have "beta_contract
      (App (Lam Prop
        (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
          (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))) c)
      (subst0 c
        (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
          (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
          (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1)))))"
    by (rule beta_contract.beta)
  moreover have
    "subst0 c
      (Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> (Conj (App (shift_by 2 X) (Var 0)) (Var 1)))
        (Lam \<sigma> (Conj (App (shift_by 2 Y) (Var 0)) (Var 1))))
      = Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (intens_conj \<sigma> X c) (intens_conj \<sigma> Y c)"
    by (simp add: subst0_def intens_conj_def shift_by_def
        subst_lift_shift_by_2 shift_def)
  ultimately show ?thesis
    unfolding intens_pred_def by simp
qed

end
