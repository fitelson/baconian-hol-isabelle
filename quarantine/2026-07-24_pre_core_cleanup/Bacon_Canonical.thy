theory Bacon_Canonical
  imports Bacon_Completeness "HOL-Library.Countable"
begin

section \<open>Canonical theories for Henkin completeness\<close>

text \<open>
  This theory starts the canonical-model side of the completeness proof.  The
  earlier completeness interface reduces completeness to countermodel
  existence.  Here we introduce the syntactic objects that a Lindenbaum-Henkin
  construction is meant to produce: typed sets of assumptions, finite
  derivability from such sets, consistency, maximal consistency, and Henkin
  witnesses for existential formulas.

  We keep these notions proof-system specific where the underlying theoremhood
  and local derivability relations differ.  The first block is for the minimal
  higher-order logic \<open>H\<close>; the second repeats the infrastructure for the
  Classicist extension \<open>C\<close>.
\<close>

instantiation otype :: countable
begin

instance
  by countable_datatype

end

instantiation oterm :: countable
begin

instance
  by countable_datatype

end

subsection \<open>Common predicates\<close>

definition typed_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "typed_theory \<Gamma> T \<longleftrightarrow> (\<forall>A \<in> T. \<Gamma> \<turnstile> A : Prop)"

definition Henkin_witnessed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "Henkin_witnessed \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow> Exists \<sigma> A \<in> T \<longrightarrow>
      (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T))"

definition Henkin_scheme_in ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (otype \<Rightarrow> oterm \<Rightarrow> oterm) \<Rightarrow> bool" where
  "Henkin_scheme_in \<Gamma> T W \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      \<Gamma> \<turnstile> W \<sigma> A : \<sigma> \<and>
      Imp (Exists \<sigma> A) (subst0 (W \<sigma> A) A) \<in> T)"

lemma typed_theoryD:
  assumes "typed_theory \<Gamma> T"
    and "A \<in> T"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms unfolding typed_theory_def by blast

lemma typed_theory_singleton:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "typed_theory \<Gamma> {A}"
  using assms unfolding typed_theory_def by simp

lemma typed_theory_insert:
  assumes "typed_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "typed_theory \<Gamma> (insert A T)"
  using assms unfolding typed_theory_def by blast

lemma typed_theory_Un:
  assumes "typed_theory \<Gamma> T"
    and "typed_theory \<Gamma> U"
  shows "typed_theory \<Gamma> (T \<union> U)"
  using assms unfolding typed_theory_def by blast

lemma typed_theory_set:
  assumes "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "typed_theory \<Gamma> (set \<Delta>)"
  using assms unfolding typed_theory_def by blast

lemma Henkin_witnessedD:
  assumes "Henkin_witnessed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "Exists \<sigma> A \<in> T"
  obtains W where "\<Gamma> \<turnstile> W : \<sigma>" and "subst0 W A \<in> T"
  using assms unfolding Henkin_witnessed_def by blast

lemma Henkin_scheme_inD:
  assumes "Henkin_scheme_in \<Gamma> T W"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> W \<sigma> A : \<sigma>"
    and "Imp (Exists \<sigma> A) (subst0 (W \<sigma> A) A) \<in> T"
  using assms unfolding Henkin_scheme_in_def by auto

fun consts_of :: "oterm \<Rightarrow> string set" where
  "consts_of (Var n) = {}"
| "consts_of (Const c \<sigma>) = {c}"
| "consts_of (App M N) = consts_of M \<union> consts_of N"
| "consts_of (Lam \<sigma> M) = consts_of M"
| "consts_of (Eq \<sigma> M N) = consts_of M \<union> consts_of N"
| "consts_of (Neg A) = consts_of A"
| "consts_of (Conj A B) = consts_of A \<union> consts_of B"
| "consts_of (Disj A B) = consts_of A \<union> consts_of B"
| "consts_of (Imp A B) = consts_of A \<union> consts_of B"
| "consts_of (Forall \<sigma> A) = consts_of A"
| "consts_of (Exists \<sigma> A) = consts_of A"

definition consts_of_set :: "oterm set \<Rightarrow> string set" where
  "consts_of_set T = (\<Union>A \<in> T. consts_of A)"

definition fresh_const_for :: "string \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "fresh_const_for c T A \<longleftrightarrow> c \<notin> consts_of_set T \<and> c \<notin> consts_of A"

lemma finite_consts_of[simp]:
  "finite (consts_of A)"
  by (induction A) auto

lemma consts_of_setD:
  assumes "c \<in> consts_of_set T"
  obtains A where "A \<in> T" and "c \<in> consts_of A"
  using assms unfolding consts_of_set_def by blast

lemma consts_of_setI:
  assumes "A \<in> T"
    and "c \<in> consts_of A"
  shows "c \<in> consts_of_set T"
  using assms unfolding consts_of_set_def by blast

lemma finite_consts_of_set:
  assumes "finite T"
  shows "finite (consts_of_set T)"
  using assms
proof (induction T rule: finite_induct)
  case empty
  then show ?case
    unfolding consts_of_set_def by simp
next
  case (insert A T)
  have "consts_of_set (insert A T) = consts_of A \<union> consts_of_set T"
    unfolding consts_of_set_def by auto
  then show ?case
    using insert.IH by simp
qed

lemma fresh_string_finite:
  fixes S :: "string set"
  assumes "finite S"
  shows "\<exists>c. c \<notin> S"
proof (cases "S = {}")
  case True
  then show ?thesis
    by blast
next
  case False
  let ?n = "Suc (Max (length ` S))"
  let ?c = "replicate ?n (undefined :: char)"
  have len_lt: "\<And>s. s \<in> S \<Longrightarrow> length s < ?n"
  proof -
    fix s
    assume "s \<in> S"
    then have len_mem: "length s \<in> length ` S"
      by blast
    have finite_lengths: "finite (length ` S)"
      using assms by simp
    have "length s \<le> Max (length ` S)"
      by (rule Max_ge[OF finite_lengths len_mem])
    then show "length s < ?n"
      by simp
  qed
  have "?c \<notin> S"
  proof
    assume "?c \<in> S"
    then have "length ?c < ?n"
      by (rule len_lt)
    then show False
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma fresh_const_for_finite:
  assumes "finite T"
  obtains c where "fresh_const_for c T A"
proof -
  have finite_support: "finite (consts_of_set T \<union> consts_of A)"
    using assms by (simp add: finite_consts_of_set)
  obtain c where "c \<notin> consts_of_set T \<union> consts_of A"
    using fresh_string_finite[OF finite_support] by blast
  then have "fresh_const_for c T A"
    unfolding fresh_const_for_def by blast
  then show ?thesis
    using that by blast
qed

lemma consts_of_rename[simp]:
  "consts_of (rename r A) = consts_of A"
  by (induction A arbitrary: r) auto

lemma consts_of_lift_subst_subset:
  assumes "\<And>n. consts_of (s n) \<subseteq> C"
  shows "consts_of (lift_subst s n) \<subseteq> C"
  using assms by (cases n) auto

lemma consts_of_subst_subset:
  assumes "\<And>n. consts_of (s n) \<subseteq> C"
  shows "consts_of (subst s A) \<subseteq> consts_of A \<union> C"
  using assms
proof (induction A arbitrary: s)
  case (Lam \<sigma> A)
  have lift: "\<And>n. consts_of (lift_subst s n) \<subseteq> C"
    using Lam.prems by (rule consts_of_lift_subst_subset)
  have "consts_of (subst (lift_subst s) A) \<subseteq> consts_of A \<union> C"
    using lift by (rule Lam.IH)
  then show ?case
    by simp
next
  case (Forall \<sigma> A)
  have lift: "\<And>n. consts_of (lift_subst s n) \<subseteq> C"
    using Forall.prems by (rule consts_of_lift_subst_subset)
  have "consts_of (subst (lift_subst s) A) \<subseteq> consts_of A \<union> C"
    using lift by (rule Forall.IH)
  then show ?case
    by simp
next
  case (Exists \<sigma> A)
  have lift: "\<And>n. consts_of (lift_subst s n) \<subseteq> C"
    using Exists.prems by (rule consts_of_lift_subst_subset)
  have "consts_of (subst (lift_subst s) A) \<subseteq> consts_of A \<union> C"
    using lift by (rule Exists.IH)
  then show ?case
    by simp
qed auto

lemma consts_of_subst0_const_subset:
  "consts_of (subst0 (Const c \<sigma>) A) \<subseteq> insert c (consts_of A)"
proof -
  have subst_support:
    "consts_of (subst (case_nat (Const c \<sigma>) Var) A) \<subseteq> consts_of A \<union> {c}"
  proof (rule consts_of_subst_subset)
    fix n
    show "consts_of (case_nat (Const c \<sigma>) Var n) \<subseteq> {c}"
      by (cases n) auto
  qed
  then show ?thesis
    unfolding subst0_def by auto
qed

fun subst_const :: "string \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "subst_const c \<sigma> N (Var n) = Var n"
| "subst_const c \<sigma> N (Const d \<tau>) =
    (if d = c \<and> \<tau> = \<sigma> then N else Const d \<tau>)"
| "subst_const c \<sigma> N (App M P) =
    App (subst_const c \<sigma> N M) (subst_const c \<sigma> N P)"
| "subst_const c \<sigma> N (Lam \<rho> M) =
    Lam \<rho> (subst_const c \<sigma> (shift N) M)"
| "subst_const c \<sigma> N (Eq \<rho> M P) =
    Eq \<rho> (subst_const c \<sigma> N M) (subst_const c \<sigma> N P)"
| "subst_const c \<sigma> N (Neg A) = Neg (subst_const c \<sigma> N A)"
| "subst_const c \<sigma> N (Conj A B) =
    Conj (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
| "subst_const c \<sigma> N (Disj A B) =
    Disj (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
| "subst_const c \<sigma> N (Imp A B) =
    Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
| "subst_const c \<sigma> N (Forall \<rho> A) =
    Forall \<rho> (subst_const c \<sigma> (shift N) A)"
| "subst_const c \<sigma> N (Exists \<rho> A) =
    Exists \<rho> (subst_const c \<sigma> (shift N) A)"

definition abstract_const :: "string \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "abstract_const c \<sigma> A = subst_const c \<sigma> (Var 0) (shift A)"

lemma subst_const_fresh[simp]:
  assumes "c \<notin> consts_of A"
  shows "subst_const c \<sigma> N A = A"
  using assms by (induction A arbitrary: N) auto

lemma subst_const_same[simp]:
  "subst_const c \<sigma> (Const c \<sigma>) A = A"
  by (induction A) (auto simp: shift_def)

lemma subst_const_fresh_set:
  assumes "c \<notin> consts_of_set T"
    and "A \<in> T"
  shows "subst_const c \<sigma> N A = A"
proof -
  have "c \<notin> consts_of A"
    using assms consts_of_setI by blast
  then show ?thesis
    by simp
qed

lemma subst_const_preserves_typing:
  assumes M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile> subst_const c \<sigma> N M : \<tau>"
  using M_type N_type
proof (induction arbitrary: N \<sigma> c rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case
    by auto
next
  case (Const \<Gamma> d \<tau>)
  then show ?case
    by auto
next
  case (App \<Gamma> M \<rho> \<tau> P)
  have M_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N M : \<rho> \<rightarrow>\<^sub>o \<tau>"
    using App.prems by (rule App.IH(1))
  have P_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : \<rho>"
    using App.prems by (rule App.IH(2))
  show ?case
    using has_type.App[OF M_sub P_sub] by simp
next
  case (Lam \<rho> \<Gamma> M \<tau>)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Lam.prems by (rule weakening_front)
  have "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) M : \<tau>"
    using shifted_N by (rule Lam.IH)
  then show ?case
    using has_type.Lam by fastforce
next
  case (Eq \<Gamma> M \<rho> P)
  have M_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N M : \<rho>"
    using Eq.prems by (rule Eq.IH(1))
  have P_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : \<rho>"
    using Eq.prems by (rule Eq.IH(2))
  show ?case
    using has_type.Eq[OF M_sub P_sub] by simp
next
  case (Neg \<Gamma> A)
  have A_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Neg.prems by (rule Neg.IH)
  then show ?case
    using has_type.Neg by fastforce
next
  case (Conj \<Gamma> A B)
  have A_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Conj.prems by (rule Conj.IH(1))
  have B_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using Conj.prems by (rule Conj.IH(2))
  show ?case
    using has_type.Conj[OF A_sub B_sub] by simp
next
  case (Disj \<Gamma> A B)
  have A_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Disj.prems by (rule Disj.IH(1))
  have B_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using Disj.prems by (rule Disj.IH(2))
  show ?case
    using has_type.Disj[OF A_sub B_sub] by simp
next
  case (Imp \<Gamma> A B)
  have A_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Imp.prems by (rule Imp.IH(1))
  have B_sub: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using Imp.prems by (rule Imp.IH(2))
  show ?case
    using has_type.Imp[OF A_sub B_sub] by simp
next
  case (Forall \<rho> \<Gamma> A)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Forall.prems by (rule weakening_front)
  have "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) A : Prop"
    using shifted_N by (rule Forall.IH)
  then show ?case
    using has_type.Forall by fastforce
next
  case (Exists \<rho> \<Gamma> A)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Exists.prems by (rule weakening_front)
  have "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) A : Prop"
    using shifted_N by (rule Exists.IH)
  then show ?case
    using has_type.Exists by fastforce
qed

lemma abstract_const_preserves_typing:
  assumes "\<Gamma> \<turnstile> A : \<tau>"
  shows "\<sigma> # \<Gamma> \<turnstile> abstract_const c \<sigma> A : \<tau>"
proof -
  have shifted_type: "\<sigma> # \<Gamma> \<turnstile> shift A : \<tau>"
    using assms by (rule weakening_front)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  show ?thesis
    unfolding abstract_const_def
    using shifted_type var_type by (rule subst_const_preserves_typing)
qed

lemma abstract_const_fresh:
  assumes "c \<notin> consts_of A"
  shows "abstract_const c \<sigma> A = shift A"
  using assms unfolding abstract_const_def shift_def by simp

lemma typed_theory_subst_const_image:
  assumes "typed_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "typed_theory \<Gamma> (subst_const c \<sigma> N ` T)"
proof (unfold typed_theory_def, intro ballI)
  fix A
  assume "A \<in> subst_const c \<sigma> N ` T"
  then obtain B where B_in: "B \<in> T" and A_def: "A = subst_const c \<sigma> N B"
    by blast
  have "\<Gamma> \<turnstile> B : Prop"
    using assms(1) B_in by (rule typed_theoryD)
  then have "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using assms(2) by (rule subst_const_preserves_typing)
  then show "\<Gamma> \<turnstile> A : Prop"
    using A_def by simp
qed

lemma subst_const_image_fresh_set:
  assumes "c \<notin> consts_of_set T"
  shows "subst_const c \<sigma> N ` T = T"
proof
  show "subst_const c \<sigma> N ` T \<subseteq> T"
  proof
    fix A
    assume "A \<in> subst_const c \<sigma> N ` T"
    then obtain B where B_in: "B \<in> T" and A_def: "A = subst_const c \<sigma> N B"
      by blast
    have "subst_const c \<sigma> N B = B"
      using assms B_in by (rule subst_const_fresh_set)
    then show "A \<in> T"
      using A_def B_in by simp
  qed
  show "T \<subseteq> subst_const c \<sigma> N ` T"
  proof
    fix A
    assume A_in: "A \<in> T"
    have subst_eq: "subst_const c \<sigma> N A = A"
      using assms A_in by (rule subst_const_fresh_set)
    have image_member: "subst_const c \<sigma> N A \<in> subst_const c \<sigma> N ` T"
      using A_in by (rule imageI)
    show "A \<in> subst_const c \<sigma> N ` T"
      using subst_eq image_member
      by simp
  qed
qed

lemma rename_cong:
  assumes "\<And>n. r n = s n"
  shows "rename r M = rename s M"
  using assms
proof (induction M arbitrary: r s)
  case (Var n)
  then show ?case
    by simp
next
  case (Const c \<tau>)
  then show ?case
    by simp
next
  case (App M P)
  then show ?case
    by simp
next
  case (Lam \<rho> M)
  have lift_eq: "\<And>n. lift_ren r n = lift_ren s n"
    using Lam.prems by (case_tac n; simp)
  have "rename (lift_ren r) M = rename (lift_ren s) M"
    using lift_eq by (rule Lam.IH)
  then show ?case
    by simp
next
  case (Eq \<rho> M P)
  then show ?case
    by simp
next
  case (Neg A)
  then show ?case
    by simp
next
  case (Conj A B)
  then show ?case
    by simp
next
  case (Disj A B)
  then show ?case
    by simp
next
  case (Imp A B)
  then show ?case
    by simp
next
  case (Forall \<rho> A)
  have lift_eq: "\<And>n. lift_ren r n = lift_ren s n"
    using Forall.prems by (case_tac n; simp)
  have "rename (lift_ren r) A = rename (lift_ren s) A"
    using lift_eq by (rule Forall.IH)
  then show ?case
    by simp
next
  case (Exists \<rho> A)
  have lift_eq: "\<And>n. lift_ren r n = lift_ren s n"
    using Exists.prems by (case_tac n; simp)
  have "rename (lift_ren r) A = rename (lift_ren s) A"
    using lift_eq by (rule Exists.IH)
  then show ?case
    by simp
qed

lemma rename_comp:
  "rename r (rename s M) = rename (r \<circ> s) M"
proof (induction M arbitrary: r s)
  case (Lam \<rho> M)
  have "rename (lift_ren r) (rename (lift_ren s) M) =
      rename (lift_ren r \<circ> lift_ren s) M"
    by (rule Lam.IH)
  also have "... = rename (lift_ren (r \<circ> s)) M"
    by (rule rename_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Forall \<rho> M)
  have "rename (lift_ren r) (rename (lift_ren s) M) =
      rename (lift_ren r \<circ> lift_ren s) M"
    by (rule Forall.IH)
  also have "... = rename (lift_ren (r \<circ> s)) M"
    by (rule rename_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Exists \<rho> M)
  have "rename (lift_ren r) (rename (lift_ren s) M) =
      rename (lift_ren r \<circ> lift_ren s) M"
    by (rule Exists.IH)
  also have "... = rename (lift_ren (r \<circ> s)) M"
    by (rule rename_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
qed auto

lemma shift_rename_lift:
  "shift (rename r N) = rename (lift_ren r) (shift N)"
proof -
  have left: "shift (rename r N) = rename (Suc \<circ> r) N"
    unfolding shift_def by (simp add: rename_comp)
  have right: "rename (lift_ren r) (shift N) =
      rename (lift_ren r \<circ> Suc) N"
    unfolding shift_def by (simp add: rename_comp)
  have "rename (Suc \<circ> r) N = rename (lift_ren r \<circ> Suc) N"
    by (rule rename_cong) simp
  then show ?thesis
    using left right by simp
qed

lemma subst_const_rename:
  "subst_const c \<sigma> (rename r N) (rename r M) =
    rename r (subst_const c \<sigma> N M)"
proof (induction M arbitrary: N r)
  case (Lam \<rho> M)
  have shifted: "shift (rename r N) = rename (lift_ren r) (shift N)"
    by (rule shift_rename_lift)
  have "subst_const c \<sigma> (rename (lift_ren r) (shift N))
      (rename (lift_ren r) M) =
      rename (lift_ren r) (subst_const c \<sigma> (shift N) M)"
    by (rule Lam.IH)
  then show ?case
    using shifted by simp
next
  case (Forall \<rho> M)
  have shifted: "shift (rename r N) = rename (lift_ren r) (shift N)"
    by (rule shift_rename_lift)
  have "subst_const c \<sigma> (rename (lift_ren r) (shift N))
      (rename (lift_ren r) M) =
      rename (lift_ren r) (subst_const c \<sigma> (shift N) M)"
    by (rule Forall.IH)
  then show ?case
    using shifted by simp
next
  case (Exists \<rho> M)
  have shifted: "shift (rename r N) = rename (lift_ren r) (shift N)"
    by (rule shift_rename_lift)
  have "subst_const c \<sigma> (rename (lift_ren r) (shift N))
      (rename (lift_ren r) M) =
      rename (lift_ren r) (subst_const c \<sigma> (shift N) M)"
    by (rule Exists.IH)
  then show ?case
    using shifted by simp
qed auto

lemma subst_const_shift:
  "subst_const c \<sigma> (shift N) (shift M) = shift (subst_const c \<sigma> N M)"
  unfolding shift_def
  by (rule subst_const_rename)

lemma subst_const_shift_by:
  "subst_const c \<sigma> (shift_by k N) (shift_by k M) =
    shift_by k (subst_const c \<sigma> N M)"
  unfolding shift_by_def
  by (rule subst_const_rename)

lemma subst_const_app_vec:
  "subst_const c \<sigma> N (app_vec F As) =
    app_vec (subst_const c \<sigma> N F) (map (subst_const c \<sigma> N) As)"
  by (induction As arbitrary: F) simp_all

lemma subst_const_fresh_vars[simp]:
  "map (subst_const c \<sigma> N) (fresh_vars k) = fresh_vars k"
  unfolding fresh_vars_def
  by (simp add: map_map)

lemma subst_const_zeta_body:
  "subst_const c \<sigma> (shift_by (length \<sigma>s) N) (zeta_body \<sigma>s F G) =
    zeta_body \<sigma>s (subst_const c \<sigma> N F) (subst_const c \<sigma> N G)"
  unfolding zeta_body_def
  by (simp add: subst_const_app_vec subst_const_shift_by)

definition prefix_ren :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "prefix_ren k r n = (if n < k then n else k + r (n - k))"

lemma rename_shift_by_prefix:
  "rename (prefix_ren k r) (shift_by k M) =
    shift_by k (rename r M)"
proof -
  have maps:
      "\<And>n. (prefix_ren k r \<circ> shift_ren k 0) n =
        (shift_ren k 0 \<circ> r) n"
    by (simp add: prefix_ren_def shift_ren_def add.commute)
  show ?thesis
    unfolding shift_by_def
    apply (simp only: rename_comp)
    by (rule rename_cong) (rule maps)
qed

lemma rename_app_vec:
  "rename r (app_vec F As) =
    app_vec (rename r F) (map (rename r) As)"
  by (induction As arbitrary: F) simp_all

lemma rename_prefix_fresh_vars[simp]:
  "map (rename (prefix_ren k r)) (fresh_vars k) = fresh_vars k"
  unfolding fresh_vars_def prefix_ren_def
  by (simp add: map_map)

lemma rename_zeta_body_prefix:
  "rename (prefix_ren (length \<sigma>s) r) (zeta_body \<sigma>s F G) =
    zeta_body \<sigma>s (rename r F) (rename r G)"
  unfolding zeta_body_def
  by (simp add: rename_app_vec rename_shift_by_prefix)

lemma prefix_ren_preserves_lookup:
  assumes mapping:
      "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
        lookup \<Delta> (r n) = Some \<tau>"
    and source: "lookup (\<sigma>s @ \<Gamma>) n = Some \<tau>"
  shows "lookup (\<sigma>s @ \<Delta>)
    (prefix_ren (length \<sigma>s) r n) = Some \<tau>"
proof (cases "n < length \<sigma>s")
  case True
  then show ?thesis
    using source
    by (simp add: prefix_ren_def lookup_def nth_append)
next
  case False
  have n_bound: "n < length \<sigma>s + length \<Gamma>"
    using source
    by (auto simp: lookup_def split: if_splits)
  have nth_eq: "(\<sigma>s @ \<Gamma>) ! n = \<tau>"
    using source n_bound
    unfolding lookup_def
    by simp
  have tail_bound: "n - length \<sigma>s < length \<Gamma>"
    using n_bound False
    by arith
  have tail_eq: "\<Gamma> ! (n - length \<sigma>s) = \<tau>"
    using nth_eq False
    by (simp add: nth_append)
  then have source_tail: "lookup \<Gamma> (n - length \<sigma>s) = Some \<tau>"
    using tail_bound tail_eq
    by (simp add: lookup_def)
  have target_tail:
      "lookup \<Delta> (r (n - length \<sigma>s)) = Some \<tau>"
    using source_tail by (rule mapping)
  have target_bound:
      "r (n - length \<sigma>s) < length \<Delta>"
    using target_tail
    by (auto simp: lookup_def split: if_splits)
  have target_eq:
      "\<Delta> ! r (n - length \<sigma>s) = \<tau>"
    using target_tail target_bound
    by (simp add: lookup_def)
  show ?thesis
    using False target_bound target_eq
    by (simp add: prefix_ren_def lookup_def nth_append)
qed

lemma subst_cong:
  assumes "\<And>n. s n = t n"
  shows "subst s M = subst t M"
  using assms
proof (induction M arbitrary: s t)
  case (Var n)
  then show ?case
    by simp
next
  case (Const c \<tau>)
  then show ?case
    by simp
next
  case (App M P)
  then show ?case
    by simp
next
  case (Lam \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Lam.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Lam.IH)
  then show ?case
    by simp
next
  case (Eq \<rho> M P)
  then show ?case
    by simp
next
  case (Neg A)
  then show ?case
    by simp
next
  case (Conj A B)
  then show ?case
    by simp
next
  case (Disj A B)
  then show ?case
    by simp
next
  case (Imp A B)
  then show ?case
    by simp
next
  case (Forall \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Forall.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Forall.IH)
  then show ?case
    by simp
next
  case (Exists \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Exists.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Exists.IH)
  then show ?case
    by simp
qed

lemma subst_rename:
  "subst s (rename r M) = subst (s \<circ> r) M"
proof (induction M arbitrary: s r)
  case (Lam \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Lam.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule subst_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Forall \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Forall.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule subst_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Exists \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Exists.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule subst_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
qed simp_all

lemma rename_subst:
  "rename r (subst s M) = subst (\<lambda>n. rename r (s n)) M"
proof (induction M arbitrary: r s)
  case (Lam \<rho> M)
  have "rename (lift_ren r) (subst (lift_subst s) M) =
      subst (\<lambda>n. rename (lift_ren r) (lift_subst s n)) M"
    by (rule Lam.IH)
  also have "... = subst (lift_subst (\<lambda>n. rename r (s n))) M"
    by (rule subst_cong) (case_tac n; simp add: rename_comp comp_def)
  finally show ?case
    by simp
next
  case (Forall \<rho> M)
  have "rename (lift_ren r) (subst (lift_subst s) M) =
      subst (\<lambda>n. rename (lift_ren r) (lift_subst s n)) M"
    by (rule Forall.IH)
  also have "... = subst (lift_subst (\<lambda>n. rename r (s n))) M"
    by (rule subst_cong) (case_tac n; simp add: rename_comp comp_def)
  finally show ?case
    by simp
next
  case (Exists \<rho> M)
  have "rename (lift_ren r) (subst (lift_subst s) M) =
      subst (\<lambda>n. rename (lift_ren r) (lift_subst s n)) M"
    by (rule Exists.IH)
  also have "... = subst (lift_subst (\<lambda>n. rename r (s n))) M"
    by (rule subst_cong) (case_tac n; simp add: rename_comp comp_def)
  finally show ?case
    by simp
qed simp_all

lemma subst_lift_shift:
  "subst (lift_subst s) (shift M) = shift (subst s M)"
proof -
  have lhs: "subst (lift_subst s) (shift M) =
      subst (lift_subst s \<circ> Suc) M"
    unfolding shift_def by (simp add: subst_rename)
  have map_eq: "\<And>n. (lift_subst s \<circ> Suc) n = rename Suc (s n)"
    by simp
  have subst_eq: "subst (lift_subst s \<circ> Suc) M =
      subst (\<lambda>n. rename Suc (s n)) M"
    by (rule subst_cong) (rule map_eq)
  have rhs: "shift (subst s M) = subst (\<lambda>n. rename Suc (s n)) M"
    unfolding shift_def by (simp add: rename_subst)
  show ?thesis
    using lhs subst_eq rhs by simp
qed

lemma lift_subst_Var[simp]:
  "lift_subst Var = Var"
  by (rule ext) (case_tac x; simp)

lemma subst_Var[simp]:
  "subst Var M = M"
  by (induction M) simp_all

lemma subst_comp:
  "subst s (subst t M) = subst (\<lambda>n. subst s (t n)) M"
proof (induction M arbitrary: s t)
  case (Lam \<rho> M)
  have lift_comp: "\<And>n.
      subst (lift_subst s) (lift_subst t n) =
      lift_subst (\<lambda>m. subst s (t m)) n"
  proof -
    fix n
    show "subst (lift_subst s) (lift_subst t n) =
        lift_subst (\<lambda>m. subst s (t m)) n"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst (lift_subst s) (rename Suc (t m)) =
          subst (lift_subst s \<circ> Suc) (t m)"
        by (simp add: subst_rename)
      also have "... = subst (\<lambda>k. rename Suc (s k)) (t m)"
        by (rule subst_cong) simp
      also have "... = rename Suc (subst s (t m))"
        by (simp add: rename_subst)
      finally show ?thesis
        using Suc by simp
    qed
  qed
  have "subst (lift_subst s) (subst (lift_subst t) M) =
      subst (\<lambda>n. subst (lift_subst s) (lift_subst t n)) M"
    by (rule Lam.IH)
  also have "... = subst (lift_subst (\<lambda>m. subst s (t m))) M"
    by (rule subst_cong) (rule lift_comp)
  finally show ?case
    by simp
next
  case (Forall \<rho> M)
  have lift_comp: "\<And>n.
      subst (lift_subst s) (lift_subst t n) =
      lift_subst (\<lambda>m. subst s (t m)) n"
  proof -
    fix n
    show "subst (lift_subst s) (lift_subst t n) =
        lift_subst (\<lambda>m. subst s (t m)) n"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst (lift_subst s) (rename Suc (t m)) =
          subst (lift_subst s \<circ> Suc) (t m)"
        by (simp add: subst_rename)
      also have "... = subst (\<lambda>k. rename Suc (s k)) (t m)"
        by (rule subst_cong) simp
      also have "... = rename Suc (subst s (t m))"
        by (simp add: rename_subst)
      finally show ?thesis
        using Suc by simp
    qed
  qed
  have "subst (lift_subst s) (subst (lift_subst t) M) =
      subst (\<lambda>n. subst (lift_subst s) (lift_subst t n)) M"
    by (rule Forall.IH)
  also have "... = subst (lift_subst (\<lambda>m. subst s (t m))) M"
    by (rule subst_cong) (rule lift_comp)
  finally show ?case
    by simp
next
  case (Exists \<rho> M)
  have lift_comp: "\<And>n.
      subst (lift_subst s) (lift_subst t n) =
      lift_subst (\<lambda>m. subst s (t m)) n"
  proof -
    fix n
    show "subst (lift_subst s) (lift_subst t n) =
        lift_subst (\<lambda>m. subst s (t m)) n"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst (lift_subst s) (rename Suc (t m)) =
          subst (lift_subst s \<circ> Suc) (t m)"
        by (simp add: subst_rename)
      also have "... = subst (\<lambda>k. rename Suc (s k)) (t m)"
        by (rule subst_cong) simp
      also have "... = rename Suc (subst s (t m))"
        by (simp add: rename_subst)
      finally show ?thesis
        using Suc by simp
    qed
  qed
  have "subst (lift_subst s) (subst (lift_subst t) M) =
      subst (\<lambda>n. subst (lift_subst s) (lift_subst t n)) M"
    by (rule Exists.IH)
  also have "... = subst (lift_subst (\<lambda>m. subst s (t m))) M"
    by (rule subst_cong) (rule lift_comp)
  finally show ?case
    by simp
qed simp_all

lemma subst0_subst_lift:
  "subst0 W (subst (lift_subst s) A) = subst (case_nat W s) A"
proof -
  let ?inst = "case_nat W Var"
  have "subst0 W (subst (lift_subst s) A) =
      subst (\<lambda>n. subst ?inst (lift_subst s n)) A"
    unfolding subst0_def by (simp add: subst_comp)
  also have "... = subst (case_nat W s) A"
  proof (rule subst_cong)
    fix n
    show "subst ?inst (lift_subst s n) = case_nat W s n"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst ?inst (rename Suc (s m)) = s m"
        using subst0_shift[of W "s m"]
        unfolding subst0_def shift_def by simp
      then show ?thesis
        using Suc by simp
    qed
  qed
  finally show ?thesis .
qed

lemma subst_subst0:
  "subst s (subst0 W A) = subst0 (subst s W) (subst (lift_subst s) A)"
proof -
  have "subst s (subst0 W A) =
      subst (\<lambda>n. subst s (case_nat W Var n)) A"
    unfolding subst0_def by (simp add: subst_comp)
  also have "... = subst (case_nat (subst s W) s) A"
    by (rule subst_cong) (case_tac n; simp)
  also have "... = subst0 (subst s W) (subst (lift_subst s) A)"
    by (simp add: subst0_subst_lift)
  finally show ?thesis .
qed

lemma beta_contract_subst:
  assumes "M \<rightarrow>\<^sub>\<beta> P"
  shows "subst s M \<rightarrow>\<^sub>\<beta> subst s P"
  using assms
proof cases
  case (beta \<rho> A T)
  then show ?thesis
    by (auto simp add: subst_subst0 intro: beta_contract.beta)
qed

lemma eta_contract_subst:
  assumes "M \<rightarrow>\<^sub>\<eta> P"
  shows "subst s M \<rightarrow>\<^sub>\<eta> subst s P"
  using assms
proof cases
  case (eta F)
  then show ?thesis
    by (auto simp add: subst_lift_shift intro: eta_contract.eta)
qed

lemma compatible_step_subst:
  assumes step: "compatible_step R A B"
    and root_pres: "\<And>s M P. R M P \<Longrightarrow> R (subst s M) (subst s P)"
  shows "compatible_step R (subst s A) (subst s B)"
  using step
proof (induction arbitrary: s)
  case (root M P)
  show ?case
    by (rule compatible_step.root, rule root_pres, rule root.hyps)
next
  case (App_left M M' P)
  show ?case
    using App_left.IH by (simp add: compatible_step.App_left)
next
  case (App_right P P' M)
  show ?case
    using App_right.IH by (simp add: compatible_step.App_right)
next
  case (Lam_body M M' \<rho>)
  have body: "compatible_step R
      (subst (lift_subst s) M) (subst (lift_subst s) M')"
    by (rule Lam_body.IH)
  then show ?case
    by (simp add: compatible_step.Lam_body)
next
  case (Eq_left M M' \<rho> P)
  show ?case
    using Eq_left.IH by (simp add: compatible_step.Eq_left)
next
  case (Eq_right P P' \<rho> M)
  show ?case
    using Eq_right.IH by (simp add: compatible_step.Eq_right)
next
  case (Neg_body A A')
  show ?case
    using Neg_body.IH by (simp add: compatible_step.Neg_body)
next
  case (Conj_left A A' B)
  show ?case
    using Conj_left.IH by (simp add: compatible_step.Conj_left)
next
  case (Conj_right B B' A)
  show ?case
    using Conj_right.IH by (simp add: compatible_step.Conj_right)
next
  case (Disj_left A A' B)
  show ?case
    using Disj_left.IH by (simp add: compatible_step.Disj_left)
next
  case (Disj_right B B' A)
  show ?case
    using Disj_right.IH by (simp add: compatible_step.Disj_right)
next
  case (Imp_left A A' B)
  show ?case
    using Imp_left.IH by (simp add: compatible_step.Imp_left)
next
  case (Imp_right B B' A)
  show ?case
    using Imp_right.IH by (simp add: compatible_step.Imp_right)
next
  case (Forall_body A A' \<rho>)
  have body: "compatible_step R
      (subst (lift_subst s) A) (subst (lift_subst s) A')"
    by (rule Forall_body.IH)
  then show ?case
    by (simp add: compatible_step.Forall_body)
next
  case (Exists_body A A' \<rho>)
  have body: "compatible_step R
      (subst (lift_subst s) A) (subst (lift_subst s) A')"
    by (rule Exists_body.IH)
  then show ?case
    by (simp add: compatible_step.Exists_body)
qed

lemma compatible_beta_subst:
  assumes "compatible_step beta_contract A B"
  shows "compatible_step beta_contract (subst s A) (subst s B)"
  using assms beta_contract_subst
  by (rule compatible_step_subst)

lemma compatible_eta_subst:
  assumes "compatible_step eta_contract A B"
  shows "compatible_step eta_contract (subst s A) (subst s B)"
  using assms eta_contract_subst
  by (rule compatible_step_subst)

definition term_subst_typed :: "ctx \<Rightarrow> ctx \<Rightarrow> oterm env \<Rightarrow> bool" where
  "term_subst_typed \<Delta> \<Gamma> s \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Delta> n = Some \<sigma> \<longrightarrow> \<Gamma> \<turnstile> s n : \<sigma>)"

lemma term_subst_typed_Var:
  "term_subst_typed \<Gamma> \<Gamma> Var"
  unfolding term_subst_typed_def by auto

lemma term_subst_typedD:
  assumes "term_subst_typed \<Delta> \<Gamma> s"
    and "lookup \<Delta> n = Some \<sigma>"
  shows "\<Gamma> \<turnstile> s n : \<sigma>"
  using assms unfolding term_subst_typed_def by blast

lemma term_subst_preserves_typing:
  assumes "\<Delta> \<turnstile> M : \<tau>"
    and "term_subst_typed \<Delta> \<Gamma> s"
  shows "\<Gamma> \<turnstile> subst s M : \<tau>"
  using assms(1)
proof (rule substitution_preserves_typing)
  fix n \<sigma>
  assume lookup: "lookup \<Delta> n = Some \<sigma>"
  show "\<Gamma> \<turnstile> s n : \<sigma>"
    using assms(2) lookup
    by (rule term_subst_typedD)
qed

lemma term_subst_typed_lift:
  assumes "term_subst_typed \<Delta> \<Gamma> s"
  shows "term_subst_typed (\<sigma> # \<Delta>) (\<sigma> # \<Gamma>) (lift_subst s)"
proof (unfold term_subst_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Delta>) n = Some \<tau>"
  show "\<sigma> # \<Gamma> \<turnstile> lift_subst s n : \<tau>"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 by auto
  next
    case (Suc m)
    then have lookup_delta: "lookup \<Delta> m = Some \<tau>"
      using lookup by simp
    have "\<Gamma> \<turnstile> s m : \<tau>"
      using assms lookup_delta
      by (rule term_subst_typedD)
    then have "\<sigma> # \<Gamma> \<turnstile> shift (s m) : \<tau>"
      by (rule weakening_front)
    then show ?thesis
      using Suc unfolding shift_def by simp
  qed
qed

lemma term_subst_typed_extend:
  assumes "term_subst_typed \<Delta> \<Gamma> s"
    and "\<Gamma> \<turnstile> W : \<sigma>"
  shows "term_subst_typed (\<sigma> # \<Delta>) \<Gamma> (case_nat W s)"
proof (unfold term_subst_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Delta>) n = Some \<tau>"
  show "\<Gamma> \<turnstile> case_nat W s n : \<tau>"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 assms(2) by simp
  next
    case (Suc m)
    then have lookup_delta: "lookup \<Delta> m = Some \<tau>"
      using lookup by simp
    have "\<Gamma> \<turnstile> s m : \<tau>"
      using assms(1) lookup_delta
      by (rule term_subst_typedD)
    then show ?thesis
      using Suc by simp
  qed
qed

lemma beta_eta_equiv_subst:
  assumes equiv: "beta_eta_equiv \<Delta> \<tau> A B"
  shows "term_subst_typed \<Delta> \<Gamma> s \<Longrightarrow>
    beta_eta_equiv \<Gamma> \<tau> (subst s A) (subst s B)"
  using equiv
proof (induction arbitrary: \<Gamma> s)
  case (Refl \<Delta> M \<tau>)
  have "\<Gamma> \<turnstile> subst s M : \<tau>"
    using Refl.hyps Refl.prems by (rule term_subst_preserves_typing)
  then show ?case
    by (rule beta_eta_equiv.Refl)
next
  case (Beta \<Delta> M \<tau> N)
  have M_type: "\<Gamma> \<turnstile> subst s M : \<tau>"
    using Beta.hyps(1) Beta.prems by (rule term_subst_preserves_typing)
  have N_type: "\<Gamma> \<turnstile> subst s N : \<tau>"
    using Beta.hyps(2) Beta.prems by (rule term_subst_preserves_typing)
  have step: "compatible_step beta_contract (subst s M) (subst s N)"
    using Beta.hyps(3) by (rule compatible_beta_subst)
  show ?case
    using M_type N_type step by (rule beta_eta_equiv.Beta)
next
  case (Eta \<Delta> M \<tau> N)
  have M_type: "\<Gamma> \<turnstile> subst s M : \<tau>"
    using Eta.hyps(1) Eta.prems by (rule term_subst_preserves_typing)
  have N_type: "\<Gamma> \<turnstile> subst s N : \<tau>"
    using Eta.hyps(2) Eta.prems by (rule term_subst_preserves_typing)
  have step: "compatible_step eta_contract (subst s M) (subst s N)"
    using Eta.hyps(3) by (rule compatible_eta_subst)
  show ?case
    using M_type N_type step by (rule beta_eta_equiv.Eta)
next
  case (Sym \<Delta> \<tau> M N)
  then have "beta_eta_equiv \<Gamma> \<tau> (subst s M) (subst s N)"
    by blast
  then show ?case
    by (rule beta_eta_equiv.Sym)
next
  case (Trans \<Delta> \<tau> M N P)
  have MN: "beta_eta_equiv \<Gamma> \<tau> (subst s M) (subst s N)"
    using Trans.IH(1) Trans.prems by blast
  have NP: "beta_eta_equiv \<Gamma> \<tau> (subst s N) (subst s P)"
    using Trans.IH(2) Trans.prems by blast
  show ?case
    using MN NP by (rule beta_eta_equiv.Trans)
qed

lemma subst_const_subst:
  assumes s'_def: "\<And>n. s' n = subst_const c \<sigma> N (s n)"
    and N'_subst: "subst s' N' = N"
  shows "subst_const c \<sigma> N (subst s A) =
    subst s' (subst_const c \<sigma> N' A)"
  using s'_def N'_subst
proof (induction A arbitrary: s s' N N')
  case (Var n)
  then show ?case
    by simp
next
  case (Const d \<tau>)
  then show ?case
    by simp
next
  case (App M P)
  then show ?case
    by simp
next
  case (Lam \<rho> M)
  have lift_def: "\<And>n. lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
  proof -
    fix n
    show "lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst_const c \<sigma> (shift N) (rename Suc (s m)) =
          rename Suc (subst_const c \<sigma> N (s m))"
        unfolding shift_def
        using subst_const_rename[of c \<sigma> Suc N "s m"] by simp
      then show ?thesis
        using Suc Lam.prems(1)[of m] by simp
    qed
  qed
  have shifted_subst: "subst (lift_subst s') (shift N') = shift N"
    using subst_lift_shift[of s' N'] Lam.prems(2) by simp
  have "subst_const c \<sigma> (shift N) (subst (lift_subst s) M) =
      subst (lift_subst s') (subst_const c \<sigma> (shift N') M)"
    using lift_def shifted_subst by (rule Lam.IH)
  then show ?case
    by simp
next
  case (Eq \<rho> M P)
  then show ?case
    by simp
next
  case (Neg A)
  then show ?case
    by simp
next
  case (Conj A B)
  then show ?case
    by simp
next
  case (Disj A B)
  then show ?case
    by simp
next
  case (Imp A B)
  then show ?case
    by simp
next
  case (Forall \<rho> A)
  have lift_def: "\<And>n. lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
  proof -
    fix n
    show "lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst_const c \<sigma> (shift N) (rename Suc (s m)) =
          rename Suc (subst_const c \<sigma> N (s m))"
        unfolding shift_def
        using subst_const_rename[of c \<sigma> Suc N "s m"] by simp
      then show ?thesis
        using Suc Forall.prems(1)[of m] by simp
    qed
  qed
  have shifted_subst: "subst (lift_subst s') (shift N') = shift N"
    using subst_lift_shift[of s' N'] Forall.prems(2) by simp
  have "subst_const c \<sigma> (shift N) (subst (lift_subst s) A) =
      subst (lift_subst s') (subst_const c \<sigma> (shift N') A)"
    using lift_def shifted_subst by (rule Forall.IH)
  then show ?case
    by simp
next
  case (Exists \<rho> A)
  have lift_def: "\<And>n. lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
  proof -
    fix n
    show "lift_subst s' n =
      subst_const c \<sigma> (shift N) (lift_subst s n)"
    proof (cases n)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      have "subst_const c \<sigma> (shift N) (rename Suc (s m)) =
          rename Suc (subst_const c \<sigma> N (s m))"
        unfolding shift_def
        using subst_const_rename[of c \<sigma> Suc N "s m"] by simp
      then show ?thesis
        using Suc Exists.prems(1)[of m] by simp
    qed
  qed
  have shifted_subst: "subst (lift_subst s') (shift N') = shift N"
    using subst_lift_shift[of s' N'] Exists.prems(2) by simp
  have "subst_const c \<sigma> (shift N) (subst (lift_subst s) A) =
      subst (lift_subst s') (subst_const c \<sigma> (shift N') A)"
    using lift_def shifted_subst by (rule Exists.IH)
  then show ?case
    by simp
qed

lemma subst_const_subst0:
  "subst_const c \<sigma> N (subst0 T A) =
    subst0 (subst_const c \<sigma> N T) (subst_const c \<sigma> (shift N) A)"
proof -
  let ?s = "case_nat T Var"
  let ?s' = "case_nat (subst_const c \<sigma> N T) Var"
  have s'_def: "\<And>n. ?s' n = subst_const c \<sigma> N (?s n)"
    by (case_tac n; simp)
  have shifted_subst: "subst ?s' (shift N) = N"
    using subst0_shift[of "subst_const c \<sigma> N T" N]
    unfolding subst0_def by simp
  show ?thesis
    unfolding subst0_def
    using subst_const_subst[OF s'_def shifted_subst, of A] by simp
qed

lemma subst0_abstract_const[simp]:
  "subst0 (Const c \<sigma>) (abstract_const c \<sigma> A) = A"
proof -
  let ?s = "case_nat (Const c \<sigma>) Var"
  have s_def: "\<And>n. ?s n = subst_const c \<sigma> (Const c \<sigma>) (?s n)"
    by simp
  have var_subst: "subst ?s (Var 0) = Const c \<sigma>"
    by simp
  have "subst ?s (subst_const c \<sigma> (Var 0) (shift A)) =
      subst_const c \<sigma> (Const c \<sigma>) (subst ?s (shift A))"
    using subst_const_subst[OF s_def var_subst, of "shift A"] by simp
  also have "... = subst ?s (shift A)"
    by simp
  also have "... = A"
    using subst0_shift[of "Const c \<sigma>" A] unfolding subst0_def by simp
  finally show ?thesis
    unfolding abstract_const_def subst0_def .
qed

lemma subst0_rename_lift_Suc_var0[simp]:
  "subst0 (Var 0) (rename (lift_ren Suc) A) = A"
  unfolding subst0_def
  by (rule subst_rename_inverse) (case_tac n; simp)

lemma rename_subst0:
  "rename r (subst0 T A) = subst0 (rename r T) (rename (lift_ren r) A)"
proof -
  let ?s = "case_nat T Var"
  let ?t = "case_nat (rename r T) Var"
  have lhs: "rename r (subst0 T A) =
      subst (\<lambda>n. rename r (?s n)) A"
    unfolding subst0_def by (simp add: rename_subst)
  have rhs: "subst0 (rename r T) (rename (lift_ren r) A) =
      subst (?t \<circ> lift_ren r) A"
    unfolding subst0_def by (simp add: subst_rename)
  have maps: "\<And>n. rename r (?s n) = (?t \<circ> lift_ren r) n"
    by (case_tac n; simp add: comp_def)
  have "subst (\<lambda>n. rename r (?s n)) A =
      subst (?t \<circ> lift_ren r) A"
    by (rule subst_cong) (rule maps)
  then show ?thesis
    using lhs rhs by simp
qed

lemma shift_subst0:
  "shift (subst0 T A) = subst0 (shift T) (rename (lift_ren Suc) A)"
  unfolding shift_def
  using rename_subst0[of Suc T A] by simp

lemma abstract_const_subst0_const_fresh:
  assumes "c \<notin> consts_of A"
  shows "abstract_const c \<sigma> (subst0 (Const c \<sigma>) A) = A"
proof -
  let ?A = "rename (lift_ren Suc) A"
  have fresh_lift: "c \<notin> consts_of (rename (lift_ren Suc) A)"
    using assms by simp
  have "subst_const c \<sigma> (Var 0) (shift (subst0 (Const c \<sigma>) A)) =
      subst_const c \<sigma> (Var 0) (subst0 (Const c \<sigma>) ?A)"
    using shift_subst0[of "Const c \<sigma>" A] by (simp add: shift_def)
  also have "... = subst0 (subst_const c \<sigma> (Var 0) (Const c \<sigma>))
      (subst_const c \<sigma> (shift (Var 0)) ?A)"
    by (rule subst_const_subst0)
  also have "... = subst0 (Var 0) ?A"
    using fresh_lift by (simp add: shift_def)
  also have "... = A"
    by simp
  finally have "subst_const c \<sigma> (Var 0) (shift (subst0 (Const c \<sigma>) A)) = A" .
  then show ?thesis
    unfolding abstract_const_def by simp
qed

lemma abstract_const_image_fresh_set:
  assumes "c \<notin> consts_of_set T"
  shows "abstract_const c \<sigma> ` T = shift ` T"
proof
  show "abstract_const c \<sigma> ` T \<subseteq> shift ` T"
  proof
    fix A
    assume "A \<in> abstract_const c \<sigma> ` T"
    then obtain B where B_in: "B \<in> T" and A_def: "A = abstract_const c \<sigma> B"
      by blast
    have "c \<notin> consts_of B"
      using assms B_in consts_of_setI by blast
    then show "A \<in> shift ` T"
      using B_in A_def abstract_const_fresh by auto
  qed
  show "shift ` T \<subseteq> abstract_const c \<sigma> ` T"
  proof
    fix A
    assume "A \<in> shift ` T"
    then obtain B where B_in: "B \<in> T" and A_def: "A = shift B"
      by blast
    have "c \<notin> consts_of B"
      using assms B_in consts_of_setI by blast
    then have "abstract_const c \<sigma> B = shift B"
      by (rule abstract_const_fresh)
    then have "A = abstract_const c \<sigma> B"
      using A_def by simp
    then show "A \<in> abstract_const c \<sigma> ` T"
      using B_in by blast
  qed
qed

lemma shift_ObjTrue[simp]:
  "shift ObjTrue = ObjTrue"
  by (simp add: ObjTrue_def shift_def)

lemma shift_ObjFalse[simp]:
  "shift ObjFalse = ObjFalse"
proof -
  have true_ren: "rename Suc ObjTrue = ObjTrue"
    using shift_ObjTrue unfolding shift_def .
  show ?thesis
    using true_ren by (simp add: ObjFalse_def shift_def)
qed

lemma abstract_const_ObjFalse[simp]:
  "abstract_const c \<sigma> ObjFalse = ObjFalse"
proof -
  have fresh: "c \<notin> consts_of ObjFalse"
    by (simp add: ObjFalse_def ObjTrue_def)
  have "abstract_const c \<sigma> ObjFalse = shift ObjFalse"
    using fresh by (rule abstract_const_fresh)
  then show ?thesis
    by simp
qed

lemma prop_eval_rename:
  "prop_eval v (rename r A) =
    prop_eval (\<lambda>B. prop_eval v (rename r B)) A"
  by (induction A arbitrary: r) auto

lemma prop_tautology_rename:
  assumes "prop_tautology \<Gamma> A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "prop_tautology \<Delta> (rename r A)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) unfolding prop_tautology_def by blast
  have rename_type: "\<Delta> \<turnstile> rename r A : Prop"
    using A_type assms(2) by (rule renaming_preserves_typing)
  have eval: "\<forall>v. prop_eval v (rename r A)"
  proof
    fix v
    let ?v' = "\<lambda>B. prop_eval v (rename r B)"
    have "prop_eval ?v' A"
      using assms(1) unfolding prop_tautology_def by blast
    then show "prop_eval v (rename r A)"
      using prop_eval_rename[of v r A] by simp
  qed
  show ?thesis
    using rename_type eval unfolding prop_tautology_def by blast
qed

lemma beta_contract_rename:
  assumes "M \<rightarrow>\<^sub>\<beta> P"
  shows "rename r M \<rightarrow>\<^sub>\<beta> rename r P"
  using assms
proof cases
  case (beta \<rho> A T)
  then show ?thesis
    by (auto simp add: rename_subst0 intro: beta_contract.beta)
qed

lemma eta_contract_rename:
  assumes "M \<rightarrow>\<^sub>\<eta> P"
  shows "rename r M \<rightarrow>\<^sub>\<eta> rename r P"
  using assms
proof cases
  case (eta F)
  then show ?thesis
    by (auto simp add: shift_rename_lift[symmetric] intro: eta_contract.eta)
qed

lemma compatible_step_rename:
  assumes step: "compatible_step R A B"
    and root_pres: "\<And>r M P. R M P \<Longrightarrow> R (rename r M) (rename r P)"
  shows "compatible_step R (rename r A) (rename r B)"
  using step
proof (induction arbitrary: r)
  case (root M P)
  show ?case
    by (rule compatible_step.root, rule root_pres, rule root.hyps)
next
  case (App_left M M' P)
  show ?case
    using App_left.IH by (simp add: compatible_step.App_left)
next
  case (App_right P P' M)
  show ?case
    using App_right.IH by (simp add: compatible_step.App_right)
next
  case (Lam_body M M' \<rho>)
  have body: "compatible_step R (rename (lift_ren r) M) (rename (lift_ren r) M')"
    by (rule Lam_body.IH)
  then show ?case
    by (simp add: compatible_step.Lam_body)
next
  case (Eq_left M M' \<rho> P)
  show ?case
    using Eq_left.IH by (simp add: compatible_step.Eq_left)
next
  case (Eq_right P P' \<rho> M)
  show ?case
    using Eq_right.IH by (simp add: compatible_step.Eq_right)
next
  case (Neg_body A A')
  show ?case
    using Neg_body.IH by (simp add: compatible_step.Neg_body)
next
  case (Conj_left A A' B)
  show ?case
    using Conj_left.IH by (simp add: compatible_step.Conj_left)
next
  case (Conj_right B B' A)
  show ?case
    using Conj_right.IH by (simp add: compatible_step.Conj_right)
next
  case (Disj_left A A' B)
  show ?case
    using Disj_left.IH by (simp add: compatible_step.Disj_left)
next
  case (Disj_right B B' A)
  show ?case
    using Disj_right.IH by (simp add: compatible_step.Disj_right)
next
  case (Imp_left A A' B)
  show ?case
    using Imp_left.IH by (simp add: compatible_step.Imp_left)
next
  case (Imp_right B B' A)
  show ?case
    using Imp_right.IH by (simp add: compatible_step.Imp_right)
next
  case (Forall_body A A' \<rho>)
  have body: "compatible_step R (rename (lift_ren r) A) (rename (lift_ren r) A')"
    by (rule Forall_body.IH)
  then show ?case
    by (simp add: compatible_step.Forall_body)
next
  case (Exists_body A A' \<rho>)
  have body: "compatible_step R (rename (lift_ren r) A) (rename (lift_ren r) A')"
    by (rule Exists_body.IH)
  then show ?case
    by (simp add: compatible_step.Exists_body)
qed

lemma compatible_beta_rename:
  assumes "compatible_step beta_contract A B"
  shows "compatible_step beta_contract (rename r A) (rename r B)"
  using assms beta_contract_rename
  by (rule compatible_step_rename)

lemma compatible_eta_rename:
  assumes "compatible_step eta_contract A B"
  shows "compatible_step eta_contract (rename r A) (rename r B)"
  using assms eta_contract_rename
  by (rule compatible_step_rename)

lemma beta_contract_subst_const:
  assumes "M \<rightarrow>\<^sub>\<beta> P"
  shows "subst_const c \<sigma> N M \<rightarrow>\<^sub>\<beta> subst_const c \<sigma> N P"
  using assms
proof cases
  case (beta \<rho> A T)
  then show ?thesis
    by (auto simp add: subst_const_subst0 intro: beta_contract.beta)
qed

lemma eta_contract_subst_const:
  assumes "M \<rightarrow>\<^sub>\<eta> P"
  shows "subst_const c \<sigma> N M \<rightarrow>\<^sub>\<eta> subst_const c \<sigma> N P"
  using assms
proof cases
  case (eta F)
  then show ?thesis
    by (auto simp add: subst_const_shift intro: eta_contract.eta)
qed

lemma compatible_step_subst_const:
  assumes step: "compatible_step R A B"
    and root_pres: "\<And>N M P. R M P \<Longrightarrow>
      R (subst_const c \<sigma> N M) (subst_const c \<sigma> N P)"
  shows "compatible_step R (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
  using step
proof (induction arbitrary: N)
  case (root M P)
  show ?case
    using root_pres[OF root.hyps, of N] by (rule compatible_step.root)
next
  case (App_left M M' P)
  show ?case
    using App_left.IH by (simp add: compatible_step.App_left)
next
  case (App_right P P' M)
  show ?case
    using App_right.IH by (simp add: compatible_step.App_right)
next
  case (Lam_body M M' \<rho>)
  have body: "compatible_step R
      (subst_const c \<sigma> (shift N) M)
      (subst_const c \<sigma> (shift N) M')"
    by (rule Lam_body.IH)
  then show ?case
    by (simp add: compatible_step.Lam_body)
next
  case (Eq_left M M' \<rho> P)
  show ?case
    using Eq_left.IH by (simp add: compatible_step.Eq_left)
next
  case (Eq_right P P' \<rho> M)
  show ?case
    using Eq_right.IH by (simp add: compatible_step.Eq_right)
next
  case (Neg_body A A')
  show ?case
    using Neg_body.IH by (simp add: compatible_step.Neg_body)
next
  case (Conj_left A A' B)
  show ?case
    using Conj_left.IH by (simp add: compatible_step.Conj_left)
next
  case (Conj_right B B' A)
  show ?case
    using Conj_right.IH by (simp add: compatible_step.Conj_right)
next
  case (Disj_left A A' B)
  show ?case
    using Disj_left.IH by (simp add: compatible_step.Disj_left)
next
  case (Disj_right B B' A)
  show ?case
    using Disj_right.IH by (simp add: compatible_step.Disj_right)
next
  case (Imp_left A A' B)
  show ?case
    using Imp_left.IH by (simp add: compatible_step.Imp_left)
next
  case (Imp_right B B' A)
  show ?case
    using Imp_right.IH by (simp add: compatible_step.Imp_right)
next
  case (Forall_body A A' \<rho>)
  have body: "compatible_step R
      (subst_const c \<sigma> (shift N) A)
      (subst_const c \<sigma> (shift N) A')"
    by (rule Forall_body.IH)
  then show ?case
    by (simp add: compatible_step.Forall_body)
next
  case (Exists_body A A' \<rho>)
  have body: "compatible_step R
      (subst_const c \<sigma> (shift N) A)
      (subst_const c \<sigma> (shift N) A')"
    by (rule Exists_body.IH)
  then show ?case
    by (simp add: compatible_step.Exists_body)
qed

lemma compatible_beta_subst_const:
  assumes "compatible_step beta_contract A B"
  shows "compatible_step beta_contract
    (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
  using assms beta_contract_subst_const
  by (rule compatible_step_subst_const)

lemma compatible_eta_subst_const:
  assumes "compatible_step eta_contract A B"
  shows "compatible_step eta_contract
    (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
  using assms eta_contract_subst_const
  by (rule compatible_step_subst_const)

lemma prop_eval_subst_const:
  "prop_eval v (subst_const c \<sigma> N A) =
    prop_eval (\<lambda>B. prop_eval v (subst_const c \<sigma> N B)) A"
  by (induction A arbitrary: N) auto

lemma prop_tautology_subst_const:
  assumes "prop_tautology \<Gamma> A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "prop_tautology \<Gamma> (subst_const c \<sigma> N A)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) unfolding prop_tautology_def by blast
  have subst_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using A_type assms(2) by (rule subst_const_preserves_typing)
  have eval: "\<forall>v. prop_eval v (subst_const c \<sigma> N A)"
  proof
    fix v
    let ?v' = "\<lambda>B. prop_eval v (subst_const c \<sigma> N B)"
    have "prop_eval ?v' A"
      using assms(1) unfolding prop_tautology_def by blast
    then show "prop_eval v (subst_const c \<sigma> N A)"
      using prop_eval_subst_const[of v c \<sigma> N A] by simp
  qed
  show ?thesis
    using subst_type eval unfolding prop_tautology_def by blast
qed

lemma H_proves_rename:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> \<turnstile>\<^sub>H rename r A"
  using assms
proof (induction arbitrary: \<Delta> r rule: H_proves.induct)
  case (PC \<Gamma> A)
  have "prop_tautology \<Delta> (rename r A)"
    using PC.hyps PC.prems by (rule prop_tautology_rename)
  then show ?case
    by (rule H_proves.PC)
next
  case (UI \<rho> \<Gamma> A T)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using UI.prems by (rule lookup_lift_ren)
  have A_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) A : Prop"
    using UI.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have T_ren_type: "\<Delta> \<turnstile> rename r T : \<rho>"
    using UI.hyps(2) UI.prems by (rule renaming_preserves_typing)
  have "\<Delta> \<turnstile>\<^sub>H Imp (Forall \<rho> (rename (lift_ren r) A))
      (subst0 (rename r T) (rename (lift_ren r) A))"
    using A_ren_type T_ren_type by (rule H_proves.UI)
  then show ?case
    by (simp add: rename_subst0)
next
  case (EG \<rho> \<Gamma> A T)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using EG.prems by (rule lookup_lift_ren)
  have A_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) A : Prop"
    using EG.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have T_ren_type: "\<Delta> \<turnstile> rename r T : \<rho>"
    using EG.hyps(2) EG.prems by (rule renaming_preserves_typing)
  have "\<Delta> \<turnstile>\<^sub>H Imp
      (subst0 (rename r T) (rename (lift_ren r) A))
      (Exists \<rho> (rename (lift_ren r) A))"
    using A_ren_type T_ren_type by (rule H_proves.EG)
  then show ?case
    by (simp add: rename_subst0)
next
  case (Ref \<Gamma> M \<rho>)
  have "\<Delta> \<turnstile> rename r M : \<rho>"
    using Ref.hyps Ref.prems by (rule renaming_preserves_typing)
  then show ?case
    by (simp add: H_proves.Ref)
next
  case (LL \<Gamma> A \<rho> B F)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : \<rho>"
    using LL.hyps(1) LL.prems by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : \<rho>"
    using LL.hyps(2) LL.prems by (rule renaming_preserves_typing)
  have F_ren_type: "\<Delta> \<turnstile> rename r F : \<rho> \<rightarrow>\<^sub>o Prop"
    using LL.hyps(3) LL.prems by (rule renaming_preserves_typing)
  have "\<Delta> \<turnstile>\<^sub>H Imp (Eq \<rho> (rename r A) (rename r B))
      (Imp (App (rename r F) (rename r A))
        (App (rename r F) (rename r B)))"
    using A_ren_type B_ren_type F_ren_type by (rule H_proves.LL)
  then show ?case
    by simp
next
  case (Beta \<Gamma> A B)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Beta.hyps(1) Beta.prems by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : Prop"
    using Beta.hyps(2) Beta.prems by (rule renaming_preserves_typing)
  have step: "compatible_step beta_contract (rename r A) (rename r B)"
    using Beta.hyps(3) by (rule compatible_beta_rename)
  have "\<Delta> \<turnstile>\<^sub>H (rename r A \<longleftrightarrow>\<^sub>o rename r B)"
    using A_ren_type B_ren_type step by (rule H_proves.Beta)
  then show ?case
    by simp
next
  case (Eta \<Gamma> A B)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Eta.hyps(1) Eta.prems by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : Prop"
    using Eta.hyps(2) Eta.prems by (rule renaming_preserves_typing)
  have step: "compatible_step eta_contract (rename r A) (rename r B)"
    using Eta.hyps(3) by (rule compatible_eta_rename)
  have "\<Delta> \<turnstile>\<^sub>H (rename r A \<longleftrightarrow>\<^sub>o rename r B)"
    using A_ren_type B_ren_type step by (rule H_proves.Eta)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Delta> \<turnstile>\<^sub>H rename r A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Delta> \<turnstile>\<^sub>H rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Delta> \<turnstile>\<^sub>H Imp (rename r A) (rename r B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule H_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Gen.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<Delta> \<turnstile> rename r P : Prop"
    using Gen.hyps(1) Gen.prems by (rule renaming_preserves_typing)
  have Q_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) Q : Prop"
    using Gen.hyps(2) lift_rel by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>H
      rename (lift_ren r) (Imp (shift P) Q)"
    using lift_rel by (rule Gen.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>H
      Imp (shift (rename r P)) (rename (lift_ren r) Q)"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>H Imp (rename r P)
      (Forall \<rho> (rename (lift_ren r) Q))"
    using P_ren_type Q_ren_type d_ext by (rule H_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Inst.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) P : Prop"
    using Inst.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have Q_ren_type: "\<Delta> \<turnstile> rename r Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>H
      rename (lift_ren r) (Imp P (shift Q))"
    using lift_rel by (rule Inst.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>H
      Imp (rename (lift_ren r) P) (shift (rename r Q))"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>H Imp (Exists \<rho> (rename (lift_ren r) P)) (rename r Q)"
    using P_ren_type Q_ren_type d_ext by (rule H_proves.Inst)
  then show ?case
    by simp
qed

lemma H_proves_subst_const:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
  using assms
proof (induction arbitrary: N \<sigma> c rule: H_proves.induct)
  case (PC \<Gamma> A)
  have "prop_tautology \<Gamma> (subst_const c \<sigma> N A)"
    using PC.hyps PC.prems by (rule prop_tautology_subst_const)
  then show ?case
    by (rule H_proves.PC)
next
  case (UI \<rho> \<Gamma> A T)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using UI.prems by (rule weakening_front)
  have A_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) A : Prop"
    using UI.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have T_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N T : \<rho>"
    using UI.hyps(2) UI.prems by (rule subst_const_preserves_typing)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (Forall \<rho> (subst_const c \<sigma> (shift N) A))
      (subst0 (subst_const c \<sigma> N T) (subst_const c \<sigma> (shift N) A))"
    using A_sub_type T_sub_type by (rule H_proves.UI)
  then show ?case
    by (simp add: subst_const_subst0)
next
  case (EG \<rho> \<Gamma> A T)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using EG.prems by (rule weakening_front)
  have A_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) A : Prop"
    using EG.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have T_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N T : \<rho>"
    using EG.hyps(2) EG.prems by (rule subst_const_preserves_typing)
  have "\<Gamma> \<turnstile>\<^sub>H Imp
      (subst0 (subst_const c \<sigma> N T) (subst_const c \<sigma> (shift N) A))
      (Exists \<rho> (subst_const c \<sigma> (shift N) A))"
    using A_sub_type T_sub_type by (rule H_proves.EG)
  then show ?case
    by (simp add: subst_const_subst0)
next
  case (Ref \<Gamma> M \<rho>)
  have "\<Gamma> \<turnstile> subst_const c \<sigma> N M : \<rho>"
    using Ref.hyps Ref.prems by (rule subst_const_preserves_typing)
  then show ?case
    by (simp add: H_proves.Ref)
next
  case (LL \<Gamma> A \<rho> B F)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : \<rho>"
    using LL.hyps(1) LL.prems by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : \<rho>"
    using LL.hyps(2) LL.prems by (rule subst_const_preserves_typing)
  have F_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N F : \<rho> \<rightarrow>\<^sub>o Prop"
    using LL.hyps(3) LL.prems by (rule subst_const_preserves_typing)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (Eq \<rho> (subst_const c \<sigma> N A) (subst_const c \<sigma> N B))
      (Imp (App (subst_const c \<sigma> N F) (subst_const c \<sigma> N A))
        (App (subst_const c \<sigma> N F) (subst_const c \<sigma> N B)))"
    using A_sub_type B_sub_type F_sub_type by (rule H_proves.LL)
  then show ?case
    by simp
next
  case (Beta \<Gamma> A B)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Beta.hyps(1) Beta.prems by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using Beta.hyps(2) Beta.prems by (rule subst_const_preserves_typing)
  have step: "compatible_step beta_contract
      (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using Beta.hyps(3) by (rule compatible_beta_subst_const)
  have "\<Gamma> \<turnstile>\<^sub>H
      (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o subst_const c \<sigma> N B)"
    using A_sub_type B_sub_type step by (rule H_proves.Beta)
  then show ?case
    by simp
next
  case (Eta \<Gamma> A B)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Eta.hyps(1) Eta.prems by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using Eta.hyps(2) Eta.prems by (rule subst_const_preserves_typing)
  have step: "compatible_step eta_contract
      (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using Eta.hyps(3) by (rule compatible_eta_subst_const)
  have "\<Gamma> \<turnstile>\<^sub>H
      (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o subst_const c \<sigma> N B)"
    using A_sub_type B_sub_type step by (rule H_proves.Eta)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Gamma> \<turnstile>\<^sub>H subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Gamma> \<turnstile>\<^sub>H
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule H_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Gen.prems by (rule weakening_front)
  have P_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : Prop"
    using Gen.hyps(1) Gen.prems by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) Q : Prop"
    using Gen.hyps(2) shifted_N by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>H
      subst_const c \<sigma> (shift N) (Imp (shift P) Q)"
    using shifted_N by (rule Gen.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>H
      Imp (shift (subst_const c \<sigma> N P)) (subst_const c \<sigma> (shift N) Q)"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (subst_const c \<sigma> N P)
      (Forall \<rho> (subst_const c \<sigma> (shift N) Q))"
    using P_sub_type Q_sub_type d_ext by (rule H_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Inst.prems by (rule weakening_front)
  have P_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) P : Prop"
    using Inst.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>H
      subst_const c \<sigma> (shift N) (Imp P (shift Q))"
    using shifted_N by (rule Inst.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>H
      Imp (subst_const c \<sigma> (shift N) P) (shift (subst_const c \<sigma> N Q))"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (Exists \<rho> (subst_const c \<sigma> (shift N) P))
      (subst_const c \<sigma> N Q)"
    using P_sub_type Q_sub_type d_ext by (rule H_proves.Inst)
  then show ?case
    by simp
qed

lemma H_derivable_subst_const:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule subst_const_preserves_typing)
  have "subst_const c \<sigma> N A \<in> set (map (subst_const c \<sigma> N) \<Delta>)"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_sub_type by (rule H_derivable.Assumption)
next
  case (Theorem \<Gamma> A \<Delta>)
  have "\<Gamma> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule H_proves_subst_const)
  then show ?case
    by (rule H_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have dA: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp_raw: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>H
      subst_const c \<sigma> N (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have dImp: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>H
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule H_derivable.Derive_MP)
qed

lemma H_derivable_rename:
  assumes "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>H rename r A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Sigma> \<Gamma>)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule renaming_preserves_typing)
  have "rename r A \<in> set (map (rename r) \<Sigma>)"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_ren_type by (rule H_derivable.Assumption)
next
  case (Theorem \<Gamma> A \<Sigma>)
  have "\<Delta> \<turnstile>\<^sub>H rename r A"
    using Theorem.hyps Theorem.prems by (rule H_proves_rename)
  then show ?case
    by (rule H_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Sigma> A B)
  have dA: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>H rename r A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp_raw: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>H rename r (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have dImp: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>H Imp (rename r A) (rename r B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule H_derivable.Derive_MP)
qed

lemma lift_ren_three_two[simp]:
  "lift_ren (lift_ren (lift_ren r)) 2 = 2"
  by (simp add: numeral_2_eq_2)

lemma rename_boolean_identity[simp]:
  assumes "A \<in> set all_boolean_identities"
  shows "rename r A = A"
  using assms
  by (auto simp: all_boolean_identities_def bool_comm_conj_def bool_comm_disj_def
      bool_dist_conj_disj_def bool_dist_disj_conj_def
      bool_dissolve_conj_disj_def bool_dissolve_disj_conj_def)

lemma rename_classic_identity_identity[simp]:
  "rename r (classic_identity_identity \<sigma>) = classic_identity_identity \<sigma>"
  by (simp add: classic_identity_identity_def)

lemma rename_classic_absorb_disj_forall[simp]:
  "rename r (classic_absorb_disj_forall \<sigma>) = classic_absorb_disj_forall \<sigma>"
  by (simp add: classic_absorb_disj_forall_def)

lemma rename_classic_dist_disj_forall[simp]:
  "rename r (classic_dist_disj_forall \<sigma>) = classic_dist_disj_forall \<sigma>"
  by (simp add: classic_dist_disj_forall_def)

lemma rename_classic_absorb_conj_exists[simp]:
  "rename r (classic_absorb_conj_exists \<sigma>) = classic_absorb_conj_exists \<sigma>"
  by (simp add: classic_absorb_conj_exists_def)

lemma rename_classic_dist_conj_exists[simp]:
  "rename r (classic_dist_conj_exists \<sigma>) = classic_dist_conj_exists \<sigma>"
  by (simp add: classic_dist_conj_exists_def)

lemma subst_const_boolean_identity[simp]:
  assumes "A \<in> set all_boolean_identities"
  shows "subst_const c \<sigma> N A = A"
  using assms
  by (auto simp: all_boolean_identities_def bool_comm_conj_def bool_comm_disj_def
      bool_dist_conj_disj_def bool_dist_disj_conj_def
      bool_dissolve_conj_disj_def bool_dissolve_disj_conj_def)

lemma subst_const_classic_identity_identity[simp]:
  "subst_const c \<tau> N (classic_identity_identity \<sigma>) =
    classic_identity_identity \<sigma>"
  by (simp add: classic_identity_identity_def)

lemma subst_const_classic_absorb_disj_forall[simp]:
  "subst_const c \<tau> N (classic_absorb_disj_forall \<sigma>) =
    classic_absorb_disj_forall \<sigma>"
  by (simp add: classic_absorb_disj_forall_def)

lemma subst_const_classic_dist_disj_forall[simp]:
  "subst_const c \<tau> N (classic_dist_disj_forall \<sigma>) =
    classic_dist_disj_forall \<sigma>"
  by (simp add: classic_dist_disj_forall_def)

lemma subst_const_classic_absorb_conj_exists[simp]:
  "subst_const c \<tau> N (classic_absorb_conj_exists \<sigma>) =
    classic_absorb_conj_exists \<sigma>"
  by (simp add: classic_absorb_conj_exists_def)

lemma subst_const_classic_dist_conj_exists[simp]:
  "subst_const c \<tau> N (classic_dist_conj_exists \<sigma>) =
    classic_dist_conj_exists \<sigma>"
  by (simp add: classic_dist_conj_exists_def)

lemma C_proves_subst_const:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
  using assms
proof (induction arbitrary: N \<sigma> c rule: C_proves.induct)
  case (H \<Gamma> A)
  have "\<Gamma> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
    using H.hyps H.prems by (rule H_proves_subst_const)
  then show ?case
    by (rule C_proves.H)
next
  case (BooleanIdentity A \<Gamma>)
  have "\<Gamma> \<turnstile>\<^sub>C A"
    using BooleanIdentity.hyps by (rule C_proves.BooleanIdentity)
  then show ?case
    using BooleanIdentity.hyps by simp
next
  case (IdentityIdentity \<Gamma> \<rho>)
  have "\<Gamma> \<turnstile>\<^sub>C classic_identity_identity \<rho>"
    by (rule C_proves.IdentityIdentity)
  then show ?case
    by simp
next
  case (AbsorbDisjForall \<Gamma> \<rho>)
  have "\<Gamma> \<turnstile>\<^sub>C classic_absorb_disj_forall \<rho>"
    by (rule C_proves.AbsorbDisjForall)
  then show ?case
    by simp
next
  case (DistDisjForall \<Gamma> \<rho>)
  have "\<Gamma> \<turnstile>\<^sub>C classic_dist_disj_forall \<rho>"
    by (rule C_proves.DistDisjForall)
  then show ?case
    by simp
next
  case (AbsorbConjExists \<Gamma> \<rho>)
  have "\<Gamma> \<turnstile>\<^sub>C classic_absorb_conj_exists \<rho>"
    by (rule C_proves.AbsorbConjExists)
  then show ?case
    by simp
next
  case (DistConjExists \<Gamma> \<rho>)
  have "\<Gamma> \<turnstile>\<^sub>C classic_dist_conj_exists \<rho>"
    by (rule C_proves.DistConjExists)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Gamma> \<turnstile>\<^sub>C subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Gamma> \<turnstile>\<^sub>C
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule C_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Gen.prems by (rule weakening_front)
  have P_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : Prop"
    using Gen.hyps(1) Gen.prems by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) Q : Prop"
    using Gen.hyps(2) shifted_N by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>C
      subst_const c \<sigma> (shift N) (Imp (shift P) Q)"
    using shifted_N by (rule Gen.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>C
      Imp (shift (subst_const c \<sigma> N P)) (subst_const c \<sigma> (shift N) Q)"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>C Imp (subst_const c \<sigma> N P)
      (Forall \<rho> (subst_const c \<sigma> (shift N) Q))"
    using P_sub_type Q_sub_type d_ext by (rule C_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Inst.prems by (rule weakening_front)
  have P_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) P : Prop"
    using Inst.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>C
      subst_const c \<sigma> (shift N) (Imp P (shift Q))"
    using shifted_N by (rule Inst.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>C
      Imp (subst_const c \<sigma> (shift N) P) (shift (subst_const c \<sigma> N Q))"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>C Imp (Exists \<rho> (subst_const c \<sigma> (shift N) P))
      (subst_const c \<sigma> N Q)"
    using P_sub_type Q_sub_type d_ext by (rule C_proves.Inst)
  then show ?case
    by simp
qed

lemma C_proves_rename:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> \<turnstile>\<^sub>C rename r A"
  using assms
proof (induction arbitrary: \<Delta> r rule: C_proves.induct)
  case (H \<Gamma> A)
  have "\<Delta> \<turnstile>\<^sub>H rename r A"
    using H.hyps H.prems by (rule H_proves_rename)
  then show ?case
    by (rule C_proves.H)
next
  case (BooleanIdentity A \<Gamma>)
  have "\<Delta> \<turnstile>\<^sub>C A"
    using BooleanIdentity.hyps by (rule C_proves.BooleanIdentity)
  then show ?case
    using BooleanIdentity.hyps by simp
next
  case (IdentityIdentity \<Gamma> \<rho>)
  have "\<Delta> \<turnstile>\<^sub>C classic_identity_identity \<rho>"
    by (rule C_proves.IdentityIdentity)
  then show ?case
    by simp
next
  case (AbsorbDisjForall \<Gamma> \<rho>)
  have "\<Delta> \<turnstile>\<^sub>C classic_absorb_disj_forall \<rho>"
    by (rule C_proves.AbsorbDisjForall)
  then show ?case
    by simp
next
  case (DistDisjForall \<Gamma> \<rho>)
  have "\<Delta> \<turnstile>\<^sub>C classic_dist_disj_forall \<rho>"
    by (rule C_proves.DistDisjForall)
  then show ?case
    by simp
next
  case (AbsorbConjExists \<Gamma> \<rho>)
  have "\<Delta> \<turnstile>\<^sub>C classic_absorb_conj_exists \<rho>"
    by (rule C_proves.AbsorbConjExists)
  then show ?case
    by simp
next
  case (DistConjExists \<Gamma> \<rho>)
  have "\<Delta> \<turnstile>\<^sub>C classic_dist_conj_exists \<rho>"
    by (rule C_proves.DistConjExists)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Delta> \<turnstile>\<^sub>C rename r A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Delta> \<turnstile>\<^sub>C rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Delta> \<turnstile>\<^sub>C Imp (rename r A) (rename r B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule C_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Gen.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<Delta> \<turnstile> rename r P : Prop"
    using Gen.hyps(1) Gen.prems by (rule renaming_preserves_typing)
  have Q_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) Q : Prop"
    using Gen.hyps(2) lift_rel by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>C
      rename (lift_ren r) (Imp (shift P) Q)"
    using lift_rel by (rule Gen.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>C
      Imp (shift (rename r P)) (rename (lift_ren r) Q)"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>C Imp (rename r P)
      (Forall \<rho> (rename (lift_ren r) Q))"
    using P_ren_type Q_ren_type d_ext by (rule C_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Inst.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) P : Prop"
    using Inst.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have Q_ren_type: "\<Delta> \<turnstile> rename r Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>C
      rename (lift_ren r) (Imp P (shift Q))"
    using lift_rel by (rule Inst.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>C
      Imp (rename (lift_ren r) P) (shift (rename r Q))"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>C Imp (Exists \<rho> (rename (lift_ren r) P)) (rename r Q)"
    using P_ren_type Q_ren_type d_ext by (rule C_proves.Inst)
  then show ?case
    by simp
qed

lemma CE_proves_subst_const:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
  using assms
proof (induction arbitrary: N \<sigma> c rule: CE_proves.induct)
  case (C \<Gamma> A)
  have "\<Gamma> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
    using C.hyps C.prems by (rule C_proves_subst_const)
  then show ?case
    by (rule CE_proves.C)
next
  case (PropEquivalence \<Gamma> A B)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using PropEquivalence.hyps(1) PropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using PropEquivalence.hyps(2) PropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_iff_raw: "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N (A \<longleftrightarrow>\<^sub>o B)"
    using PropEquivalence.prems by (rule PropEquivalence.IH)
  have d_iff: "\<Gamma> \<turnstile>\<^sub>CE
      (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o subst_const c \<sigma> N B)"
    using d_iff_raw by simp
  have "\<Gamma> \<turnstile>\<^sub>CE Eq Prop (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using A_sub_type B_sub_type d_iff by (rule CE_proves.PropEquivalence)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Gamma> \<turnstile>\<^sub>CE
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule CE_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Gen.prems by (rule weakening_front)
  have P_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : Prop"
    using Gen.hyps(1) Gen.prems by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) Q : Prop"
    using Gen.hyps(2) shifted_N by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>CE
      subst_const c \<sigma> (shift N) (Imp (shift P) Q)"
    using shifted_N by (rule Gen.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>CE
      Imp (shift (subst_const c \<sigma> N P)) (subst_const c \<sigma> (shift N) Q)"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>CE Imp (subst_const c \<sigma> N P)
      (Forall \<rho> (subst_const c \<sigma> (shift N) Q))"
    using P_sub_type Q_sub_type d_ext by (rule CE_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Inst.prems by (rule weakening_front)
  have P_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) P : Prop"
    using Inst.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>CE
      subst_const c \<sigma> (shift N) (Imp P (shift Q))"
    using shifted_N by (rule Inst.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>CE
      Imp (subst_const c \<sigma> (shift N) P) (shift (subst_const c \<sigma> N Q))"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>CE Imp (Exists \<rho> (subst_const c \<sigma> (shift N) P))
      (subst_const c \<sigma> N Q)"
    using P_sub_type Q_sub_type d_ext by (rule CE_proves.Inst)
  then show ?case
    by simp
qed

lemma CEV_proves_subst_const:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N A"
  using assms
proof (induction arbitrary: N \<sigma> c rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  have "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
    using CE.hyps CE.prems by (rule CE_proves_subst_const)
  then show ?case
    by (rule CEV_proves.CE)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  have shifted_N: "\<sigma>s @ \<Gamma> \<turnstile> shift_by (length \<sigma>s) N : \<sigma>"
    using VectorEquivalence.prems by (rule shift_by_preserves_typing)
  have F_sub_type:
      "\<Gamma> \<turnstile> subst_const c \<sigma> N F : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(1) VectorEquivalence.prems
    by (rule subst_const_preserves_typing)
  have G_sub_type:
      "\<Gamma> \<turnstile> subst_const c \<sigma> N G : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(2) VectorEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_zeta_raw:
      "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
        subst_const c \<sigma> (shift_by (length \<sigma>s) N) (zeta_body \<sigma>s F G)"
    using shifted_N by (rule VectorEquivalence.IH)
  have d_zeta:
      "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
        zeta_body \<sigma>s (subst_const c \<sigma> N F) (subst_const c \<sigma> N G)"
    using d_zeta_raw by (simp add: subst_const_zeta_body)
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (arrow_type \<sigma>s Prop)
        (subst_const c \<sigma> N F) (subst_const c \<sigma> N G)"
    using F_sub_type G_sub_type d_zeta by (rule CEV_proves.VectorEquivalence)
  then show ?case
    by simp
next
  case (ContextVectorEquivalence \<Gamma> A F \<sigma>s G)
  have shifted_N: "\<sigma>s @ \<Gamma> \<turnstile> shift_by (length \<sigma>s) N : \<sigma>"
    using ContextVectorEquivalence.prems by (rule shift_by_preserves_typing)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using ContextVectorEquivalence.hyps(1) ContextVectorEquivalence.prems
    by (rule subst_const_preserves_typing)
  have F_sub_type:
      "\<Gamma> \<turnstile> subst_const c \<sigma> N F : arrow_type \<sigma>s Prop"
    using ContextVectorEquivalence.hyps(2) ContextVectorEquivalence.prems
    by (rule subst_const_preserves_typing)
  have G_sub_type:
      "\<Gamma> \<turnstile> subst_const c \<sigma> N G : arrow_type \<sigma>s Prop"
    using ContextVectorEquivalence.hyps(3) ContextVectorEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_context_raw:
      "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
        subst_const c \<sigma> (shift_by (length \<sigma>s) N)
          (Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G))"
    using shifted_N by (rule ContextVectorEquivalence.IH)
  have d_context:
      "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift_by (length \<sigma>s) (subst_const c \<sigma> N A))
          (zeta_body \<sigma>s (subst_const c \<sigma> N F)
            (subst_const c \<sigma> N G))"
    using d_context_raw
    by (simp add: subst_const_shift_by subst_const_zeta_body)
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst_const c \<sigma> N A)
        (Eq (arrow_type \<sigma>s Prop)
          (subst_const c \<sigma> N F) (subst_const c \<sigma> N G))"
    using A_sub_type F_sub_type G_sub_type d_context
    by (rule CEV_proves.ContextVectorEquivalence)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule CEV_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Gen.prems by (rule weakening_front)
  have P_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N P : Prop"
    using Gen.hyps(1) Gen.prems by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) Q : Prop"
    using Gen.hyps(2) shifted_N by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>CEV
      subst_const c \<sigma> (shift N) (Imp (shift P) Q)"
    using shifted_N by (rule Gen.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (subst_const c \<sigma> N P)) (subst_const c \<sigma> (shift N) Q)"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (subst_const c \<sigma> N P)
      (Forall \<rho> (subst_const c \<sigma> (shift N) Q))"
    using P_sub_type Q_sub_type d_ext by (rule CEV_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have shifted_N: "\<rho> # \<Gamma> \<turnstile> shift N : \<sigma>"
    using Inst.prems by (rule weakening_front)
  have P_sub_type: "\<rho> # \<Gamma> \<turnstile> subst_const c \<sigma> (shift N) P : Prop"
    using Inst.hyps(1) shifted_N by (rule subst_const_preserves_typing)
  have Q_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule subst_const_preserves_typing)
  have d_ext_raw: "\<rho> # \<Gamma> \<turnstile>\<^sub>CEV
      subst_const c \<sigma> (shift N) (Imp P (shift Q))"
    using shifted_N by (rule Inst.IH)
  have d_ext: "\<rho> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst_const c \<sigma> (shift N) P) (shift (subst_const c \<sigma> N Q))"
    using d_ext_raw by (simp add: subst_const_shift)
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Exists \<rho> (subst_const c \<sigma> (shift N) P))
        (subst_const c \<sigma> N Q)"
    using P_sub_type Q_sub_type d_ext by (rule CEV_proves.Inst)
  then show ?case
    by simp
qed

lemma CEV_proves_rename_if_CE_rename:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>CEV A"
    and mapping:
      "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
        lookup \<Delta> (r n) = Some \<tau>"
    and ce_rename:
      "\<And>\<Gamma> A \<Delta> r. \<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow>
        (\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
          lookup \<Delta> (r n) = Some \<tau>) \<Longrightarrow>
        \<Delta> \<turnstile>\<^sub>CE rename r A"
  shows "\<Delta> \<turnstile>\<^sub>CEV rename r A"
  using derivation mapping
proof (induction arbitrary: \<Delta> r rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  have "\<Delta> \<turnstile>\<^sub>CE rename r A"
    using CE.hyps CE.prems by (rule ce_rename)
  then show ?case
    by (rule CEV_proves.CE)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  let ?r' = "prefix_ren (length \<sigma>s) r"
  have prefix_mapping:
      "\<And>n \<tau>. lookup (\<sigma>s @ \<Gamma>) n = Some \<tau> \<Longrightarrow>
        lookup (\<sigma>s @ \<Delta>) (?r' n) = Some \<tau>"
    using VectorEquivalence.prems
    by (rule prefix_ren_preserves_lookup)
  have F_ren_type:
      "\<Delta> \<turnstile> rename r F : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(1) VectorEquivalence.prems
    by (rule renaming_preserves_typing)
  have G_ren_type:
      "\<Delta> \<turnstile> rename r G : arrow_type \<sigma>s Prop"
    using VectorEquivalence.hyps(2) VectorEquivalence.prems
    by (rule renaming_preserves_typing)
  have d_zeta_raw:
      "\<sigma>s @ \<Delta> \<turnstile>\<^sub>CEV rename ?r' (zeta_body \<sigma>s F G)"
    using prefix_mapping by (rule VectorEquivalence.IH)
  have d_zeta:
      "\<sigma>s @ \<Delta> \<turnstile>\<^sub>CEV
        zeta_body \<sigma>s (rename r F) (rename r G)"
    using d_zeta_raw by (simp add: rename_zeta_body_prefix)
  have "\<Delta> \<turnstile>\<^sub>CEV
      Eq (arrow_type \<sigma>s Prop) (rename r F) (rename r G)"
    using F_ren_type G_ren_type d_zeta
    by (rule CEV_proves.VectorEquivalence)
  then show ?case
    by simp
next
  case (ContextVectorEquivalence \<Gamma> A F \<sigma>s G)
  let ?r' = "prefix_ren (length \<sigma>s) r"
  have prefix_mapping:
      "\<And>n \<tau>. lookup (\<sigma>s @ \<Gamma>) n = Some \<tau> \<Longrightarrow>
        lookup (\<sigma>s @ \<Delta>) (?r' n) = Some \<tau>"
    using ContextVectorEquivalence.prems
    by (rule prefix_ren_preserves_lookup)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using ContextVectorEquivalence.hyps(1) ContextVectorEquivalence.prems
    by (rule renaming_preserves_typing)
  have F_ren_type:
      "\<Delta> \<turnstile> rename r F : arrow_type \<sigma>s Prop"
    using ContextVectorEquivalence.hyps(2) ContextVectorEquivalence.prems
    by (rule renaming_preserves_typing)
  have G_ren_type:
      "\<Delta> \<turnstile> rename r G : arrow_type \<sigma>s Prop"
    using ContextVectorEquivalence.hyps(3) ContextVectorEquivalence.prems
    by (rule renaming_preserves_typing)
  have d_context_raw:
      "\<sigma>s @ \<Delta> \<turnstile>\<^sub>CEV
        rename ?r'
          (Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G))"
    using prefix_mapping by (rule ContextVectorEquivalence.IH)
  have d_context:
      "\<sigma>s @ \<Delta> \<turnstile>\<^sub>CEV
        Imp (shift_by (length \<sigma>s) (rename r A))
          (zeta_body \<sigma>s (rename r F) (rename r G))"
    using d_context_raw
    by (simp add: rename_shift_by_prefix rename_zeta_body_prefix)
  have "\<Delta> \<turnstile>\<^sub>CEV
      Imp (rename r A)
        (Eq (arrow_type \<sigma>s Prop) (rename r F) (rename r G))"
    using A_ren_type F_ren_type G_ren_type d_context
    by (rule CEV_proves.ContextVectorEquivalence)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have d_A: "\<Delta> \<turnstile>\<^sub>CEV rename r A"
    using MP.prems by (rule MP.IH(1))
  have d_imp_raw: "\<Delta> \<turnstile>\<^sub>CEV rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have d_imp: "\<Delta> \<turnstile>\<^sub>CEV Imp (rename r A) (rename r B)"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CEV_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have lifted_mapping:
      "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
        lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Gen.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<Delta> \<turnstile> rename r P : Prop"
    using Gen.hyps(1) Gen.prems by (rule renaming_preserves_typing)
  have Q_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) Q : Prop"
    using Gen.hyps(2) lifted_mapping by (rule renaming_preserves_typing)
  have d_ext_raw:
      "\<rho> # \<Delta> \<turnstile>\<^sub>CEV
        rename (lift_ren r) (Imp (shift P) Q)"
    using lifted_mapping by (rule Gen.IH)
  have d_ext:
      "\<rho> # \<Delta> \<turnstile>\<^sub>CEV
        Imp (shift (rename r P)) (rename (lift_ren r) Q)"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>CEV
      Imp (rename r P) (Forall \<rho> (rename (lift_ren r) Q))"
    using P_ren_type Q_ren_type d_ext by (rule CEV_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have lifted_mapping:
      "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
        lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Inst.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) P : Prop"
    using Inst.hyps(1) lifted_mapping by (rule renaming_preserves_typing)
  have Q_ren_type: "\<Delta> \<turnstile> rename r Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule renaming_preserves_typing)
  have d_ext_raw:
      "\<rho> # \<Delta> \<turnstile>\<^sub>CEV
        rename (lift_ren r) (Imp P (shift Q))"
    using lifted_mapping by (rule Inst.IH)
  have d_ext:
      "\<rho> # \<Delta> \<turnstile>\<^sub>CEV
        Imp (rename (lift_ren r) P) (shift (rename r Q))"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>CEV
      Imp (Exists \<rho> (rename (lift_ren r) P)) (rename r Q)"
    using P_ren_type Q_ren_type d_ext by (rule CEV_proves.Inst)
  then show ?case
    by simp
qed

lemma CE_proves_rename:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> \<turnstile>\<^sub>CE rename r A"
  using assms
proof (induction arbitrary: \<Delta> r rule: CE_proves.induct)
  case (C \<Gamma> A)
  have "\<Delta> \<turnstile>\<^sub>C rename r A"
    using C.hyps C.prems by (rule C_proves_rename)
  then show ?case
    by (rule CE_proves.C)
next
  case (PropEquivalence \<Gamma> A B)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using PropEquivalence.hyps(1) PropEquivalence.prems
    by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : Prop"
    using PropEquivalence.hyps(2) PropEquivalence.prems
    by (rule renaming_preserves_typing)
  have d_iff_raw: "\<Delta> \<turnstile>\<^sub>CE rename r (A \<longleftrightarrow>\<^sub>o B)"
    using PropEquivalence.prems by (rule PropEquivalence.IH)
  have d_iff: "\<Delta> \<turnstile>\<^sub>CE (rename r A \<longleftrightarrow>\<^sub>o rename r B)"
    using d_iff_raw by simp
  have "\<Delta> \<turnstile>\<^sub>CE Eq Prop (rename r A) (rename r B)"
    using A_ren_type B_ren_type d_iff by (rule CE_proves.PropEquivalence)
  then show ?case
    by simp
next
  case (MP \<Gamma> A B)
  have dA: "\<Delta> \<turnstile>\<^sub>CE rename r A"
    using MP.prems by (rule MP.IH(1))
  have dImp_raw: "\<Delta> \<turnstile>\<^sub>CE rename r (Imp A B)"
    using MP.prems by (rule MP.IH(2))
  have dImp: "\<Delta> \<turnstile>\<^sub>CE Imp (rename r A) (rename r B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule CE_proves.MP)
next
  case (Gen \<Gamma> P \<rho> Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Gen.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<Delta> \<turnstile> rename r P : Prop"
    using Gen.hyps(1) Gen.prems by (rule renaming_preserves_typing)
  have Q_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) Q : Prop"
    using Gen.hyps(2) lift_rel by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>CE
      rename (lift_ren r) (Imp (shift P) Q)"
    using lift_rel by (rule Gen.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>CE
      Imp (shift (rename r P)) (rename (lift_ren r) Q)"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>CE Imp (rename r P)
      (Forall \<rho> (rename (lift_ren r) Q))"
    using P_ren_type Q_ren_type d_ext by (rule CE_proves.Gen)
  then show ?case
    by simp
next
  case (Inst \<rho> \<Gamma> P Q)
  have lift_rel: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
      lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    using Inst.prems by (rule lookup_lift_ren)
  have P_ren_type: "\<rho> # \<Delta> \<turnstile> rename (lift_ren r) P : Prop"
    using Inst.hyps(1) lift_rel by (rule renaming_preserves_typing)
  have Q_ren_type: "\<Delta> \<turnstile> rename r Q : Prop"
    using Inst.hyps(2) Inst.prems by (rule renaming_preserves_typing)
  have d_ext_raw: "\<rho> # \<Delta> \<turnstile>\<^sub>CE
      rename (lift_ren r) (Imp P (shift Q))"
    using lift_rel by (rule Inst.IH)
  have d_ext: "\<rho> # \<Delta> \<turnstile>\<^sub>CE
      Imp (rename (lift_ren r) P) (shift (rename r Q))"
    using d_ext_raw by (simp add: shift_rename_lift)
  have "\<Delta> \<turnstile>\<^sub>CE Imp (Exists \<rho> (rename (lift_ren r) P)) (rename r Q)"
    using P_ren_type Q_ren_type d_ext by (rule CE_proves.Inst)
  then show ?case
    by simp
qed

lemma CEV_proves_rename:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
      lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> \<turnstile>\<^sub>CEV rename r A"
  using assms CE_proves_rename
  by (rule CEV_proves_rename_if_CE_rename)

lemma C_derivable_subst_const:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule subst_const_preserves_typing)
  have "subst_const c \<sigma> N A \<in> set (map (subst_const c \<sigma> N) \<Delta>)"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_sub_type by (rule C_derivable.Assumption)
next
  case (Theorem \<Gamma> A \<Delta>)
  have "\<Gamma> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule C_proves_subst_const)
  then show ?case
    by (rule C_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have dA: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp_raw: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>C
      subst_const c \<sigma> N (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have dImp: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>C
      Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule C_derivable.Derive_MP)
qed

lemma C_derivable_rename:
  assumes "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>C rename r A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Sigma> \<Gamma>)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule renaming_preserves_typing)
  have "rename r A \<in> set (map (rename r) \<Sigma>)"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_ren_type by (rule C_derivable.Assumption)
next
  case (Theorem \<Gamma> A \<Sigma>)
  have "\<Delta> \<turnstile>\<^sub>C rename r A"
    using Theorem.hyps Theorem.prems by (rule C_proves_rename)
  then show ?case
    by (rule C_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Sigma> A B)
  have dA: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>C rename r A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp_raw: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>C rename r (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have dImp: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>C Imp (rename r A) (rename r B)"
    using dImp_raw by simp
  show ?case
    using dA dImp by (rule C_derivable.Derive_MP)
qed

definition henkin_witness_axiom :: "string \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "henkin_witness_axiom c \<sigma> A =
    Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A)"

lemma abstract_const_henkin_witness_axiom_fresh:
  assumes "c \<notin> consts_of A"
  shows "abstract_const c \<sigma> (henkin_witness_axiom c \<sigma> A) =
    Imp (shift (Exists \<sigma> A)) A"
proof -
  have exists_fresh: "c \<notin> consts_of (Exists \<sigma> A)"
    using assms by simp
  have "abstract_const c \<sigma> (Exists \<sigma> A) = shift (Exists \<sigma> A)"
    using exists_fresh by (rule abstract_const_fresh)
  then have abs_exists: "abstract_const c \<sigma> (Exists \<sigma> A) = shift (Exists \<sigma> A)" .
  have abs_subst: "abstract_const c \<sigma> (subst0 (Const c \<sigma>) A) = A"
    using assms by (rule abstract_const_subst0_const_fresh)
  have "abstract_const c \<sigma>
      (Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A)) =
      Imp (abstract_const c \<sigma> (Exists \<sigma> A))
        (abstract_const c \<sigma> (subst0 (Const c \<sigma>) A))"
    unfolding abstract_const_def shift_def by simp
  then show ?thesis
    using abs_exists abs_subst unfolding henkin_witness_axiom_def by simp
qed

definition Henkin_axioms :: "ctx \<Rightarrow> (otype \<Rightarrow> oterm \<Rightarrow> string) \<Rightarrow> oterm set" where
  "Henkin_axioms \<Gamma> h =
    {henkin_witness_axiom (h \<sigma> A) \<sigma> A | \<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop}"

definition Henkin_witness_axioms_available :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "Henkin_witness_axioms_available \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      (\<exists>c. henkin_witness_axiom c \<sigma> A \<in> T))"

primrec add_witness_axioms ::
    "(string \<times> otype \<times> oterm) list \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "add_witness_axioms [] T = T"
| "add_witness_axioms (x # xs) T =
    (case x of (c, \<sigma>, A) =>
      add_witness_axioms xs (insert (henkin_witness_axiom c \<sigma> A) T))"

primrec witness_bodies ::
    "(string \<times> otype \<times> oterm) list \<Rightarrow> (otype \<times> oterm) list" where
  "witness_bodies [] = []"
| "witness_bodies (x # xs) =
    (case x of (c, \<sigma>, A) => (\<sigma>, A) # witness_bodies xs)"

primrec fresh_witness_axiom_sequence ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (string \<times> otype \<times> oterm) list \<Rightarrow> bool" where
  "fresh_witness_axiom_sequence \<Gamma> T [] = True"
| "fresh_witness_axiom_sequence \<Gamma> T (x # xs) =
    (case x of (c, \<sigma>, A) =>
      \<sigma> # \<Gamma> \<turnstile> A : Prop \<and>
      c \<notin> consts_of_set T \<and>
      c \<notin> consts_of A \<and>
      fresh_witness_axiom_sequence \<Gamma>
        (insert (henkin_witness_axiom c \<sigma> A) T) xs)"

lemma henkin_witness_axiom_typed:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> henkin_witness_axiom c \<sigma> A : Prop"
proof -
  have "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms by auto
  moreover have "\<Gamma> \<turnstile> subst0 (Const c \<sigma>) A : Prop"
    using assms has_type.Const by (rule subst0_preserves_typing)
  ultimately show ?thesis
    unfolding henkin_witness_axiom_def by auto
qed

lemma typed_theory_Henkin_axioms:
  "typed_theory \<Gamma> (Henkin_axioms \<Gamma> h)"
proof (unfold typed_theory_def Henkin_axioms_def, intro ballI)
  fix B
  assume "B \<in> {henkin_witness_axiom (h \<sigma> A) \<sigma> A |\<sigma> A.
      \<sigma> # \<Gamma> \<turnstile> A : Prop}"
  then obtain \<sigma> A where B_def: "B = henkin_witness_axiom (h \<sigma> A) \<sigma> A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    by blast
  show "\<Gamma> \<turnstile> B : Prop"
    using henkin_witness_axiom_typed[OF A_type, of "h \<sigma> A"] B_def by simp
qed

lemma typed_theory_insert_henkin_witness_axiom:
  assumes "typed_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "typed_theory \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
  using assms henkin_witness_axiom_typed
  unfolding typed_theory_def by blast

lemma typed_theory_add_fresh_witness_axioms:
  assumes "typed_theory \<Gamma> T"
    and "fresh_witness_axiom_sequence \<Gamma> T xs"
  shows "typed_theory \<Gamma> (add_witness_axioms xs T)"
  using assms
proof (induction xs arbitrary: T)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain c \<sigma> A where x_def: "x = (c, \<sigma>, A)"
    by (cases x) auto
  have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Cons.prems(2) unfolding x_def by simp
  have tail_fresh: "fresh_witness_axiom_sequence \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) xs"
    using Cons.prems(2) unfolding x_def by simp
  have typed_insert: "typed_theory \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) A_type by (rule typed_theory_insert_henkin_witness_axiom)
  show ?case
    using Cons.IH[OF typed_insert tail_fresh] unfolding x_def by simp
qed

lemma fresh_witness_axiom_sequence_exists:
  assumes finite_T: "finite T"
    and typed_specs: "\<And>\<sigma> A. (\<sigma>, A) \<in> set specs \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<exists>xs. fresh_witness_axiom_sequence \<Gamma> T xs \<and>
    witness_bodies xs = specs"
  using assms
proof (induction specs arbitrary: T)
  case Nil
  then show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Cons spec specs)
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Cons.prems(2) unfolding spec_def by simp
  obtain c where fresh: "fresh_const_for c T A"
    using Cons.prems(1) by (rule fresh_const_for_finite)
  have fresh_T: "c \<notin> consts_of_set T"
    using fresh unfolding fresh_const_for_def by blast
  have fresh_A: "c \<notin> consts_of A"
    using fresh unfolding fresh_const_for_def by blast
  have finite_insert: "finite (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) by simp
  have tail_typed: "\<And>\<tau> B. (\<tau>, B) \<in> set specs \<Longrightarrow> \<tau> # \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(2) unfolding spec_def by simp
  obtain xs where tail_fresh: "fresh_witness_axiom_sequence \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) xs"
    and bodies: "witness_bodies xs = specs"
    using Cons.IH[OF finite_insert tail_typed] by blast
  have "fresh_witness_axiom_sequence \<Gamma> T ((c, \<sigma>, A) # xs)"
    using A_type fresh_T fresh_A tail_fresh by simp
  moreover have "witness_bodies ((c, \<sigma>, A) # xs) = spec # specs"
    using bodies unfolding spec_def by simp
  ultimately show ?case
    by blast
qed

definition enumerates_witness_bodies ::
    "ctx \<Rightarrow> (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> bool" where
  "enumerates_witness_bodies \<Gamma> enum \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow> (\<exists>n. enum n = (\<sigma>, A)))"

definition fresh_const_for_stage :: "oterm set \<Rightarrow> oterm \<Rightarrow> string" where
  "fresh_const_for_stage T A = (SOME c. fresh_const_for c T A)"

definition staged_henkin_step ::
    "ctx \<Rightarrow> otype \<times> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "staged_henkin_step \<Gamma> spec T =
    (case spec of (\<sigma>, A) =>
      if \<sigma> # \<Gamma> \<turnstile> A : Prop
      then insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T
      else T)"

primrec staged_henkin_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "staged_henkin_chain \<Gamma> T enum 0 = T"
| "staged_henkin_chain \<Gamma> T enum (Suc n) =
    staged_henkin_step \<Gamma> (enum n) (staged_henkin_chain \<Gamma> T enum n)"

definition staged_henkin_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> oterm set" where
  "staged_henkin_extension \<Gamma> T enum =
    (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"

lemma fresh_const_for_stage_fresh:
  assumes "finite T"
  shows "fresh_const_for (fresh_const_for_stage T A) T A"
  unfolding fresh_const_for_stage_def
  using fresh_const_for_finite[OF assms, of A]
  by (metis someI_ex)

lemma staged_henkin_step_extends:
  "T \<subseteq> staged_henkin_step \<Gamma> spec T"
  unfolding staged_henkin_step_def
  by (cases spec) auto

lemma staged_henkin_step_finite:
  assumes "finite T"
  shows "finite (staged_henkin_step \<Gamma> spec T)"
  using assms unfolding staged_henkin_step_def
  by (cases spec) auto

lemma staged_henkin_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (staged_henkin_step \<Gamma> spec T)"
  using assms unfolding staged_henkin_step_def
  by (cases spec) (auto intro: typed_theory_insert_henkin_witness_axiom)

lemma staged_henkin_step_adds:
  assumes "spec = (\<sigma>, A)"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A \<in>
    staged_henkin_step \<Gamma> spec T"
  using assms unfolding staged_henkin_step_def by simp

lemma staged_henkin_chain_step:
  "staged_henkin_chain \<Gamma> T enum n \<subseteq>
    staged_henkin_chain \<Gamma> T enum (Suc n)"
  using staged_henkin_step_extends[of
      "staged_henkin_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma staged_henkin_chain_finite:
  assumes "finite T"
  shows "finite (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: staged_henkin_step_finite)
qed

lemma staged_henkin_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: staged_henkin_step_typed)
qed

lemma staged_henkin_extension_extends:
  "T \<subseteq> staged_henkin_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> staged_henkin_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> staged_henkin_extension \<Gamma> T enum"
    unfolding staged_henkin_extension_def by blast
qed

lemma staged_henkin_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule staged_henkin_chain_typed)
  then show ?thesis
    unfolding typed_theory_def staged_henkin_extension_def by blast
qed

lemma Henkin_witness_axioms_available_mono:
  assumes "Henkin_witness_axioms_available \<Gamma> T"
    and "T \<subseteq> U"
  shows "Henkin_witness_axioms_available \<Gamma> U"
  using assms unfolding Henkin_witness_axioms_available_def by blast

lemma staged_henkin_extension_witness_axioms_available:
  assumes "enumerates_witness_bodies \<Gamma> enum"
  shows "Henkin_witness_axioms_available \<Gamma>
    (staged_henkin_extension \<Gamma> T enum)"
proof (unfold Henkin_witness_axioms_available_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = (\<sigma>, A)"
    using assms A_type unfolding enumerates_witness_bodies_def by blast
  let ?Tn = "staged_henkin_chain \<Gamma> T enum n"
  let ?c = "fresh_const_for_stage ?Tn A"
  have ax_in_next: "henkin_witness_axiom ?c \<sigma> A \<in>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    using staged_henkin_step_adds[OF enum_n A_type, of ?Tn]
    by simp
  have "staged_henkin_chain \<Gamma> T enum (Suc n) \<in>
      range (staged_henkin_chain \<Gamma> T enum)"
    by blast
  then have "henkin_witness_axiom ?c \<sigma> A \<in>
      staged_henkin_extension \<Gamma> T enum"
    unfolding staged_henkin_extension_def
    using ax_in_next by (rule UnionI)
  then show "\<exists>c. henkin_witness_axiom c \<sigma> A \<in>
      staged_henkin_extension \<Gamma> T enum"
    by blast
qed

lemma henkin_scheme_in_of_witness_axioms:
  assumes "\<And>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      henkin_witness_axiom (h \<sigma> A) \<sigma> A \<in> T"
  shows "Henkin_scheme_in \<Gamma> T (\<lambda>\<sigma> A. Const (h \<sigma> A) \<sigma>)"
proof (unfold Henkin_scheme_in_def, intro allI impI conjI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  show "\<Gamma> \<turnstile> Const (h \<sigma> A) \<sigma> : \<sigma>"
    by auto
  show "Imp (Exists \<sigma> A) (subst0 (Const (h \<sigma> A) \<sigma>) A) \<in> T"
    using assms[OF A_type] unfolding henkin_witness_axiom_def .
qed

lemma henkin_scheme_in_if_Henkin_axioms_subset:
  assumes "Henkin_axioms \<Gamma> h \<subseteq> T"
  shows "Henkin_scheme_in \<Gamma> T (\<lambda>\<sigma> A. Const (h \<sigma> A) \<sigma>)"
proof (rule henkin_scheme_in_of_witness_axioms)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  have "henkin_witness_axiom (h \<sigma> A) \<sigma> A \<in> Henkin_axioms \<Gamma> h"
    unfolding Henkin_axioms_def using A_type by blast
  then show "henkin_witness_axiom (h \<sigma> A) \<sigma> A \<in> T"
    using assms by blast
qed

definition enumerates_formulas :: "ctx \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> bool" where
  "enumerates_formulas \<Gamma> enum \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> (\<exists>n. enum n = A))"

lemma enumerates_witness_bodies_from_nat:
  "enumerates_witness_bodies \<Gamma> (from_nat :: nat \<Rightarrow> otype \<times> oterm)"
  unfolding enumerates_witness_bodies_def
proof (intro allI impI)
  fix \<sigma> A
  assume "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  have "\<exists>n. (from_nat n :: otype \<times> oterm) = (\<sigma>, A)"
    using surj_from_nat[where ?'a = "otype \<times> oterm"]
    unfolding surj_def by metis
  then show "\<exists>n. (from_nat :: nat \<Rightarrow> otype \<times> oterm) n = (\<sigma>, A)"
    by blast
qed

lemma enumerates_witness_bodies_exists:
  "\<exists>enum. enumerates_witness_bodies \<Gamma> enum"
  using enumerates_witness_bodies_from_nat by blast

lemma enumerates_formulas_from_nat:
  "enumerates_formulas \<Gamma> (from_nat :: nat \<Rightarrow> oterm)"
  unfolding enumerates_formulas_def
proof (intro allI impI)
  fix A
  assume "\<Gamma> \<turnstile> A : Prop"
  have "\<exists>n. (from_nat n :: oterm) = A"
    using surj_from_nat[where ?'a = oterm]
    unfolding surj_def by metis
  then show "\<exists>n. (from_nat :: nat \<Rightarrow> oterm) n = A"
    by blast
qed

lemma enumerates_formulas_exists:
  "\<exists>enum. enumerates_formulas \<Gamma> enum"
  using enumerates_formulas_from_nat by blast

lemma typed_theory_nat_union:
  assumes "\<And>n. typed_theory \<Gamma> (S n)"
  shows "typed_theory \<Gamma> (\<Union>n. S n)"
  using assms unfolding typed_theory_def by blast

lemma nat_chain_mono:
  fixes S :: "nat \<Rightarrow> 'a set"
  assumes step: "\<And>n. S n \<subseteq> S (Suc n)"
    and le: "i \<le> j"
  shows "S i \<subseteq> S j"
  using le
proof (induction j arbitrary: i)
  case 0
  then show ?case
    by auto
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True
    then show ?thesis
      by auto
  next
    case False
    then have "i \<le> j"
      using Suc.prems by auto
    then have "S i \<subseteq> S j"
      by (rule Suc.IH)
    also have "... \<subseteq> S (Suc j)"
      by (rule step)
    finally show ?thesis .
  qed
qed

lemma finite_subset_nat_chain:
  fixes S :: "nat \<Rightarrow> 'a set"
  assumes finite_F: "finite F"
    and sub_union: "F \<subseteq> (\<Union>n. S n)"
    and step: "\<And>n. S n \<subseteq> S (Suc n)"
  shows "\<exists>n. F \<subseteq> S n"
  using finite_F sub_union
proof (induction F rule: finite_induct)
  case empty
  then show ?case
    by blast
next
  case (insert x F)
  obtain nx where x_in: "x \<in> S nx"
    using insert.prems by blast
  have F_sub_union: "F \<subseteq> (\<Union>n. S n)"
    using insert.prems by blast
  obtain nF where F_sub: "F \<subseteq> S nF"
    using insert.IH[OF F_sub_union] by blast
  let ?n = "max nx nF"
  have nx_le: "nx \<le> ?n"
    by simp
  have nF_le: "nF \<le> ?n"
    by simp
  have S_nx_sub: "S nx \<subseteq> S ?n"
  proof (rule nat_chain_mono)
    show "\<And>n. S n \<subseteq> S (Suc n)"
      by (rule step)
    show "nx \<le> ?n"
      by (rule nx_le)
  qed
  have S_nF_sub: "S nF \<subseteq> S ?n"
  proof (rule nat_chain_mono)
    show "\<And>n. S n \<subseteq> S (Suc n)"
      by (rule step)
    show "nF \<le> ?n"
      by (rule nF_le)
  qed
  have x_in_n: "x \<in> S ?n"
    using x_in S_nx_sub by auto
  have F_sub_n: "F \<subseteq> S ?n"
    using F_sub S_nF_sub by auto
  show ?case
    using x_in_n F_sub_n by blast
qed

lemma prop_tautology_contradiction:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma> (Imp A (Imp (Neg A) ObjFalse))"
proof -
  have "\<Gamma> \<turnstile> Imp A (Imp (Neg A) ObjFalse) : Prop"
    using assms typed_ObjFalse by auto
  moreover have "\<forall>v. prop_eval v (Imp A (Imp (Neg A) ObjFalse))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp B (Imp A B))"
proof -
  have "\<Gamma> \<turnstile> Imp B (Imp A B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp B (Imp A B))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_imp_of_neg_left:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (Neg A) (Imp A B))"
proof -
  have "\<Gamma> \<turnstile> Imp (Neg A) (Imp A B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp (Neg A) (Imp A B))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_deduction_mp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
proof -
  have "\<Gamma> \<turnstile>
      Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v
      (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_imp_trans:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
proof -
  have "\<Gamma> \<turnstile> Imp (Imp A B) (Imp (Imp B C) (Imp A C)) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v
      (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_swap_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp A (Imp B C)) (Imp B (Imp A C)))"
proof -
  have "\<Gamma> \<turnstile> Imp (Imp A (Imp B C)) (Imp B (Imp A C)) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v
      (Imp (Imp A (Imp B C)) (Imp B (Imp A C)))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_cases:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp A B) (Imp (Imp (Neg A) B) B))"
proof -
  have "\<Gamma> \<turnstile> Imp (Imp A B) (Imp (Imp (Neg A) B) B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v
      (Imp (Imp A B) (Imp (Imp (Neg A) B) B))"
    by auto
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_imp_false_to_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma> (Imp ObjTrue (Imp (Imp A ObjFalse) (Neg A)))"
proof -
  have "\<Gamma> \<turnstile> Imp ObjTrue (Imp (Imp A ObjFalse) (Neg A)) : Prop"
    using assms typed_ObjTrue typed_ObjFalse
    by (intro has_type.Imp has_type.Neg)
  moreover have "\<forall>v. prop_eval v
      (Imp ObjTrue (Imp (Imp A ObjFalse) (Neg A)))"
    by (simp add: ObjFalse_def)
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_imp_neg_false_to_formula:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma> (Imp ObjTrue (Imp (Imp (Neg A) ObjFalse) A))"
proof -
  have "\<Gamma> \<turnstile> Imp ObjTrue (Imp (Imp (Neg A) ObjFalse) A) : Prop"
    using assms typed_ObjTrue typed_ObjFalse
    by (intro has_type.Imp has_type.Neg)
  moreover have "\<forall>v. prop_eval v
      (Imp ObjTrue (Imp (Imp (Neg A) ObjFalse) A))"
    by (simp add: ObjFalse_def)
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_classical_contrapositive:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (Imp (Neg A) B) (Imp (Neg B) A))"
proof -
  have "\<Gamma> \<turnstile> Imp (Imp (Neg A) B) (Imp (Neg B) A) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp (Imp (Neg A) B) (Imp (Neg B) A))"
    apply (simp only: prop_eval.simps)
    by blast
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_conj_left:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (Conj A B) A)"
proof -
  have "\<Gamma> \<turnstile> Imp (Conj A B) A : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp (Conj A B) A)"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_conj_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (Conj A B) B)"
proof -
  have "\<Gamma> \<turnstile> Imp (Conj A B) B : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp (Conj A B) B)"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_disj_left_intro:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp A (Disj A B))"
proof -
  have "\<Gamma> \<turnstile> Imp A (Disj A B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp A (Disj A B))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_disj_right_intro:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp B (Disj A B))"
proof -
  have "\<Gamma> \<turnstile> Imp B (Disj A B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp B (Disj A B))"
    by simp
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed

lemma prop_tautology_disj_elim_neg_left:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (Disj A B) (Imp (Neg A) B))"
proof -
  have "\<Gamma> \<turnstile> Imp (Disj A B) (Imp (Neg A) B) : Prop"
    using assms by auto
  moreover have "\<forall>v. prop_eval v (Imp (Disj A B) (Imp (Neg A) B))"
    by auto
  ultimately show ?thesis
    unfolding prop_tautology_def by blast
qed


subsection \<open>Set derivability and canonical theories for H\<close>

definition H_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>H\<^sub>s _" [50, 50, 50] 50) where
  "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A \<longleftrightarrow> (\<exists>\<Delta>. set \<Delta> \<subseteq> T \<and> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A)"

lemma H_derivable_mono:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    and "set \<Delta> \<subseteq> set \<Delta>'"
  shows "\<Gamma> ; \<Delta>' \<turnstile>\<^sub>H A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by (intro H_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by (intro H_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  from Derive_MP.IH(1)[OF Derive_MP.prems]
    Derive_MP.IH(2)[OF Derive_MP.prems]
  show ?case
    by (rule H_derivable.Derive_MP)
qed

lemma H_set_derivable_of_list:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
  using assms unfolding H_set_derivable_def by blast

lemma H_derivable_of_set_derivable:
  assumes "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof -
  obtain \<Sigma> where "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H A"
    and "set \<Sigma> \<subseteq> set \<Delta>"
    using assms unfolding H_set_derivable_def by blast
  then show ?thesis
    by (rule H_derivable_mono)
qed

lemma H_set_derivable_rename:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> ; rename r ` T \<turnstile>\<^sub>H\<^sub>s rename r A"
proof -
  obtain \<Sigma> where \<Sigma>_sub: "set \<Sigma> \<subseteq> T"
    and d: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H A"
    using assms(1) unfolding H_set_derivable_def by blast
  have d_ren: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>H rename r A"
    using d assms(2) by (rule H_derivable_rename)
  have "set (map (rename r) \<Sigma>) \<subseteq> rename r ` T"
    using \<Sigma>_sub by auto
  then show ?thesis
    using d_ren unfolding H_set_derivable_def by blast
qed

lemma H_set_derivable_shift:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s shift A"
  unfolding shift_def
  using assms by (rule H_set_derivable_rename) auto

lemma H_set_derivable_subst_const:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>H\<^sub>s subst_const c \<sigma> N A"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> T"
    and d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    using assms(1) unfolding H_set_derivable_def by blast
  have d_sub: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>H subst_const c \<sigma> N A"
    using d assms(2) by (rule H_derivable_subst_const)
  have "set (map (subst_const c \<sigma> N) \<Delta>) \<subseteq> subst_const c \<sigma> N ` T"
    using \<Delta>_sub by auto
  then show ?thesis
    using d_sub unfolding H_set_derivable_def by blast
qed

lemma H_set_derivable_subst_const_fresh_set:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "c \<notin> consts_of_set T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s subst_const c \<sigma> N A"
proof -
  have "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>H\<^sub>s subst_const c \<sigma> N A"
    using assms(1,2) by (rule H_set_derivable_subst_const)
  then show ?thesis
    using subst_const_image_fresh_set[OF assms(3), of \<sigma> N] by simp
qed

lemma H_set_derivable_abstract_const:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>H\<^sub>s abstract_const c \<sigma> A"
proof -
  have shifted: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s shift A"
    using assms by (rule H_set_derivable_shift)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have "\<sigma> # \<Gamma> ; subst_const c \<sigma> (Var 0) ` (shift ` T) \<turnstile>\<^sub>H\<^sub>s
      subst_const c \<sigma> (Var 0) (shift A)"
    using shifted var_type by (rule H_set_derivable_subst_const)
  moreover have "subst_const c \<sigma> (Var 0) ` (shift ` T) = abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  ultimately show ?thesis
    unfolding abstract_const_def by simp
qed

lemma H_set_derivable_abstract_const_fresh_set:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "c \<notin> consts_of_set T"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s abstract_const c \<sigma> A"
proof -
  have "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>H\<^sub>s abstract_const c \<sigma> A"
    using assms(1) by (rule H_set_derivable_abstract_const)
  then show ?thesis
    using abstract_const_image_fresh_set[OF assms(2), of \<sigma>] by simp
qed

lemma H_set_derivable_abstract_fresh_witness_false:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "\<sigma> # \<Gamma> ; insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)
    \<turnstile>\<^sub>H\<^sub>s ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d: "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` insert ?W T
      \<turnstile>\<^sub>H\<^sub>s abstract_const c \<sigma> ObjFalse"
    using assms(1) by (rule H_set_derivable_abstract_const)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  have image_eq: "abstract_const c \<sigma> ` insert ?W T =
      insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)"
    using abs_T abs_W by simp
  show ?thesis
    using abs_d image_eq by simp
qed

lemma H_set_Assumption:
  assumes "A \<in> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  unfolding H_set_derivable_def
  using assms by (intro exI[of _ "[A]"]) auto

lemma H_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  unfolding H_set_derivable_def
  using assms by (intro exI[of _ "[]"] H_derivable.Theorem) auto

lemma H_set_MP:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s B"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> T" and dA: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    using assms(1) unfolding H_set_derivable_def by blast
  obtain \<Sigma> where \<Sigma>_sub: "set \<Sigma> \<subseteq> T" and dImp: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H Imp A B"
    using assms(2) unfolding H_set_derivable_def by blast
  have dA': "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>H A"
    using dA by (rule H_derivable_mono) auto
  have dImp': "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>H Imp A B"
    using dImp by (rule H_derivable_mono) auto
  have "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>H B"
    using dA' dImp' by (rule H_derivable.Derive_MP)
  moreover have "set (\<Delta> @ \<Sigma>) \<subseteq> T"
    using \<Delta>_sub \<Sigma>_sub by auto
  ultimately show ?thesis
    unfolding H_set_derivable_def by blast
qed

lemma H_set_ex_falso:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
proof -
  have taut_raw: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ObjTrue) (Imp ObjTrue A)"
    using typed_ObjTrue assms(2)
    by (intro H_proves.PC prop_tautology_imp_of_neg_left)
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp ObjFalse (Imp ObjTrue A)"
    using taut_raw by (simp add: ObjFalse_def)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp ObjFalse (Imp ObjTrue A)"
    using taut by (rule H_set_Theorem)
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp ObjTrue A"
    using assms(1) d_taut by (rule H_set_MP)
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjTrue"
    using H_proves_ObjTrue by (rule H_set_Theorem)
  show ?thesis
    using d_true d_imp by (rule H_set_MP)
qed

lemma H_set_derivable_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>H\<^sub>s A"
  using assms unfolding H_set_derivable_def by blast

lemma H_set_derivable_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms H_derivable_formula unfolding H_set_derivable_def by blast

lemma H_set_derivable_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  obtains U where "finite U" and "U \<subseteq> T" and "\<Gamma> ; U \<turnstile>\<^sub>H\<^sub>s A"
proof -
  obtain \<Delta> where "set \<Delta> \<subseteq> T" and "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    using assms unfolding H_set_derivable_def by blast
  then have "finite (set \<Delta>)" "set \<Delta> \<subseteq> T" "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
    using H_set_derivable_of_list by auto
  then show ?thesis
    using that by blast
qed

lemma H_derivable_empty_imp_proves:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    and "\<Delta> = []"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by simp
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>H A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp: "\<Gamma> \<turnstile>\<^sub>H Imp A B"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  show ?case
    using dA dImp
    by (rule H_proves.MP)
qed

lemma H_set_derivable_empty_imp_proves:
  assumes "\<Gamma> ; {} \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof -
  obtain \<Delta> where \<Delta>_empty: "set \<Delta> \<subseteq> {}" and d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    using assms unfolding H_set_derivable_def by blast
  have \<Delta>_nil: "\<Delta> = []"
    using \<Delta>_empty by (cases \<Delta>) auto
  show ?thesis
    using d \<Delta>_nil by (rule H_derivable_empty_imp_proves)
qed

lemma H_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>H B"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule H_proves_formula)
  have prop_taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
    using assms(1) B_type by (rule prop_tautology_imp_of_right)
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp B (Imp A B)"
    using prop_taut by (rule H_proves.PC)
  show ?thesis
    using assms(2) taut by (rule H_proves.MP)
qed

lemma H_proves_imp_trans:
  assumes "\<Gamma> \<turnstile>\<^sub>H Imp A B"
    and "\<Gamma> \<turnstile>\<^sub>H Imp B C"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp A C"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>H
      Imp (Imp A B) (Imp (Imp B C) (Imp A C))"
    using assms(3,4,5)
    by (intro H_proves.PC prop_tautology_imp_trans)
  have step: "\<Gamma> \<turnstile>\<^sub>H Imp (Imp B C) (Imp A C)"
    using assms(1) taut by (rule H_proves.MP)
  show ?thesis
    using assms(2) step by (rule H_proves.MP)
qed

lemma H_proves_cases:
  assumes "\<Gamma> \<turnstile>\<^sub>H Imp A B"
    and "\<Gamma> \<turnstile>\<^sub>H Imp (Neg A) B"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H B"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>H
      Imp (Imp A B) (Imp (Imp (Neg A) B) B)"
    using assms(3,4)
    by (intro H_proves.PC prop_tautology_cases)
  have step: "\<Gamma> \<turnstile>\<^sub>H Imp (Imp (Neg A) B) B"
    using assms(1) taut by (rule H_proves.MP)
  show ?thesis
    using assms(2) step by (rule H_proves.MP)
qed

lemma H_proves_exists_imp_shift_exists:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Exists \<sigma> (Imp (shift (Exists \<sigma> A)) A)"
proof -
  let ?E = "Exists \<sigma> A"
  let ?B = "Imp (shift ?E) A"
  let ?Q = "Exists \<sigma> ?B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using assms by auto
  have shift_E_type: "\<sigma> # \<Gamma> \<turnstile> shift ?E : Prop"
    using E_type by (rule weakening_front)
  have B_type: "\<sigma> # \<Gamma> \<turnstile> ?B : Prop"
    using shift_E_type assms by auto
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using B_type by auto

  have A_imp_B: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp A ?B"
    using shift_E_type assms
    by (intro H_proves.PC prop_tautology_imp_of_right)

  have lift_B_type: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) ?B : Prop"
    using B_type
    by (rule renaming_preserves_typing) (case_tac n; simp)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by auto
  have B_imp_shift_Q: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp ?B (shift ?Q)"
  proof -
    have subst_lift: "subst0 (Var 0) (rename (lift_ren Suc) ?B) = ?B"
      by (rule subst0_rename_lift_Suc_var0)
    have shift_Q: "shift ?Q = Exists \<sigma> (rename (lift_ren Suc) ?B)"
      by (simp add: shift_def)
    have d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H
        Imp (subst0 (Var 0) (rename (lift_ren Suc) ?B))
          (Exists \<sigma> (rename (lift_ren Suc) ?B))"
      using lift_B_type var0_type by (rule H_proves.EG)
    show ?thesis
      using d by (simp only: subst_lift shift_Q)
  qed

  have A_imp_shift_Q: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp A (shift ?Q)"
  proof -
    have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift ?Q : Prop"
      using Q_type by (rule weakening_front)
    show ?thesis
      using A_imp_B B_imp_shift_Q assms B_type shift_Q_type
      by (rule H_proves_imp_trans)
  qed
  have E_imp_Q: "\<Gamma> \<turnstile>\<^sub>H Imp ?E ?Q"
    using assms Q_type A_imp_shift_Q by (rule H_proves.Inst)

  let ?K = "Const ''henkin_default'' \<sigma>"
  have K_type: "\<Gamma> \<turnstile> ?K : \<sigma>"
    by auto
  have subst_A_type: "\<Gamma> \<turnstile> subst0 ?K A : Prop"
    using assms K_type by (rule subst0_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst0 ?K ?B : Prop"
    using B_type K_type by (rule subst0_preserves_typing)
  have subst_B_eq: "subst0 ?K ?B = Imp ?E (subst0 ?K A)"
    by (simp add: subst0_def)
  have neg_E_imp_subst_B: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ?E) (subst0 ?K ?B)"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ?E) (Imp ?E (subst0 ?K A))"
      using E_type subst_A_type
      by (intro H_proves.PC prop_tautology_imp_of_neg_left)
    then show ?thesis
      using subst_B_eq by simp
  qed
  have subst_B_imp_Q: "\<Gamma> \<turnstile>\<^sub>H Imp (subst0 ?K ?B) ?Q"
    using B_type K_type by (rule H_proves.EG)
  have neg_E_imp_Q: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ?E) ?Q"
  proof -
    have neg_E_type: "\<Gamma> \<turnstile> Neg ?E : Prop"
      using E_type by (rule has_type.Neg)
    show ?thesis
      using neg_E_imp_subst_B subst_B_imp_Q neg_E_type subst_B_type Q_type
      by (rule H_proves_imp_trans)
  qed
  show ?thesis
    using E_imp_Q neg_E_imp_Q E_type Q_type
    by (rule H_proves_cases)
qed

lemma H_proves_imp_false_to_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Imp A ObjFalse) (Neg A)"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp ObjTrue (Imp (Imp A ObjFalse) (Neg A))"
    using assms by (intro H_proves.PC prop_tautology_imp_false_to_neg)
  show ?thesis
    using H_proves_ObjTrue taut by (rule H_proves.MP)
qed

lemma H_proves_imp_neg_false_to_formula:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Imp (Neg A) ObjFalse) A"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp ObjTrue (Imp (Imp (Neg A) ObjFalse) A)"
    using assms by (intro H_proves.PC prop_tautology_imp_neg_false_to_formula)
  show ?thesis
    using H_proves_ObjTrue taut by (rule H_proves.MP)
qed

lemma H_proves_not_exists_neg_imp_forall:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Neg (Exists \<sigma> (Neg A))) (Forall \<sigma> A)"
proof -
  let ?E = "Exists \<sigma> (Neg A)"
  let ?P = "Neg ?E"
  have neg_A_type: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using neg_A_type by auto
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using E_type by auto
  have shift_E_type: "\<sigma> # \<Gamma> \<turnstile> shift ?E : Prop"
    using E_type by (rule weakening_front)
  have shift_P: "shift ?P = Neg (shift ?E)"
    by (simp add: shift_def)

  have lift_neg_A_type: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) (Neg A) : Prop"
    using neg_A_type
    by (rule renaming_preserves_typing) (case_tac n; simp)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by auto
  have neg_A_imp_shift_E: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (Neg A) (shift ?E)"
  proof -
    have subst_lift: "subst0 (Var 0) (rename (lift_ren Suc) (Neg A)) = Neg A"
      by (rule subst0_rename_lift_Suc_var0)
    have shift_E: "shift ?E = Exists \<sigma> (rename (lift_ren Suc) (Neg A))"
      by (simp add: shift_def)
    have eg: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H
        Imp (subst0 (Var 0) (rename (lift_ren Suc) (Neg A)))
          (Exists \<sigma> (rename (lift_ren Suc) (Neg A)))"
      using lift_neg_A_type var0_type by (rule H_proves.EG)
    show ?thesis
      using eg by (simp only: subst_lift shift_E)
  qed

  have contra: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H
      Imp (Imp (Neg A) (shift ?E)) (Imp (Neg (shift ?E)) A)"
    using A_type shift_E_type
    by (intro H_proves.PC prop_tautology_classical_contrapositive)
  have neg_shift_E_imp_A: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (Neg (shift ?E)) A"
    using neg_A_imp_shift_E contra by (rule H_proves.MP)
  have shift_P_imp_A: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift ?P) A"
    using neg_shift_E_imp_A by (simp only: shift_P)
  show ?thesis
    using P_type A_type shift_P_imp_A by (rule H_proves.Gen)
qed

lemma H_proves_not_forall_imp_exists_neg:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Neg (Forall \<sigma> A)) (Exists \<sigma> (Neg A))"
proof -
  let ?E = "Exists \<sigma> (Neg A)"
  let ?F = "Forall \<sigma> A"
  have neg_A_type: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using neg_A_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using A_type by auto
  have not_E_imp_F: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ?E) ?F"
    using A_type by (rule H_proves_not_exists_neg_imp_forall)
  have contra: "\<Gamma> \<turnstile>\<^sub>H Imp (Imp (Neg ?E) ?F) (Imp (Neg ?F) ?E)"
    using E_type F_type
    by (intro H_proves.PC prop_tautology_classical_contrapositive)
  show ?thesis
    using not_E_imp_F contra by (rule H_proves.MP)
qed

lemma H_derivable_deduction_subset:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H B"
    and "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A B"
proof -
  have aux: "\<And>A \<Delta>. \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      set \<Sigma> \<subseteq> insert A (set \<Delta>) \<Longrightarrow>
      \<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A B"
    using assms(2)
  proof (induction rule: H_derivable.induct)
    case (Assumption B \<Sigma> \<Gamma>)
    then have A_type: "\<Gamma> \<turnstile> A : Prop"
      and \<Sigma>_sub: "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
      by auto
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps by simp
    show ?case
    proof (cases "B = A")
      case True
      have "\<Gamma> \<turnstile>\<^sub>H Imp A A"
        using A_type by (rule H_imp_self)
      then have "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A A"
        by (rule H_derivable.Theorem)
      then show ?thesis
        using True by simp
    next
      case False
      then have B_in: "B \<in> set \<Delta>"
        using Assumption.hyps \<Sigma>_sub by blast
      have dB: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H B"
        using B_in B_type by (rule H_derivable.Assumption)
      have prop_taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
        using A_type B_type by (rule prop_tautology_imp_of_right)
      have taut: "\<Gamma> \<turnstile>\<^sub>H Imp B (Imp A B)"
        using prop_taut by (rule H_proves.PC)
      have d_taut: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp B (Imp A B)"
        using taut by (rule H_derivable.Theorem)
      show ?thesis
        using dB d_taut by (rule H_derivable.Derive_MP)
    qed
  next
    case (Theorem \<Gamma> B \<Sigma>)
    have "\<Gamma> \<turnstile>\<^sub>H Imp A B"
      using Theorem.prems(1) Theorem.hyps by (rule H_proves_imp_of_right)
    then show ?case
      by (rule H_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> \<Sigma> B C)
    have A_type: "\<Gamma> \<turnstile> A : Prop"
      using Derive_MP.prems by simp
    have \<Sigma>_sub: "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
      using Derive_MP.prems by simp
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule H_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2) by (auto dest: H_derivable_formula elim: has_type.cases)
    have prop_taut: "prop_tautology \<Gamma>
        (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
      using A_type B_type C_type by (rule prop_tautology_deduction_mp)
    have taut: "\<Gamma> \<turnstile>\<^sub>H
        Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
      using prop_taut by (rule H_proves.PC)
    have d_taut: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H
        Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
      using taut by (rule H_derivable.Theorem)
    have IH_B: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A B"
      using A_type \<Sigma>_sub by (rule Derive_MP.IH(1))
    have IH_imp: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A (Imp B C)"
      using A_type \<Sigma>_sub by (rule Derive_MP.IH(2))
    have step1: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H
        Imp (Imp A (Imp B C)) (Imp A C)"
      using IH_B d_taut by (rule H_derivable.Derive_MP)
    show ?case
      using IH_imp step1 by (rule H_derivable.Derive_MP)
  qed
  show ?thesis
    using assms(1,3) by (rule aux)
qed

lemma H_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; A # \<Delta> \<turnstile>\<^sub>H B"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A B"
proof -
  have sub: "set (A # \<Delta>) \<subseteq> insert A (set \<Delta>)"
    by auto
  show ?thesis
    using assms(1) assms(2) sub by (rule H_derivable_deduction_subset)
qed

lemma H_derivable_shifted_inst:
  assumes typed_\<Delta>: "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and d: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>H Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp (Exists \<sigma> P) Q"
  using typed_\<Delta> d Q_type
proof (induction \<Delta> arbitrary: Q)
  case Nil
  have d_thm: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp P (shift Q)"
    using Nil.prems(2) by (rule H_derivable_empty_imp_proves) simp
  have inst: "\<Gamma> \<turnstile>\<^sub>H Imp (Exists \<sigma> P) Q"
    using P_type Nil.prems(3) d_thm by (rule H_proves.Inst)
  then show ?case
    by (rule H_derivable.Theorem)
next
  case (Cons A \<Delta>)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Cons.prems(1) by simp
  have rest_typed: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(1) by simp
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Cons.prems(3) by (rule weakening_front)
  have d_cons: "\<sigma> # \<Gamma> ; shift A # map shift \<Delta> \<turnstile>\<^sub>H
      Imp P (shift Q)"
    using Cons.prems(2) by simp
  have d_deduct: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>H
      Imp (shift A) (Imp P (shift Q))"
    using shift_A_type d_cons by (rule H_derivable_deduction)
  have taut: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro H_proves.PC prop_tautology_swap_imp)
  have d_taut: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>H
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using taut by (rule H_derivable.Theorem)
  have d_swapped_raw: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>H
      Imp P (Imp (shift A) (shift Q))"
    using d_deduct d_taut by (rule H_derivable.Derive_MP)
  have shift_imp: "shift (Imp A Q) = Imp (shift A) (shift Q)"
    by (simp add: shift_def)
  have d_swapped: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>H
      Imp P (shift (Imp A Q))"
    using d_swapped_raw by (simp add: shift_imp)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type Cons.prems(3) by auto
  have IH: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp (Exists \<sigma> P) (Imp A Q)"
    using rest_typed d_swapped AQ_type by (rule Cons.IH)
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> P : Prop"
    using P_type by auto
  have IH_lift: "\<Gamma> ; A # \<Delta> \<turnstile>\<^sub>H
      Imp (Exists \<sigma> P) (Imp A Q)"
    using IH by (rule H_derivable_mono) auto
  have d_exists: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>H Exists \<sigma> P"
    using exists_type by (intro H_derivable.Assumption) simp
  have IH_lift': "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>H
      Imp (Exists \<sigma> P) (Imp A Q)"
    using IH_lift by (rule H_derivable_mono) auto
  have d_A: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>H A"
    using A_type by (intro H_derivable.Assumption) simp
  have d_AQ: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>H Imp A Q"
    using d_exists IH_lift' by (rule H_derivable.Derive_MP)
  have d_Q: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>H Q"
    using d_A d_AQ by (rule H_derivable.Derive_MP)
  show ?case
    using exists_type d_Q by (rule H_derivable_deduction)
qed

lemma H_set_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; insert A T \<turnstile>\<^sub>H\<^sub>s B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A B"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> insert A T"
    and dB: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H B"
    using assms(2) unfolding H_set_derivable_def by blast
  let ?\<Delta> = "removeAll A \<Delta>"
  have \<Delta>_mono: "set \<Delta> \<subseteq> set (A # ?\<Delta>)"
    by auto
  have dB': "\<Gamma> ; A # ?\<Delta> \<turnstile>\<^sub>H B"
    using dB by (rule H_derivable_mono) (use \<Delta>_mono in blast)
  have dImp: "\<Gamma> ; ?\<Delta> \<turnstile>\<^sub>H Imp A B"
    using assms(1) dB' by (rule H_derivable_deduction)
  have "set ?\<Delta> \<subseteq> T"
    using \<Delta>_sub by auto
  then show ?thesis
    unfolding H_set_derivable_def using dImp by blast
qed

lemma H_set_derivable_shifted_inst:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Exists \<sigma> P) Q"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> shift ` T"
    and d\<Delta>: "\<sigma> # \<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp P (shift Q)"
    using assms(2) unfolding H_set_derivable_def by blast
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> set \<Delta>"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using \<Delta>_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  define \<Sigma> where "\<Sigma> = map pre \<Delta>"
  have \<Sigma>_sub: "set \<Sigma> \<subseteq> T"
    using pre_prop unfolding \<Sigma>_def by auto
  have map_shift_\<Sigma>: "map shift \<Sigma> = \<Delta>"
    unfolding \<Sigma>_def using pre_prop by (induction \<Delta>) auto
  have typed_\<Sigma>: "\<And>A. A \<in> set \<Sigma> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    using typed \<Sigma>_sub unfolding typed_theory_def by blast
  have d\<Sigma>: "\<sigma> # \<Gamma> ; map shift \<Sigma> \<turnstile>\<^sub>H Imp P (shift Q)"
    using d\<Delta> map_shift_\<Sigma> by simp
  have lower: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>H Imp (Exists \<sigma> P) Q"
    using typed_\<Sigma> d\<Sigma> P_type Q_type
    by (rule H_derivable_shifted_inst)
  show ?thesis
    unfolding H_set_derivable_def using \<Sigma>_sub lower by blast
qed

lemma H_set_derivable_fresh_witness_eigen_imp_false:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s
    Imp (Imp (shift (Exists \<sigma> A)) A) ObjFalse"
proof -
  let ?E = "Imp (shift (Exists \<sigma> A)) A"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(4) by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have E_type: "\<sigma> # \<Gamma> \<turnstile> ?E : Prop"
    using shifted_exists_type assms(4) by auto
  have d_false: "\<sigma> # \<Gamma> ; insert ?E (shift ` T) \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using assms(1,2,3) by (rule H_set_derivable_abstract_fresh_witness_false)
  show ?thesis
    using E_type d_false by (rule H_set_derivable_deduction)
qed

lemma H_set_derivable_fresh_witness_false:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_imp_false: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s Imp ?P ObjFalse"
    using d fresh_T fresh_A A_type
    by (rule H_set_derivable_fresh_witness_eigen_imp_false)
  have d_imp_shift_false: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>H\<^sub>s
      Imp ?P (shift ObjFalse)"
    using d_imp_false by simp
  have lower: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp ?Q ObjFalse"
    using typed d_imp_shift_false P_type typed_ObjFalse
    by (rule H_set_derivable_shifted_inst)
  have Q_thm: "\<Gamma> \<turnstile>\<^sub>H ?Q"
    using A_type by (rule H_proves_exists_imp_shift_exists)
  have d_Q: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ?Q"
    using Q_thm by (rule H_set_Theorem)
  show ?thesis
    using d_Q lower by (rule H_set_MP)
qed

definition H_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "H_consistent \<Gamma> T \<longleftrightarrow> \<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"

definition H_deductively_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "H_deductively_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A \<longrightarrow> A \<in> T)"

definition H_negation_complete :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "H_negation_complete \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> A \<in> T \<or> Neg A \<in> T)"

definition H_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "H_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> H_consistent \<Gamma> T \<and> H_negation_complete \<Gamma> T"

definition H_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "H_Henkin_theory \<Gamma> T \<longleftrightarrow>
    H_maximal_consistent \<Gamma> T \<and> Henkin_witnessed \<Gamma> T"

definition H_Henkin_axioms_consistency_preserving ::
    "ctx \<Rightarrow> (otype \<Rightarrow> oterm \<Rightarrow> string) \<Rightarrow> bool" where
  "H_Henkin_axioms_consistency_preserving \<Gamma> h \<longleftrightarrow>
    (\<forall>T. typed_theory \<Gamma> T \<longrightarrow> H_consistent \<Gamma> T \<longrightarrow>
      H_consistent \<Gamma> (T \<union> Henkin_axioms \<Gamma> h))"

lemma H_consistentD:
  assumes "H_consistent \<Gamma> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  using assms unfolding H_consistent_def by blast

lemma H_consistent_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "H_consistent \<Gamma> T"
proof (unfold H_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  then have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    using assms(1) by (rule H_set_ex_falso)
  then show False
    using assms(2) by blast
qed

lemma H_consistent_subset:
  assumes "H_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "H_consistent \<Gamma> T"
  using assms H_set_derivable_mono unfolding H_consistent_def by blast

lemma H_consistent_insert_fresh_witness_axiom:
  assumes typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "H_consistent \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold H_consistent_def, intro notI)
  assume d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using typed d fresh_T fresh_A A_type
    by (rule H_set_derivable_fresh_witness_false)
  then show False
    using consistent unfolding H_consistent_def by blast
qed

lemma H_consistent_add_fresh_witness_axioms:
  assumes "typed_theory \<Gamma> T"
    and "H_consistent \<Gamma> T"
    and "fresh_witness_axiom_sequence \<Gamma> T xs"
  shows "H_consistent \<Gamma> (add_witness_axioms xs T)"
  using assms
proof (induction xs arbitrary: T)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain c \<sigma> A where x_def: "x = (c, \<sigma>, A)"
    by (cases x) auto
  have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Cons.prems(3) unfolding x_def by simp
  have fresh_T: "c \<notin> consts_of_set T"
    using Cons.prems(3) unfolding x_def by simp
  have fresh_A: "c \<notin> consts_of A"
    using Cons.prems(3) unfolding x_def by simp
  have tail_fresh: "fresh_witness_axiom_sequence \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) xs"
    using Cons.prems(3) unfolding x_def by simp
  have typed_insert: "typed_theory \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) A_type by (rule typed_theory_insert_henkin_witness_axiom)
  have consistent_insert: "H_consistent \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) Cons.prems(2) fresh_T fresh_A A_type
    by (rule H_consistent_insert_fresh_witness_axiom)
  show ?case
    using Cons.IH[OF typed_insert consistent_insert tail_fresh]
    unfolding x_def by simp
qed

lemma H_consistent_fresh_witness_extension_exists:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
    and typed_specs: "\<And>\<sigma> A. (\<sigma>, A) \<in> set specs \<Longrightarrow>
      \<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<exists>xs. fresh_witness_axiom_sequence \<Gamma> T xs \<and>
    witness_bodies xs = specs \<and>
    typed_theory \<Gamma> (add_witness_axioms xs T) \<and>
    H_consistent \<Gamma> (add_witness_axioms xs T)"
proof -
  obtain xs where fresh: "fresh_witness_axiom_sequence \<Gamma> T xs"
    and bodies: "witness_bodies xs = specs"
    using fresh_witness_axiom_sequence_exists[OF finite_T typed_specs] by blast
  have typed_ext: "typed_theory \<Gamma> (add_witness_axioms xs T)"
    using typed fresh by (rule typed_theory_add_fresh_witness_axioms)
  have consistent_ext: "H_consistent \<Gamma> (add_witness_axioms xs T)"
    using typed consistent fresh by (rule H_consistent_add_fresh_witness_axioms)
  show ?thesis
    using fresh bodies typed_ext consistent_ext by blast
qed

lemma H_staged_henkin_step_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "H_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using typed consistent fresh_T fresh_A True
      by (rule H_consistent_insert_fresh_witness_axiom)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma H_staged_henkin_chain_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(1) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(2) by (rule staged_henkin_chain_typed)
  have consistent_n: "H_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using finite_n typed_n consistent_n
    by (simp add: H_staged_henkin_step_consistent)
qed

lemma H_staged_henkin_extension_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold H_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; staged_henkin_extension \<Gamma> T enum
    \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using d_false by (rule H_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  have "\<exists>n. U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    by blast
  have "\<Gamma> ; staged_henkin_chain \<Gamma> T enum n \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule H_set_derivable_mono)
  moreover have "H_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule H_staged_henkin_chain_consistent)
  ultimately show False
    unfolding H_consistent_def by blast
qed

lemma H_consistent_singleton_neg_of_not_proves:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>H A"
  shows "H_consistent \<Gamma> {Neg A}"
proof (unfold H_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; {Neg A} \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "\<Gamma> ; {} \<turnstile>\<^sub>H\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule H_set_derivable_deduction)
  have imp_false: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg A) ObjFalse"
    using d_imp_false by (rule H_set_derivable_empty_imp_proves)
  have imp_A: "\<Gamma> \<turnstile>\<^sub>H Imp (Imp (Neg A) ObjFalse) A"
    using assms(1) by (rule H_proves_imp_neg_false_to_formula)
  have "\<Gamma> \<turnstile>\<^sub>H A"
    using imp_false imp_A by (rule H_proves.MP)
  then show False
    using assms(2) by contradiction
qed

lemma H_deductively_closedD:
  assumes "H_deductively_closed \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "A \<in> T"
proof -
  have "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule H_set_derivable_formula)
  then show ?thesis
    using assms unfolding H_deductively_closed_def by blast
qed

lemma H_contains_theorems:
  assumes "H_deductively_closed \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>H A"
  shows "A \<in> T"
proof -
  have derivable: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    using assms(2) by (rule H_set_Theorem)
  show ?thesis
    using assms(1) derivable by (rule H_deductively_closedD)
qed

lemma H_closed_under_MP:
  assumes "typed_theory \<Gamma> T"
    and "H_deductively_closed \<Gamma> T"
    and "A \<in> T"
    and "Imp A B \<in> T"
  shows "B \<in> T"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1,3) by (rule typed_theoryD)
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms(1,4) by (rule typed_theoryD)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    by (auto elim: has_type.cases)
  have dA: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    using assms(3) A_type by (rule H_set_Assumption)
  have dImp: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A B"
    using assms(4) imp_type by (rule H_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s B"
    using dA dImp by (rule H_set_MP)
  then show ?thesis
    using assms(2) B_type unfolding H_deductively_closed_def by blast
qed

lemma H_Henkin_witnessed_from_scheme:
  assumes "typed_theory \<Gamma> T"
    and "H_deductively_closed \<Gamma> T"
    and "Henkin_scheme_in \<Gamma> T W"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  have W_type: "\<Gamma> \<turnstile> W \<sigma> A : \<sigma>"
    using assms(3) A_type by (rule Henkin_scheme_inD(1))
  have imp_in: "Imp (Exists \<sigma> A) (subst0 (W \<sigma> A) A) \<in> T"
    using assms(3) A_type by (rule Henkin_scheme_inD(2))
  have subst_in: "subst0 (W \<sigma> A) A \<in> T"
    using assms(1,2) exists_in imp_in by (rule H_closed_under_MP)
  show "\<exists>V. \<Gamma> \<turnstile> V : \<sigma> \<and> subst0 V A \<in> T"
    using W_type subst_in by blast
qed

lemma H_Henkin_witnessed_from_available:
  assumes "typed_theory \<Gamma> T"
    and "H_deductively_closed \<Gamma> T"
    and "Henkin_witness_axioms_available \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where imp_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using assms(3) A_type
    unfolding Henkin_witness_axioms_available_def by blast
  have witness_type: "\<Gamma> \<turnstile> Const c \<sigma> : \<sigma>"
    by auto
  have subst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using assms(1,2) exists_in imp_in
    unfolding henkin_witness_axiom_def
    by (rule H_closed_under_MP)
  show "\<exists>V. \<Gamma> \<turnstile> V : \<sigma> \<and> subst0 V A \<in> T"
    using witness_type subst_in by blast
qed

lemma H_set_derives_ObjFalse_of_formula_and_neg:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "Neg A \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule H_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp (Neg A) ObjFalse)"
    using A_type by (intro H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule H_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
    using assms(2) neg_type by (rule H_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule H_set_MP)
  then show ?thesis
    using d_neg by (metis H_set_MP)
qed

lemma H_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule H_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp (Neg A) ObjFalse)"
    using A_type by (intro H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule H_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule H_set_MP)
  then show ?thesis
    using assms(2) by (metis H_set_MP)
qed

lemma H_consistent_not_both_derivable:
  assumes "H_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
  then have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A" .
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using assms(2) d_neg by (rule H_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding H_consistent_def by blast
qed

lemma H_consistent_not_derives_with_neg:
  assumes "H_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  then have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using assms(2) by (rule H_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding H_consistent_def by blast
qed

lemma H_consistent_insert_formula_if_not_neg_derivable:
  assumes "H_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
  shows "H_consistent \<Gamma> (insert A T)"
proof (unfold H_consistent_def, intro notI)
  assume "\<Gamma> ; insert A T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  then have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>H\<^sub>s ObjFalse" .
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule H_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using H_proves_imp_false_to_neg[OF assms(2)] by (rule H_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule H_set_MP)
  then show False
    using assms(3) by blast
qed

lemma H_consistent_insert_neg_if_not_derivable:
  assumes "H_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "H_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold H_consistent_def, intro notI)
  assume "\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type \<open>\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>H\<^sub>s ObjFalse\<close>
    by (rule H_set_derivable_deduction)
  have d_A_thm: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Imp (Neg A) ObjFalse) A"
    using H_proves_imp_neg_false_to_formula[OF assms(2)] by (rule H_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    using d_imp_false d_A_thm by (rule H_set_MP)
  then show False
    using assms(3) by blast
qed

lemma H_consistent_insert_neg_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "H_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have consistent: "H_consistent \<Gamma> T"
    using assms by (rule H_consistent_of_not_set_derivable)
  show ?thesis
    using consistent assms by (rule H_consistent_insert_neg_if_not_derivable)
qed

lemma H_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "H_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> H_consistent \<Gamma> (insert A T)"
  shows "H_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have "\<Gamma> ; insert A T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using assms(3) unfolding H_consistent_def by blast
  then have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>H\<^sub>s ObjFalse" .
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule H_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using H_proves_imp_false_to_neg[OF assms(2)] by (rule H_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule H_set_MP)
  have not_d_A: "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  proof
    assume d_A: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
      using d_A d_neg by (rule H_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding H_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A by (rule H_consistent_insert_neg_if_not_derivable)
qed

lemma H_consistent_decidable_extension:
  assumes "H_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "H_consistent \<Gamma> (insert A T) \<or>
    H_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "H_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis by blast
next
  case False
  then have not_consistent: "\<not> H_consistent \<Gamma> (insert A T)" .
  have "H_consistent \<Gamma> (insert (Neg A) T)"
    using assms(1) assms(2) not_consistent
    by (rule H_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis by blast
qed

lemma H_consistent_no_neg_pair:
  assumes "H_consistent \<Gamma> T"
    and "A \<in> T"
    and "Neg A \<in> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows False
proof -
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    using assms(2,4) by (rule H_set_Assumption)
  then have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using assms(3) by (rule H_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding H_consistent_def by blast
qed

lemma H_maximal_consistent_deductively_closed:
  assumes "H_maximal_consistent \<Gamma> T"
  shows "H_deductively_closed \<Gamma> T"
proof (unfold H_deductively_closed_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and derivable: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  have consistent: "H_consistent \<Gamma> T"
    using assms unfolding H_maximal_consistent_def by blast
  have complete: "H_negation_complete \<Gamma> T"
    using assms unfolding H_maximal_consistent_def by blast
  show "A \<in> T"
  proof (rule ccontr)
    assume "A \<notin> T"
    then have "Neg A \<in> T"
      using complete A_type unfolding H_negation_complete_def by blast
    then have neg_in: "Neg A \<in> T" .
    have "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
      using consistent neg_in by (rule H_consistent_not_derives_with_neg)
    then show False
      using derivable by blast
  qed
qed

lemma H_maximal_neg_mem_iff:
  assumes "H_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "Neg A \<in> T \<longleftrightarrow> A \<notin> T"
proof
  assume neg_in: "Neg A \<in> T"
  show "A \<notin> T"
  proof
    assume A_in: "A \<in> T"
    have consistent: "H_consistent \<Gamma> T"
      using assms(1) unfolding H_maximal_consistent_def by blast
    show False
      using consistent A_in neg_in assms(2) by (rule H_consistent_no_neg_pair)
  qed
next
  assume A_notin: "A \<notin> T"
  have complete: "H_negation_complete \<Gamma> T"
    using assms(1) unfolding H_maximal_consistent_def by blast
  then show "Neg A \<in> T"
    using A_notin assms(2) unfolding H_negation_complete_def by blast
qed

lemma H_maximal_contains_theorems:
  assumes "H_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>H A"
  shows "A \<in> T"
  using H_maximal_consistent_deductively_closed[OF assms(1)] assms(2)
  by (rule H_contains_theorems)

lemma H_Henkin_maximal_consistent:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "H_maximal_consistent \<Gamma> T"
  using assms unfolding H_Henkin_theory_def by blast

lemma H_Henkin_theory_witnessed:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
  using assms unfolding H_Henkin_theory_def by blast

lemma H_Henkin_typed_theory:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "typed_theory \<Gamma> T"
  using H_Henkin_maximal_consistent[OF assms]
  unfolding H_maximal_consistent_def by blast

lemma H_Henkin_consistent:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "H_consistent \<Gamma> T"
  using H_Henkin_maximal_consistent[OF assms]
  unfolding H_maximal_consistent_def by blast

lemma H_Henkin_negation_complete:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "H_negation_complete \<Gamma> T"
  using H_Henkin_maximal_consistent[OF assms]
  unfolding H_maximal_consistent_def by blast

lemma H_Henkin_deductively_closed:
  assumes "H_Henkin_theory \<Gamma> T"
  shows "H_deductively_closed \<Gamma> T"
  using H_Henkin_maximal_consistent[OF assms]
  by (rule H_maximal_consistent_deductively_closed)

lemma H_Henkin_contains_derivable:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
  shows "A \<in> T"
  using H_Henkin_deductively_closed[OF assms(1)] assms(2)
  by (rule H_deductively_closedD)

lemma H_Henkin_contains_theorems:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>H A"
  shows "A \<in> T"
  using H_Henkin_deductively_closed[OF assms(1)] assms(2)
  by (rule H_contains_theorems)

lemma H_Henkin_closed_under_MP:
  assumes "H_Henkin_theory \<Gamma> T"
    and "A \<in> T"
    and "Imp A B \<in> T"
  shows "B \<in> T"
  using H_Henkin_typed_theory[OF assms(1)]
    H_Henkin_deductively_closed[OF assms(1)] assms(2,3)
  by (rule H_closed_under_MP)

lemma H_maximal_imp_mem_iff:
  assumes "H_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Imp A B \<in> T \<longleftrightarrow> (A \<in> T \<longrightarrow> B \<in> T)"
proof
  assume imp_in: "Imp A B \<in> T"
  show "A \<in> T \<longrightarrow> B \<in> T"
  proof
    assume A_in: "A \<in> T"
    have typed: "typed_theory \<Gamma> T"
      using assms(1) unfolding H_maximal_consistent_def by blast
    have closed: "H_deductively_closed \<Gamma> T"
      using assms(1) by (rule H_maximal_consistent_deductively_closed)
    show "B \<in> T"
      using typed closed A_in imp_in by (rule H_closed_under_MP)
  qed
next
  assume semantic_condition: "A \<in> T \<longrightarrow> B \<in> T"
  have closed: "H_deductively_closed \<Gamma> T"
    using assms(1) by (rule H_maximal_consistent_deductively_closed)
  show "Imp A B \<in> T"
  proof (cases "A \<in> T")
    case True
    then have B_in: "B \<in> T"
      using semantic_condition by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>H Imp B (Imp A B)"
      using assms(2,3) by (intro H_proves.PC prop_tautology_imp_of_right)
    have "Imp B (Imp A B) \<in> T"
      using closed taut by (rule H_contains_theorems)
    then show ?thesis
    proof -
      have typed: "typed_theory \<Gamma> T"
        using assms(1) unfolding H_maximal_consistent_def by blast
      show ?thesis
        using typed closed B_in \<open>Imp B (Imp A B) \<in> T\<close>
        by (rule H_closed_under_MP)
    qed
  next
    case False
    then have neg_in: "Neg A \<in> T"
      using H_maximal_neg_mem_iff[OF assms(1,2)] by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg A) (Imp A B)"
      using assms(2,3) by (intro H_proves.PC prop_tautology_imp_of_neg_left)
    have "Imp (Neg A) (Imp A B) \<in> T"
      using closed taut by (rule H_contains_theorems)
    then show ?thesis
    proof -
      have typed: "typed_theory \<Gamma> T"
        using assms(1) unfolding H_maximal_consistent_def by blast
      have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
        using assms(2) by auto
      show ?thesis
        using typed closed neg_in \<open>Imp (Neg A) (Imp A B) \<in> T\<close>
        by (rule H_closed_under_MP)
    qed
  qed
qed

lemma H_maximal_conj_mem_iff:
  assumes "H_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Conj A B \<in> T \<longleftrightarrow> A \<in> T \<and> B \<in> T"
proof
  assume conj_in: "Conj A B \<in> T"
  have closed: "H_deductively_closed \<Gamma> T"
    using assms(1) by (rule H_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding H_maximal_consistent_def by blast
  have left_taut: "\<Gamma> \<turnstile>\<^sub>H Imp (Conj A B) A"
    using assms(2,3) by (intro H_proves.PC prop_tautology_conj_left)
  have right_taut: "\<Gamma> \<turnstile>\<^sub>H Imp (Conj A B) B"
    using assms(2,3) by (intro H_proves.PC prop_tautology_conj_right)
  have left_in: "Imp (Conj A B) A \<in> T"
    using closed left_taut by (rule H_contains_theorems)
  have right_in: "Imp (Conj A B) B \<in> T"
    using closed right_taut by (rule H_contains_theorems)
  have A_in: "A \<in> T"
    using typed closed conj_in left_in by (rule H_closed_under_MP)
  have B_in: "B \<in> T"
    using typed closed conj_in right_in by (rule H_closed_under_MP)
  show "A \<in> T \<and> B \<in> T"
    using A_in B_in by blast
next
  assume both: "A \<in> T \<and> B \<in> T"
  have closed: "H_deductively_closed \<Gamma> T"
    using assms(1) by (rule H_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding H_maximal_consistent_def by blast
  have taut: "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp B (Conj A B))"
    using assms(2,3) by (intro H_proves.PC prop_tautology_conj_intro)
  have taut_in: "Imp A (Imp B (Conj A B)) \<in> T"
    using closed taut by (rule H_contains_theorems)
  have imp_in: "Imp B (Conj A B) \<in> T"
    using typed closed conjunct1[OF both] taut_in by (rule H_closed_under_MP)
  show "Conj A B \<in> T"
    using typed closed conjunct2[OF both] imp_in by (rule H_closed_under_MP)
qed

lemma H_maximal_disj_mem_iff:
  assumes "H_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Disj A B \<in> T \<longleftrightarrow> A \<in> T \<or> B \<in> T"
proof
  assume disj_in: "Disj A B \<in> T"
  show "A \<in> T \<or> B \<in> T"
  proof (cases "A \<in> T")
    case True
    then show ?thesis
      by blast
  next
    case False
    have neg_A_in: "Neg A \<in> T"
      using H_maximal_neg_mem_iff[OF assms(1,2)] False by blast
    have closed: "H_deductively_closed \<Gamma> T"
      using assms(1) by (rule H_maximal_consistent_deductively_closed)
    have typed: "typed_theory \<Gamma> T"
      using assms(1) unfolding H_maximal_consistent_def by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>H Imp (Disj A B) (Imp (Neg A) B)"
      using assms(2,3) by (intro H_proves.PC prop_tautology_disj_elim_neg_left)
    have taut_in: "Imp (Disj A B) (Imp (Neg A) B) \<in> T"
      using closed taut by (rule H_contains_theorems)
    have imp_in: "Imp (Neg A) B \<in> T"
      using typed closed disj_in taut_in by (rule H_closed_under_MP)
    have neg_A_type: "\<Gamma> \<turnstile> Neg A : Prop"
      using assms(2) by auto
    have B_in: "B \<in> T"
      using typed closed neg_A_in imp_in by (rule H_closed_under_MP)
    then show ?thesis
      by blast
  qed
next
  assume disj_condition: "A \<in> T \<or> B \<in> T"
  have closed: "H_deductively_closed \<Gamma> T"
    using assms(1) by (rule H_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding H_maximal_consistent_def by blast
  show "Disj A B \<in> T"
  proof (rule disj_condition[THEN disjE])
    assume A_in: "A \<in> T"
    have taut: "\<Gamma> \<turnstile>\<^sub>H Imp A (Disj A B)"
      using assms(2,3) by (intro H_proves.PC prop_tautology_disj_left_intro)
    have taut_in: "Imp A (Disj A B) \<in> T"
      using closed taut by (rule H_contains_theorems)
    show ?thesis
      using typed closed A_in taut_in by (rule H_closed_under_MP)
  next
    assume B_in: "B \<in> T"
    have taut: "\<Gamma> \<turnstile>\<^sub>H Imp B (Disj A B)"
      using assms(2,3) by (intro H_proves.PC prop_tautology_disj_right_intro)
    have taut_in: "Imp B (Disj A B) \<in> T"
      using closed taut by (rule H_contains_theorems)
    show ?thesis
      using typed closed B_in taut_in by (rule H_closed_under_MP)
  qed
qed

lemma H_universal_instantiation_in:
  assumes "H_deductively_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "Forall \<sigma> A \<in> T"
  shows "subst0 W A \<in> T"
proof -
  have forall_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    using assms(2) by auto
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using assms(2,3) by (rule subst0_preserves_typing)
  have ui: "\<Gamma> \<turnstile>\<^sub>H Imp (Forall \<sigma> A) (subst0 W A)"
    using assms(2,3) by (rule H_proves.UI)
  have d_forall: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Forall \<sigma> A"
    using assms(4) forall_type by (rule H_set_Assumption)
  have d_ui: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Forall \<sigma> A) (subst0 W A)"
    using ui by (rule H_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s subst0 W A"
    using d_forall d_ui by (rule H_set_MP)
  then show ?thesis
    using assms(1) subst_type unfolding H_deductively_closed_def by blast
qed

lemma H_existential_generalization_in:
  assumes "H_deductively_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "subst0 W A \<in> T"
  shows "Exists \<sigma> A \<in> T"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using assms(2,3) by (rule subst0_preserves_typing)
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(2) by auto
  have eg: "\<Gamma> \<turnstile>\<^sub>H Imp (subst0 W A) (Exists \<sigma> A)"
    using assms(2,3) by (rule H_proves.EG)
  have d_subst: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s subst0 W A"
    using assms(4) subst_type by (rule H_set_Assumption)
  have d_eg: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (subst0 W A) (Exists \<sigma> A)"
    using eg by (rule H_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Exists \<sigma> A"
    using d_subst d_eg by (rule H_set_MP)
  then show ?thesis
    using assms(1) exists_type unfolding H_deductively_closed_def by blast
qed

lemma H_beta_eta_equiv_in:
  assumes "H_deductively_closed \<Gamma> T"
    and "beta_eta_equiv \<Gamma> Prop A B"
  shows "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
  using assms(1) H_beta_eta_equiv[OF assms(2)]
  by (rule H_contains_theorems)

lemma H_identity_refl_in:
  assumes "H_deductively_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "Eq \<sigma> M M \<in> T"
  using assms(1) H_proves.Ref[OF assms(2)]
  by (rule H_contains_theorems)

lemma H_identity_subst_in:
  assumes "typed_theory \<Gamma> T"
    and "H_deductively_closed \<Gamma> T"
    and "Eq \<sigma> M N \<in> T"
    and "App F M \<in> T"
    and "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "App F N \<in> T"
proof -
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using assms(5,6) by auto
  have appM_type: "\<Gamma> \<turnstile> App F M : Prop"
    using assms(5,7) by auto
  have appN_type: "\<Gamma> \<turnstile> App F N : Prop"
    using assms(6,7) by auto
  have ll: "\<Gamma> \<turnstile>\<^sub>H Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using assms(5,6,7) by (rule H_proves.LL)
  have d_eq: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Eq \<sigma> M N"
    using assms(3) eq_type by (rule H_set_Assumption)
  have d_ll: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using ll by (rule H_set_Theorem)
  have d_appM: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s App F M"
    using assms(4) appM_type by (rule H_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s Imp (App F M) (App F N)"
    using d_eq d_ll by (rule H_set_MP)
  then have "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s App F N"
    using d_appM by (metis H_set_MP)
  then show ?thesis
    using assms(2) appN_type unfolding H_deductively_closed_def by blast
qed

lemma H_Henkin_neg_mem_iff:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "Neg A \<in> T \<longleftrightarrow> A \<notin> T"
proof -
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2) by (rule H_maximal_neg_mem_iff)
qed

lemma H_Henkin_imp_mem_iff:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Imp A B \<in> T \<longleftrightarrow> (A \<in> T \<longrightarrow> B \<in> T)"
proof -
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule H_maximal_imp_mem_iff)
qed

lemma H_Henkin_conj_mem_iff:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Conj A B \<in> T \<longleftrightarrow> A \<in> T \<and> B \<in> T"
proof -
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule H_maximal_conj_mem_iff)
qed

lemma H_Henkin_disj_mem_iff:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Disj A B \<in> T \<longleftrightarrow> A \<in> T \<or> B \<in> T"
proof -
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule H_maximal_disj_mem_iff)
qed

lemma H_Henkin_forall_instance:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "Forall \<sigma> A \<in> T"
  shows "subst0 W A \<in> T"
proof -
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  have closed: "H_deductively_closed \<Gamma> T"
    using maximal by (rule H_maximal_consistent_deductively_closed)
  show ?thesis
    using closed assms(2,3,4) by (rule H_universal_instantiation_in)
qed

lemma H_Henkin_forall_mem_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "Forall \<sigma> A \<in> T \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T)"
proof
  assume forall_in: "Forall \<sigma> A \<in> T"
  show "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
  proof (intro allI impI)
    fix W
    assume W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    show "subst0 W A \<in> T"
      using henkin A_type W_type forall_in
      by (rule H_Henkin_forall_instance)
  qed
next
  assume all_instances: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
  show "Forall \<sigma> A \<in> T"
  proof (rule ccontr)
    assume forall_notin: "Forall \<sigma> A \<notin> T"
    let ?F = "Forall \<sigma> A"
    let ?E = "Exists \<sigma> (Neg A)"
    have F_type: "\<Gamma> \<turnstile> ?F : Prop"
      using A_type by auto
    have neg_A_type: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop"
      using A_type by auto
    have not_F_in: "Neg ?F \<in> T"
      using H_Henkin_neg_mem_iff[OF henkin F_type] forall_notin by blast
    have imp_theorem: "\<Gamma> \<turnstile>\<^sub>H Imp (Neg ?F) ?E"
      using A_type by (rule H_proves_not_forall_imp_exists_neg)
    have imp_in: "Imp (Neg ?F) ?E \<in> T"
      using henkin imp_theorem by (rule H_Henkin_contains_theorems)
    have exists_in: "?E \<in> T"
      using henkin not_F_in imp_in by (rule H_Henkin_closed_under_MP)
    have witnessed: "Henkin_witnessed \<Gamma> T"
      using henkin unfolding H_Henkin_theory_def by blast
    obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
      and neg_inst_in: "subst0 W (Neg A) \<in> T"
      using witnessed neg_A_type exists_in
      unfolding Henkin_witnessed_def by blast
    have inst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
      using A_type W_type by (rule subst0_preserves_typing)
    have inst_in: "subst0 W A \<in> T"
      using all_instances W_type by blast
    have "Neg (subst0 W A) \<in> T"
      using neg_inst_in by (simp add: subst0_def)
    then have "subst0 W A \<notin> T"
      using H_Henkin_neg_mem_iff[OF henkin inst_type] by blast
    then show False
      using inst_in by blast
  qed
qed

lemma H_Henkin_exists_mem_iff:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "Exists \<sigma> A \<in> T \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T)"
proof
  assume exists_in: "Exists \<sigma> A \<in> T"
  have witnessed: "Henkin_witnessed \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  then show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using assms(2) exists_in unfolding Henkin_witnessed_def by blast
next
  assume "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
  then obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_in: "subst0 W A \<in> T"
    by blast
  have maximal: "H_maximal_consistent \<Gamma> T"
    using assms(1) unfolding H_Henkin_theory_def by blast
  have closed: "H_deductively_closed \<Gamma> T"
    using maximal by (rule H_maximal_consistent_deductively_closed)
  show "Exists \<sigma> A \<in> T"
    using closed assms(2) W_type subst_in
    by (rule H_existential_generalization_in)
qed

lemma H_Henkin_exists_witness:
  assumes "H_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "Exists \<sigma> A \<in> T"
  obtains W where "\<Gamma> \<turnstile> W : \<sigma>" and "subst0 W A \<in> T"
  using H_Henkin_exists_mem_iff[OF assms(1,2)] assms(3) by blast

definition H_lindenbaum_step :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "H_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if H_consistent \<Gamma> (insert A T) then insert A T else insert (Neg A) T)
     else T)"

primrec H_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "H_lindenbaum_chain \<Gamma> T enum 0 = T"
| "H_lindenbaum_chain \<Gamma> T enum (Suc n) =
    H_lindenbaum_step \<Gamma> (enum n) (H_lindenbaum_chain \<Gamma> T enum n)"

definition H_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "H_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. H_lindenbaum_chain \<Gamma> T enum n)"

lemma H_lindenbaum_step_extends:
  "T \<subseteq> H_lindenbaum_step \<Gamma> A T"
  unfolding H_lindenbaum_step_def by auto

lemma H_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (H_lindenbaum_step \<Gamma> A T)"
  using assms unfolding H_lindenbaum_step_def typed_theory_def by auto

lemma H_lindenbaum_step_consistent:
  assumes "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (H_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding H_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "H_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> unfolding H_lindenbaum_step_def by simp
  next
    case False
    have "H_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule H_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False unfolding H_lindenbaum_step_def by simp
  qed
qed

lemma H_lindenbaum_chain_step:
  "H_lindenbaum_chain \<Gamma> T enum n \<subseteq> H_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using H_lindenbaum_step_extends[of
      "H_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma H_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (H_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: H_lindenbaum_step_typed)
qed

lemma H_lindenbaum_chain_consistent:
  assumes "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (H_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: H_lindenbaum_step_consistent)
qed

lemma H_lindenbaum_extension_extends:
  "T \<subseteq> H_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> H_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> H_lindenbaum_extension \<Gamma> T enum"
    unfolding H_lindenbaum_extension_def by blast
qed

lemma H_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (H_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule H_lindenbaum_chain_typed)
  then show ?thesis
    unfolding H_lindenbaum_extension_def by (rule typed_theory_nat_union)
qed

lemma H_lindenbaum_extension_consistent:
  assumes "H_consistent \<Gamma> T"
  shows "H_consistent \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof (unfold H_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; H_lindenbaum_extension \<Gamma> T enum \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> H_lindenbaum_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using d_false by (rule H_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. H_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding H_lindenbaum_extension_def .
  have step: "\<And>n. H_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      H_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule H_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> H_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  obtain n where U_sub_chain: "U \<subseteq> H_lindenbaum_chain \<Gamma> T enum n"
    using \<open>\<exists>n. U \<subseteq> H_lindenbaum_chain \<Gamma> T enum n\<close> by (elim exE)
  have "\<Gamma> ; H_lindenbaum_chain \<Gamma> T enum n \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule H_set_derivable_mono)
  moreover have "H_consistent \<Gamma> (H_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule H_lindenbaum_chain_consistent)
  ultimately show False
    unfolding H_consistent_def by contradiction
qed

lemma H_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "H_negation_complete \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof (unfold H_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "H_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "H_lindenbaum_chain \<Gamma> T enum (Suc n) =
      H_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> H_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> H_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "H_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> H_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding H_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> H_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding H_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> H_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> H_lindenbaum_extension \<Gamma> T enum"
  proof
    assume A_in_chain: "A \<in> H_lindenbaum_chain \<Gamma> T enum (Suc n)"
    have chain_in_range:
      "H_lindenbaum_chain \<Gamma> T enum (Suc n) \<in> range (H_lindenbaum_chain \<Gamma> T enum)"
      by (rule rangeI)
    then have "A \<in> H_lindenbaum_extension \<Gamma> T enum"
      unfolding H_lindenbaum_extension_def
      using A_in_chain by (rule UnionI)
    then show ?thesis
      by (rule disjI1)
  next
    assume neg_in_chain: "Neg A \<in> H_lindenbaum_chain \<Gamma> T enum (Suc n)"
    have chain_in_range:
      "H_lindenbaum_chain \<Gamma> T enum (Suc n) \<in> range (H_lindenbaum_chain \<Gamma> T enum)"
      by (rule rangeI)
    then have "Neg A \<in> H_lindenbaum_extension \<Gamma> T enum"
      unfolding H_lindenbaum_extension_def
      using neg_in_chain by (rule UnionI)
    then show ?thesis
      by (rule disjI2)
  qed
qed

theorem H_lindenbaum_extension_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "H_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "H_maximal_consistent \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule H_lindenbaum_extension_typed)
  have consistent: "H_consistent \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule H_lindenbaum_extension_consistent)
  have complete: "H_negation_complete \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule H_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete unfolding H_maximal_consistent_def by simp
qed

theorem H_lindenbaum_extension_Henkin_theory_from_scheme:
  assumes "typed_theory \<Gamma> T"
    and "H_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
    and "Henkin_scheme_in \<Gamma> (H_lindenbaum_extension \<Gamma> T enum) W"
  shows "H_Henkin_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof -
  have maximal: "H_maximal_consistent \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(1,2,3) by (rule H_lindenbaum_extension_maximal_consistent)
  have typed: "typed_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using maximal unfolding H_maximal_consistent_def by simp
  have closed: "H_deductively_closed \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using maximal by (rule H_maximal_consistent_deductively_closed)
  have witnessed: "Henkin_witnessed \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using typed closed assms(4) by (rule H_Henkin_witnessed_from_scheme)
  show ?thesis
    using maximal witnessed unfolding H_Henkin_theory_def by simp
qed

theorem H_lindenbaum_extension_Henkin_theory_from_available:
  assumes "typed_theory \<Gamma> T"
    and "H_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
    and "Henkin_witness_axioms_available \<Gamma> T"
  shows "H_Henkin_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
proof -
  have maximal: "H_maximal_consistent \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(1,2,3) by (rule H_lindenbaum_extension_maximal_consistent)
  have typed: "typed_theory \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using maximal unfolding H_maximal_consistent_def by simp
  have closed: "H_deductively_closed \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using maximal by (rule H_maximal_consistent_deductively_closed)
  have available: "Henkin_witness_axioms_available \<Gamma>
      (H_lindenbaum_extension \<Gamma> T enum)"
    using assms(4) H_lindenbaum_extension_extends
    by (rule Henkin_witness_axioms_available_mono)
  have witnessed: "Henkin_witnessed \<Gamma> (H_lindenbaum_extension \<Gamma> T enum)"
    using typed closed available by (rule H_Henkin_witnessed_from_available)
  show ?thesis
    using maximal witnessed unfolding H_Henkin_theory_def by simp
qed

theorem H_lindenbaum_extension_Henkin_theory_from_staged_witnesses:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "H_consistent \<Gamma> T"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  shows "H_Henkin_theory \<Gamma>
    (H_lindenbaum_extension \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum) formula_enum)"
proof -
  have typed_base: "typed_theory \<Gamma> (staged_henkin_extension \<Gamma> T body_enum)"
    using typed by (rule staged_henkin_extension_typed)
  have consistent_base: "H_consistent \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum)"
    using finite_T typed consistent by (rule H_staged_henkin_extension_consistent)
  have available_base: "Henkin_witness_axioms_available \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum)"
    using body_enum by (rule staged_henkin_extension_witness_axioms_available)
  show ?thesis
    using typed_base consistent_base formula_enum available_base
    by (rule H_lindenbaum_extension_Henkin_theory_from_available)
qed

theorem H_lindenbaum_extension_Henkin_theory_from_witness_axioms:
  assumes "typed_theory \<Gamma> T"
    and "H_consistent \<Gamma> (T \<union> Henkin_axioms \<Gamma> h)"
    and "enumerates_formulas \<Gamma> enum"
  shows "H_Henkin_theory \<Gamma>
    (H_lindenbaum_extension \<Gamma> (T \<union> Henkin_axioms \<Gamma> h) enum)"
proof -
  have typed_base: "typed_theory \<Gamma> (T \<union> Henkin_axioms \<Gamma> h)"
    using assms(1) typed_theory_Henkin_axioms by (rule typed_theory_Un)
  let ?E = "H_lindenbaum_extension \<Gamma> (T \<union> Henkin_axioms \<Gamma> h) enum"
  have extension: "T \<union> Henkin_axioms \<Gamma> h \<subseteq> ?E"
    by (rule H_lindenbaum_extension_extends)
  then have henkin_subset: "Henkin_axioms \<Gamma> h \<subseteq> ?E"
    by blast
  have scheme: "Henkin_scheme_in \<Gamma> ?E (\<lambda>\<sigma> A. Const (h \<sigma> A) \<sigma>)"
    using henkin_subset by (rule henkin_scheme_in_if_Henkin_axioms_subset)
  show ?thesis
    using typed_base assms(2,3) scheme
    by (rule H_lindenbaum_extension_Henkin_theory_from_scheme)
qed

theorem H_canonical_Henkin_theory_for_unprovable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>H A"
    and "enumerates_formulas \<Gamma> enum"
    and "H_Henkin_axioms_consistency_preserving \<Gamma> h"
  obtains T where "H_Henkin_theory \<Gamma> T" and "Neg A \<in> T"
proof -
  let ?Base = "{Neg A}"
  let ?T = "H_lindenbaum_extension \<Gamma> (?Base \<union> Henkin_axioms \<Gamma> h) enum"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using neg_type by (rule typed_theory_singleton)
  have consistent_base: "H_consistent \<Gamma> ?Base"
    using assms(1,2) by (rule H_consistent_singleton_neg_of_not_proves)
  have consistent_with_witnesses: "H_consistent \<Gamma> (?Base \<union> Henkin_axioms \<Gamma> h)"
    using assms(4) typed_base consistent_base
    unfolding H_Henkin_axioms_consistency_preserving_def by blast
  have henkin: "H_Henkin_theory \<Gamma> ?T"
    using typed_base consistent_with_witnesses assms(3)
    by (rule H_lindenbaum_extension_Henkin_theory_from_witness_axioms)
  have "?Base \<union> Henkin_axioms \<Gamma> h \<subseteq> ?T"
    by (rule H_lindenbaum_extension_extends)
  then have neg_in: "Neg A \<in> ?T"
    by blast
  show ?thesis
    using that henkin neg_in by blast
qed

theorem H_canonical_Henkin_theory_for_unprovable_staged:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>H A"
    and "enumerates_witness_bodies \<Gamma> body_enum"
    and "enumerates_formulas \<Gamma> formula_enum"
  obtains T where "H_Henkin_theory \<Gamma> T" and "Neg A \<in> T"
proof -
  let ?Base = "{Neg A}"
  let ?S = "staged_henkin_extension \<Gamma> ?Base body_enum"
  let ?T = "H_lindenbaum_extension \<Gamma> ?S formula_enum"
  have finite_base: "finite ?Base"
    by simp
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using neg_type by (rule typed_theory_singleton)
  have consistent_base: "H_consistent \<Gamma> ?Base"
    using assms(1,2) by (rule H_consistent_singleton_neg_of_not_proves)
  have henkin: "H_Henkin_theory \<Gamma> ?T"
    using finite_base typed_base consistent_base assms(3,4)
    by (rule H_lindenbaum_extension_Henkin_theory_from_staged_witnesses)
  have base_sub_staged: "?Base \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have staged_sub_lindenbaum: "?S \<subseteq> ?T"
    by (rule H_lindenbaum_extension_extends)
  have neg_in: "Neg A \<in> ?T"
    using base_sub_staged staged_sub_lindenbaum by auto
  show ?thesis
    using that henkin neg_in by blast
qed

theorem H_canonical_Henkin_theory_for_underivable_staged:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  obtains U where "H_Henkin_theory \<Gamma> U" and "T \<subseteq> U" and "Neg A \<in> U"
proof -
  let ?Base = "insert (Neg A) T"
  let ?S = "staged_henkin_extension \<Gamma> ?Base body_enum"
  let ?U = "H_lindenbaum_extension \<Gamma> ?S formula_enum"
  have finite_base: "finite ?Base"
    using finite_T by simp
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using typed neg_type by (rule typed_theory_insert)
  have consistent_base: "H_consistent \<Gamma> ?Base"
    using A_type not_derivable by (rule H_consistent_insert_neg_of_not_set_derivable)
  have henkin: "H_Henkin_theory \<Gamma> ?U"
    using finite_base typed_base consistent_base body_enum formula_enum
    by (rule H_lindenbaum_extension_Henkin_theory_from_staged_witnesses)
  have base_sub_staged: "?Base \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have staged_sub_lindenbaum: "?S \<subseteq> ?U"
    by (rule H_lindenbaum_extension_extends)
  have T_sub: "T \<subseteq> ?U"
    using base_sub_staged staged_sub_lindenbaum by auto
  have neg_in: "Neg A \<in> ?U"
    using base_sub_staged staged_sub_lindenbaum by auto
  show ?thesis
    using that henkin T_sub neg_in by blast
qed

theorem H_canonical_Henkin_theory_for_underivable_list_staged:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  obtains U where "H_Henkin_theory \<Gamma> U" and "set \<Delta> \<subseteq> U" and "Neg A \<in> U"
proof -
  have typed_set: "typed_theory \<Gamma> (set \<Delta>)"
    using typed_assms by (rule typed_theory_set)
  have not_set_derivable: "\<not> \<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
  proof
    assume "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
    then have "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
      by (rule H_derivable_of_set_derivable)
    then show False
      using not_derivable by blast
  qed
  have finite_set: "finite (set \<Delta>)"
    by simp
  obtain U where henkin: "H_Henkin_theory \<Gamma> U"
    and assms_sub: "set \<Delta> \<subseteq> U"
    and neg_in: "Neg A \<in> U"
    using finite_set typed_set A_type not_set_derivable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_underivable_staged)
  show ?thesis
    using that henkin assms_sub neg_in by blast
qed


subsection \<open>Set derivability and canonical theories for C\<close>

definition C_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>C\<^sub>s _" [50, 50, 50] 50) where
  "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A \<longleftrightarrow> (\<exists>\<Delta>. set \<Delta> \<subseteq> T \<and> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A)"

lemma C_derivable_mono:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and "set \<Delta> \<subseteq> set \<Delta>'"
  shows "\<Gamma> ; \<Delta>' \<turnstile>\<^sub>C A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by (intro C_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by (intro C_derivable.Theorem)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  from Derive_MP.IH(1)[OF Derive_MP.prems]
    Derive_MP.IH(2)[OF Derive_MP.prems]
  show ?case
    by (rule C_derivable.Derive_MP)
qed

lemma C_set_derivable_of_list:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
  using assms unfolding C_set_derivable_def by blast

lemma C_derivable_of_set_derivable:
  assumes "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof -
  obtain \<Sigma> where "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C A"
    and "set \<Sigma> \<subseteq> set \<Delta>"
    using assms unfolding C_set_derivable_def by blast
  then show ?thesis
    by (rule C_derivable_mono)
qed

lemma C_set_derivable_rename:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "\<Delta> ; rename r ` T \<turnstile>\<^sub>C\<^sub>s rename r A"
proof -
  obtain \<Sigma> where \<Sigma>_sub: "set \<Sigma> \<subseteq> T"
    and d: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C A"
    using assms(1) unfolding C_set_derivable_def by blast
  have d_ren: "\<Delta> ; map (rename r) \<Sigma> \<turnstile>\<^sub>C rename r A"
    using d assms(2) by (rule C_derivable_rename)
  have "set (map (rename r) \<Sigma>) \<subseteq> rename r ` T"
    using \<Sigma>_sub by auto
  then show ?thesis
    using d_ren unfolding C_set_derivable_def by blast
qed

lemma C_set_derivable_shift:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s shift A"
  unfolding shift_def
  using assms by (rule C_set_derivable_rename) auto

lemma C_set_derivable_subst_const:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>C\<^sub>s subst_const c \<sigma> N A"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> T"
    and d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms(1) unfolding C_set_derivable_def by blast
  have d_sub: "\<Gamma> ; map (subst_const c \<sigma> N) \<Delta> \<turnstile>\<^sub>C subst_const c \<sigma> N A"
    using d assms(2) by (rule C_derivable_subst_const)
  have "set (map (subst_const c \<sigma> N) \<Delta>) \<subseteq> subst_const c \<sigma> N ` T"
    using \<Delta>_sub by auto
  then show ?thesis
    using d_sub unfolding C_set_derivable_def by blast
qed

lemma C_set_derivable_subst_const_fresh_set:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "c \<notin> consts_of_set T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s subst_const c \<sigma> N A"
proof -
  have "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>C\<^sub>s subst_const c \<sigma> N A"
    using assms(1,2) by (rule C_set_derivable_subst_const)
  then show ?thesis
    using subst_const_image_fresh_set[OF assms(3), of \<sigma> N] by simp
qed

lemma C_set_derivable_abstract_const:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>C\<^sub>s abstract_const c \<sigma> A"
proof -
  have shifted: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s shift A"
    using assms by (rule C_set_derivable_shift)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have "\<sigma> # \<Gamma> ; subst_const c \<sigma> (Var 0) ` (shift ` T) \<turnstile>\<^sub>C\<^sub>s
      subst_const c \<sigma> (Var 0) (shift A)"
    using shifted var_type by (rule C_set_derivable_subst_const)
  moreover have "subst_const c \<sigma> (Var 0) ` (shift ` T) = abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  ultimately show ?thesis
    unfolding abstract_const_def by simp
qed

lemma C_set_derivable_abstract_const_fresh_set:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "c \<notin> consts_of_set T"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s abstract_const c \<sigma> A"
proof -
  have "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>C\<^sub>s abstract_const c \<sigma> A"
    using assms(1) by (rule C_set_derivable_abstract_const)
  then show ?thesis
    using abstract_const_image_fresh_set[OF assms(2), of \<sigma>] by simp
qed

lemma C_set_derivable_abstract_fresh_witness_false:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "\<sigma> # \<Gamma> ; insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)
    \<turnstile>\<^sub>C\<^sub>s ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d: "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` insert ?W T
      \<turnstile>\<^sub>C\<^sub>s abstract_const c \<sigma> ObjFalse"
    using assms(1) by (rule C_set_derivable_abstract_const)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  have image_eq: "abstract_const c \<sigma> ` insert ?W T =
      insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)"
    using abs_T abs_W by simp
  show ?thesis
    using abs_d image_eq by simp
qed

lemma C_set_Assumption:
  assumes "A \<in> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  unfolding C_set_derivable_def
  using assms by (intro exI[of _ "[A]"]) auto

lemma C_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  unfolding C_set_derivable_def
  using assms by (intro exI[of _ "[]"] C_derivable.Theorem) auto

lemma C_set_MP:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s B"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> T" and dA: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms(1) unfolding C_set_derivable_def by blast
  obtain \<Sigma> where \<Sigma>_sub: "set \<Sigma> \<subseteq> T" and dImp: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C Imp A B"
    using assms(2) unfolding C_set_derivable_def by blast
  have dA': "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>C A"
    using dA by (rule C_derivable_mono) auto
  have dImp': "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>C Imp A B"
    using dImp by (rule C_derivable_mono) auto
  have "\<Gamma> ; \<Delta> @ \<Sigma> \<turnstile>\<^sub>C B"
    using dA' dImp' by (rule C_derivable.Derive_MP)
  moreover have "set (\<Delta> @ \<Sigma>) \<subseteq> T"
    using \<Delta>_sub \<Sigma>_sub by auto
  ultimately show ?thesis
    unfolding C_set_derivable_def by blast
qed

lemma C_set_ex_falso:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
proof -
  have taut_raw: "\<Gamma> \<turnstile>\<^sub>C Imp (Neg ObjTrue) (Imp ObjTrue A)"
    using typed_ObjTrue assms(2)
    by (intro C_proves.H H_proves.PC prop_tautology_imp_of_neg_left)
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp ObjFalse (Imp ObjTrue A)"
    using taut_raw by (simp add: ObjFalse_def)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp ObjFalse (Imp ObjTrue A)"
    using taut by (rule C_set_Theorem)
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp ObjTrue A"
    using assms(1) d_taut by (rule C_set_MP)
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjTrue"
    using C_proves.H[OF H_proves_ObjTrue] by (rule C_set_Theorem)
  show ?thesis
    using d_true d_imp by (rule C_set_MP)
qed

lemma C_set_derivable_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s A"
  using assms unfolding C_set_derivable_def by blast

lemma C_set_derivable_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms C_derivable_formula unfolding C_set_derivable_def by blast

lemma C_set_derivable_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  obtains U where "finite U" and "U \<subseteq> T" and "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s A"
proof -
  obtain \<Delta> where "set \<Delta> \<subseteq> T" and "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms unfolding C_set_derivable_def by blast
  then have "finite (set \<Delta>)" "set \<Delta> \<subseteq> T" "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
    using C_set_derivable_of_list by auto
  then show ?thesis
    using that by blast
qed

lemma C_derivable_empty_imp_proves:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and "\<Delta> = []"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by simp
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have dA: "\<Gamma> \<turnstile>\<^sub>C A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have dImp: "\<Gamma> \<turnstile>\<^sub>C Imp A B"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  show ?case
    using dA dImp
    by (rule C_proves.MP)
qed

lemma C_set_derivable_empty_imp_proves:
  assumes "\<Gamma> ; {} \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
proof -
  obtain \<Delta> where \<Delta>_empty: "set \<Delta> \<subseteq> {}" and d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms unfolding C_set_derivable_def by blast
  have \<Delta>_nil: "\<Delta> = []"
    using \<Delta>_empty by (cases \<Delta>) auto
  show ?thesis
    using d \<Delta>_nil by (rule C_derivable_empty_imp_proves)
qed

lemma C_proves_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>C ObjTrue"
  by (intro C_proves.H H_proves_ObjTrue)

lemma C_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>C B"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule C_proves_formula)
  have prop_taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
    using assms(1) B_type by (rule prop_tautology_imp_of_right)
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp B (Imp A B)"
    using prop_taut by (intro C_proves.H H_proves.PC)
  show ?thesis
    using assms(2) taut by (rule C_proves.MP)
qed

lemma C_proves_imp_trans:
  assumes "\<Gamma> \<turnstile>\<^sub>C Imp A B"
    and "\<Gamma> \<turnstile>\<^sub>C Imp B C"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A C"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>C
      Imp (Imp A B) (Imp (Imp B C) (Imp A C))"
    using assms(3,4,5)
    by (intro C_proves.H H_proves.PC prop_tautology_imp_trans)
  have step: "\<Gamma> \<turnstile>\<^sub>C Imp (Imp B C) (Imp A C)"
    using assms(1) taut by (rule C_proves.MP)
  show ?thesis
    using assms(2) step by (rule C_proves.MP)
qed

lemma C_proves_cases:
  assumes "\<Gamma> \<turnstile>\<^sub>C Imp A B"
    and "\<Gamma> \<turnstile>\<^sub>C Imp (Neg A) B"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C B"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>C
      Imp (Imp A B) (Imp (Imp (Neg A) B) B)"
    using assms(3,4)
    by (intro C_proves.H H_proves.PC prop_tautology_cases)
  have step: "\<Gamma> \<turnstile>\<^sub>C Imp (Imp (Neg A) B) B"
    using assms(1) taut by (rule C_proves.MP)
  show ?thesis
    using assms(2) step by (rule C_proves.MP)
qed

lemma C_proves_exists_imp_shift_exists:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Exists \<sigma> (Imp (shift (Exists \<sigma> A)) A)"
  using assms
  by (intro C_proves.H H_proves_exists_imp_shift_exists)

lemma C_proves_imp_false_to_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Imp A ObjFalse) (Neg A)"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp ObjTrue (Imp (Imp A ObjFalse) (Neg A))"
    using assms by (intro C_proves.H H_proves.PC prop_tautology_imp_false_to_neg)
  show ?thesis
    using C_proves_ObjTrue taut by (rule C_proves.MP)
qed

lemma C_proves_imp_neg_false_to_formula:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Imp (Neg A) ObjFalse) A"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp ObjTrue (Imp (Imp (Neg A) ObjFalse) A)"
    using assms by (intro C_proves.H H_proves.PC prop_tautology_imp_neg_false_to_formula)
  show ?thesis
    using C_proves_ObjTrue taut by (rule C_proves.MP)
qed

lemma C_proves_not_exists_neg_imp_forall:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Neg (Exists \<sigma> (Neg A))) (Forall \<sigma> A)"
  using H_proves_not_exists_neg_imp_forall[OF assms]
  by (rule C_proves.H)

lemma C_proves_not_forall_imp_exists_neg:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Neg (Forall \<sigma> A)) (Exists \<sigma> (Neg A))"
  using H_proves_not_forall_imp_exists_neg[OF assms]
  by (rule C_proves.H)

lemma C_derivable_deduction_subset:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C B"
    and "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A B"
proof -
  have aux: "\<And>A \<Delta>. \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      set \<Sigma> \<subseteq> insert A (set \<Delta>) \<Longrightarrow>
      \<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A B"
    using assms(2)
  proof (induction rule: C_derivable.induct)
    case (Assumption B \<Sigma> \<Gamma>)
    then have A_type: "\<Gamma> \<turnstile> A : Prop"
      and \<Sigma>_sub: "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
      by auto
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps by simp
    show ?case
    proof (cases "B = A")
      case True
      have "\<Gamma> \<turnstile>\<^sub>C Imp A A"
        using H_imp_self[OF A_type] by (rule C_proves.H)
      then have "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A A"
        by (rule C_derivable.Theorem)
      then show ?thesis
        using True by simp
    next
      case False
      then have B_in: "B \<in> set \<Delta>"
        using Assumption.hyps \<Sigma>_sub by blast
      have dB: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C B"
        using B_in B_type by (rule C_derivable.Assumption)
      have prop_taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
        using A_type B_type by (rule prop_tautology_imp_of_right)
      have taut: "\<Gamma> \<turnstile>\<^sub>C Imp B (Imp A B)"
        using prop_taut by (intro C_proves.H H_proves.PC)
      have d_taut: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp B (Imp A B)"
        using taut by (rule C_derivable.Theorem)
      show ?thesis
        using dB d_taut by (rule C_derivable.Derive_MP)
    qed
  next
    case (Theorem \<Gamma> B \<Sigma>)
    have "\<Gamma> \<turnstile>\<^sub>C Imp A B"
      using Theorem.prems(1) Theorem.hyps by (rule C_proves_imp_of_right)
    then show ?case
      by (rule C_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> \<Sigma> B C)
    have A_type: "\<Gamma> \<turnstile> A : Prop"
      using Derive_MP.prems by simp
    have \<Sigma>_sub: "set \<Sigma> \<subseteq> insert A (set \<Delta>)"
      using Derive_MP.prems by simp
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule C_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2) by (auto dest: C_derivable_formula elim: has_type.cases)
    have prop_taut: "prop_tautology \<Gamma>
        (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
      using A_type B_type C_type by (rule prop_tautology_deduction_mp)
    have taut: "\<Gamma> \<turnstile>\<^sub>C
        Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
      using prop_taut by (intro C_proves.H H_proves.PC)
    have d_taut: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C
        Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
      using taut by (rule C_derivable.Theorem)
    have IH_B: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A B"
      using A_type \<Sigma>_sub by (rule Derive_MP.IH(1))
    have IH_imp: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A (Imp B C)"
      using A_type \<Sigma>_sub by (rule Derive_MP.IH(2))
    have step1: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C
        Imp (Imp A (Imp B C)) (Imp A C)"
      using IH_B d_taut by (rule C_derivable.Derive_MP)
    show ?case
      using IH_imp step1 by (rule C_derivable.Derive_MP)
  qed
  show ?thesis
    using assms(1,3) by (rule aux)
qed

lemma C_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; A # \<Delta> \<turnstile>\<^sub>C B"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp A B"
proof -
  have sub: "set (A # \<Delta>) \<subseteq> insert A (set \<Delta>)"
    by auto
  show ?thesis
    using assms(1) assms(2) sub by (rule C_derivable_deduction_subset)
qed

lemma C_derivable_shifted_inst:
  assumes typed_\<Delta>: "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and d: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>C Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp (Exists \<sigma> P) Q"
  using typed_\<Delta> d Q_type
proof (induction \<Delta> arbitrary: Q)
  case Nil
  have d_thm: "\<sigma> # \<Gamma> \<turnstile>\<^sub>C Imp P (shift Q)"
    using Nil.prems(2) by (rule C_derivable_empty_imp_proves) simp
  have inst: "\<Gamma> \<turnstile>\<^sub>C Imp (Exists \<sigma> P) Q"
    using P_type Nil.prems(3) d_thm by (rule C_proves.Inst)
  then show ?case
    by (rule C_derivable.Theorem)
next
  case (Cons A \<Delta>)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Cons.prems(1) by simp
  have rest_typed: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(1) by simp
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Cons.prems(3) by (rule weakening_front)
  have d_cons: "\<sigma> # \<Gamma> ; shift A # map shift \<Delta> \<turnstile>\<^sub>C
      Imp P (shift Q)"
    using Cons.prems(2) by simp
  have d_deduct: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>C
      Imp (shift A) (Imp P (shift Q))"
    using shift_A_type d_cons by (rule C_derivable_deduction)
  have taut: "\<sigma> # \<Gamma> \<turnstile>\<^sub>C
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro C_proves.H H_proves.PC prop_tautology_swap_imp)
  have d_taut: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>C
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using taut by (rule C_derivable.Theorem)
  have d_swapped_raw: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>C
      Imp P (Imp (shift A) (shift Q))"
    using d_deduct d_taut by (rule C_derivable.Derive_MP)
  have shift_imp: "shift (Imp A Q) = Imp (shift A) (shift Q)"
    by (simp add: shift_def)
  have d_swapped: "\<sigma> # \<Gamma> ; map shift \<Delta> \<turnstile>\<^sub>C
      Imp P (shift (Imp A Q))"
    using d_swapped_raw by (simp add: shift_imp)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type Cons.prems(3) by auto
  have IH: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp (Exists \<sigma> P) (Imp A Q)"
    using rest_typed d_swapped AQ_type by (rule Cons.IH)
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> P : Prop"
    using P_type by auto
  have IH_lift: "\<Gamma> ; A # \<Delta> \<turnstile>\<^sub>C
      Imp (Exists \<sigma> P) (Imp A Q)"
    using IH by (rule C_derivable_mono) auto
  have d_exists: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>C Exists \<sigma> P"
    using exists_type by (intro C_derivable.Assumption) simp
  have IH_lift': "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>C
      Imp (Exists \<sigma> P) (Imp A Q)"
    using IH_lift by (rule C_derivable_mono) auto
  have d_A: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>C A"
    using A_type by (intro C_derivable.Assumption) simp
  have d_AQ: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>C Imp A Q"
    using d_exists IH_lift' by (rule C_derivable.Derive_MP)
  have d_Q: "\<Gamma> ; Exists \<sigma> P # A # \<Delta> \<turnstile>\<^sub>C Q"
    using d_A d_AQ by (rule C_derivable.Derive_MP)
  show ?case
    using exists_type d_Q by (rule C_derivable_deduction)
qed

lemma C_set_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; insert A T \<turnstile>\<^sub>C\<^sub>s B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A B"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> insert A T"
    and dB: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C B"
    using assms(2) unfolding C_set_derivable_def by blast
  let ?\<Delta> = "removeAll A \<Delta>"
  have \<Delta>_mono: "set \<Delta> \<subseteq> set (A # ?\<Delta>)"
    by auto
  have dB': "\<Gamma> ; A # ?\<Delta> \<turnstile>\<^sub>C B"
    using dB by (rule C_derivable_mono) (use \<Delta>_mono in blast)
  have dImp: "\<Gamma> ; ?\<Delta> \<turnstile>\<^sub>C Imp A B"
    using assms(1) dB' by (rule C_derivable_deduction)
  have "set ?\<Delta> \<subseteq> T"
    using \<Delta>_sub by auto
  then show ?thesis
    unfolding C_set_derivable_def using dImp by blast
qed

lemma C_set_derivable_shifted_inst:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Exists \<sigma> P) Q"
proof -
  obtain \<Delta> where \<Delta>_sub: "set \<Delta> \<subseteq> shift ` T"
    and d\<Delta>: "\<sigma> # \<Gamma> ; \<Delta> \<turnstile>\<^sub>C Imp P (shift Q)"
    using assms(2) unfolding C_set_derivable_def by blast
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> set \<Delta>"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using \<Delta>_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  define \<Sigma> where "\<Sigma> = map pre \<Delta>"
  have \<Sigma>_sub: "set \<Sigma> \<subseteq> T"
    using pre_prop unfolding \<Sigma>_def by auto
  have map_shift_\<Sigma>: "map shift \<Sigma> = \<Delta>"
    unfolding \<Sigma>_def using pre_prop by (induction \<Delta>) auto
  have typed_\<Sigma>: "\<And>A. A \<in> set \<Sigma> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    using typed \<Sigma>_sub unfolding typed_theory_def by blast
  have d\<Sigma>: "\<sigma> # \<Gamma> ; map shift \<Sigma> \<turnstile>\<^sub>C Imp P (shift Q)"
    using d\<Delta> map_shift_\<Sigma> by simp
  have lower: "\<Gamma> ; \<Sigma> \<turnstile>\<^sub>C Imp (Exists \<sigma> P) Q"
    using typed_\<Sigma> d\<Sigma> P_type Q_type
    by (rule C_derivable_shifted_inst)
  show ?thesis
    unfolding C_set_derivable_def using \<Sigma>_sub lower by blast
qed

lemma C_set_derivable_fresh_witness_eigen_imp_false:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s
    Imp (Imp (shift (Exists \<sigma> A)) A) ObjFalse"
proof -
  let ?E = "Imp (shift (Exists \<sigma> A)) A"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(4) by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have E_type: "\<sigma> # \<Gamma> \<turnstile> ?E : Prop"
    using shifted_exists_type assms(4) by auto
  have d_false: "\<sigma> # \<Gamma> ; insert ?E (shift ` T) \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using assms(1,2,3) by (rule C_set_derivable_abstract_fresh_witness_false)
  show ?thesis
    using E_type d_false by (rule C_set_derivable_deduction)
qed

lemma C_set_derivable_fresh_witness_false:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_imp_false: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s Imp ?P ObjFalse"
    using d fresh_T fresh_A A_type
    by (rule C_set_derivable_fresh_witness_eigen_imp_false)
  have d_imp_shift_false: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>C\<^sub>s
      Imp ?P (shift ObjFalse)"
    using d_imp_false by simp
  have lower: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp ?Q ObjFalse"
    using typed d_imp_shift_false P_type typed_ObjFalse
    by (rule C_set_derivable_shifted_inst)
  have Q_thm: "\<Gamma> \<turnstile>\<^sub>C ?Q"
    using A_type by (rule C_proves_exists_imp_shift_exists)
  have d_Q: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ?Q"
    using Q_thm by (rule C_set_Theorem)
  show ?thesis
    using d_Q lower by (rule C_set_MP)
qed

definition C_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "C_consistent \<Gamma> T \<longleftrightarrow> \<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"

lemma C_consistentD:
  assumes "C_consistent \<Gamma> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  using assms unfolding C_consistent_def by blast

lemma C_consistent_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "C_consistent \<Gamma> T"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  then have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    using assms(1) by (rule C_set_ex_falso)
  then show False
    using assms(2) by blast
qed

lemma C_consistent_subset:
  assumes "C_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "C_consistent \<Gamma> T"
  using assms C_set_derivable_mono unfolding C_consistent_def by blast

lemma C_consistent_insert_fresh_witness_axiom:
  assumes typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "C_consistent \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold C_consistent_def, intro notI)
  assume d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using typed d fresh_T fresh_A A_type
    by (rule C_set_derivable_fresh_witness_false)
  then show False
    using consistent unfolding C_consistent_def by blast
qed

lemma C_consistent_add_fresh_witness_axioms:
  assumes "typed_theory \<Gamma> T"
    and "C_consistent \<Gamma> T"
    and "fresh_witness_axiom_sequence \<Gamma> T xs"
  shows "C_consistent \<Gamma> (add_witness_axioms xs T)"
  using assms
proof (induction xs arbitrary: T)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  obtain c \<sigma> A where x_def: "x = (c, \<sigma>, A)"
    by (cases x) auto
  have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Cons.prems(3) unfolding x_def by simp
  have fresh_T: "c \<notin> consts_of_set T"
    using Cons.prems(3) unfolding x_def by simp
  have fresh_A: "c \<notin> consts_of A"
    using Cons.prems(3) unfolding x_def by simp
  have tail_fresh: "fresh_witness_axiom_sequence \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) xs"
    using Cons.prems(3) unfolding x_def by simp
  have typed_insert: "typed_theory \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) A_type by (rule typed_theory_insert_henkin_witness_axiom)
  have consistent_insert: "C_consistent \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T)"
    using Cons.prems(1) Cons.prems(2) fresh_T fresh_A A_type
    by (rule C_consistent_insert_fresh_witness_axiom)
  show ?case
    using Cons.IH[OF typed_insert consistent_insert tail_fresh]
    unfolding x_def by simp
qed

lemma C_consistent_fresh_witness_extension_exists:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
    and typed_specs: "\<And>\<sigma> A. (\<sigma>, A) \<in> set specs \<Longrightarrow>
      \<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<exists>xs. fresh_witness_axiom_sequence \<Gamma> T xs \<and>
    witness_bodies xs = specs \<and>
    typed_theory \<Gamma> (add_witness_axioms xs T) \<and>
    C_consistent \<Gamma> (add_witness_axioms xs T)"
proof -
  obtain xs where fresh: "fresh_witness_axiom_sequence \<Gamma> T xs"
    and bodies: "witness_bodies xs = specs"
    using fresh_witness_axiom_sequence_exists[OF finite_T typed_specs] by blast
  have typed_ext: "typed_theory \<Gamma> (add_witness_axioms xs T)"
    using typed fresh by (rule typed_theory_add_fresh_witness_axioms)
  have consistent_ext: "C_consistent \<Gamma> (add_witness_axioms xs T)"
    using typed consistent fresh by (rule C_consistent_add_fresh_witness_axioms)
  show ?thesis
    using fresh bodies typed_ext consistent_ext by blast
qed

lemma C_staged_henkin_step_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "C_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using typed consistent fresh_T fresh_A True
      by (rule C_consistent_insert_fresh_witness_axiom)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma C_staged_henkin_chain_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(1) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(2) by (rule staged_henkin_chain_typed)
  have consistent_n: "C_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using finite_n typed_n consistent_n
    by (simp add: C_staged_henkin_step_consistent)
qed

lemma C_staged_henkin_extension_consistent:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold C_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; staged_henkin_extension \<Gamma> T enum
    \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using d_false by (rule C_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  have "\<exists>n. U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    by blast
  have "\<Gamma> ; staged_henkin_chain \<Gamma> T enum n \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule C_set_derivable_mono)
  moreover have "C_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule C_staged_henkin_chain_consistent)
  ultimately show False
    unfolding C_consistent_def by blast
qed

lemma C_consistent_singleton_neg_of_not_proves:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>C A"
  shows "C_consistent \<Gamma> {Neg A}"
proof (unfold C_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; {Neg A} \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "\<Gamma> ; {} \<turnstile>\<^sub>C\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule C_set_derivable_deduction)
  have imp_false: "\<Gamma> \<turnstile>\<^sub>C Imp (Neg A) ObjFalse"
    using d_imp_false by (rule C_set_derivable_empty_imp_proves)
  have imp_A: "\<Gamma> \<turnstile>\<^sub>C Imp (Imp (Neg A) ObjFalse) A"
    using assms(1) by (rule C_proves_imp_neg_false_to_formula)
  have "\<Gamma> \<turnstile>\<^sub>C A"
    using imp_false imp_A by (rule C_proves.MP)
  then show False
    using assms(2) by contradiction
qed

definition C_deductively_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "C_deductively_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A \<longrightarrow> A \<in> T)"

definition C_negation_complete :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "C_negation_complete \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> A \<in> T \<or> Neg A \<in> T)"

definition C_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "C_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> C_consistent \<Gamma> T \<and> C_negation_complete \<Gamma> T"

definition C_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "C_Henkin_theory \<Gamma> T \<longleftrightarrow>
    C_maximal_consistent \<Gamma> T \<and> Henkin_witnessed \<Gamma> T"

definition C_Henkin_axioms_consistency_preserving ::
    "ctx \<Rightarrow> (otype \<Rightarrow> oterm \<Rightarrow> string) \<Rightarrow> bool" where
  "C_Henkin_axioms_consistency_preserving \<Gamma> h \<longleftrightarrow>
    (\<forall>T. typed_theory \<Gamma> T \<longrightarrow> C_consistent \<Gamma> T \<longrightarrow>
      C_consistent \<Gamma> (T \<union> Henkin_axioms \<Gamma> h))"

lemma C_deductively_closedD:
  assumes "C_deductively_closed \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "A \<in> T"
proof -
  have "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule C_set_derivable_formula)
  then show ?thesis
    using assms unfolding C_deductively_closed_def by blast
qed

lemma C_contains_theorems:
  assumes "C_deductively_closed \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>C A"
  shows "A \<in> T"
proof -
  have derivable: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    using assms(2) by (rule C_set_Theorem)
  show ?thesis
    using assms(1) derivable by (rule C_deductively_closedD)
qed

lemma C_closed_under_MP:
  assumes "typed_theory \<Gamma> T"
    and "C_deductively_closed \<Gamma> T"
    and "A \<in> T"
    and "Imp A B \<in> T"
  shows "B \<in> T"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1,3) by (rule typed_theoryD)
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms(1,4) by (rule typed_theoryD)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    by (auto elim: has_type.cases)
  have dA: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    using assms(3) A_type by (rule C_set_Assumption)
  have dImp: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A B"
    using assms(4) imp_type by (rule C_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s B"
    using dA dImp by (rule C_set_MP)
  then show ?thesis
    using assms(2) B_type unfolding C_deductively_closed_def by blast
qed

lemma C_Henkin_witnessed_from_scheme:
  assumes "typed_theory \<Gamma> T"
    and "C_deductively_closed \<Gamma> T"
    and "Henkin_scheme_in \<Gamma> T W"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  have W_type: "\<Gamma> \<turnstile> W \<sigma> A : \<sigma>"
    using assms(3) A_type by (rule Henkin_scheme_inD(1))
  have imp_in: "Imp (Exists \<sigma> A) (subst0 (W \<sigma> A) A) \<in> T"
    using assms(3) A_type by (rule Henkin_scheme_inD(2))
  have subst_in: "subst0 (W \<sigma> A) A \<in> T"
    using assms(1,2) exists_in imp_in by (rule C_closed_under_MP)
  show "\<exists>V. \<Gamma> \<turnstile> V : \<sigma> \<and> subst0 V A \<in> T"
    using W_type subst_in by blast
qed

lemma C_Henkin_witnessed_from_available:
  assumes "typed_theory \<Gamma> T"
    and "C_deductively_closed \<Gamma> T"
    and "Henkin_witness_axioms_available \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where imp_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using assms(3) A_type
    unfolding Henkin_witness_axioms_available_def by blast
  have witness_type: "\<Gamma> \<turnstile> Const c \<sigma> : \<sigma>"
    by auto
  have subst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using assms(1,2) exists_in imp_in
    unfolding henkin_witness_axiom_def
    by (rule C_closed_under_MP)
  show "\<exists>V. \<Gamma> \<turnstile> V : \<sigma> \<and> subst0 V A \<in> T"
    using witness_type subst_in by blast
qed

lemma C_set_derives_ObjFalse_of_formula_and_neg:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "Neg A \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule C_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp A (Imp (Neg A) ObjFalse)"
    using A_type by (intro C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule C_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
    using assms(2) neg_type by (rule C_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule C_set_MP)
  then show ?thesis
    using d_neg by (metis C_set_MP)
qed

lemma C_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule C_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp A (Imp (Neg A) ObjFalse)"
    using A_type by (intro C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule C_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule C_set_MP)
  then show ?thesis
    using assms(2) by (metis C_set_MP)
qed

lemma C_consistent_not_both_derivable:
  assumes "C_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
  then have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A" .
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using assms(2) d_neg by (rule C_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding C_consistent_def by blast
qed

lemma C_consistent_not_derives_with_neg:
  assumes "C_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  then have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using assms(2) by (rule C_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding C_consistent_def by blast
qed

lemma C_consistent_insert_formula_if_not_neg_derivable:
  assumes "C_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
  shows "C_consistent \<Gamma> (insert A T)"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; insert A T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  then have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>C\<^sub>s ObjFalse" .
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule C_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using C_proves_imp_false_to_neg[OF assms(2)] by (rule C_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule C_set_MP)
  then show False
    using assms(3) by blast
qed

lemma C_consistent_insert_neg_if_not_derivable:
  assumes "C_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "C_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type \<open>\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>C\<^sub>s ObjFalse\<close>
    by (rule C_set_derivable_deduction)
  have d_A_thm: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Imp (Neg A) ObjFalse) A"
    using C_proves_imp_neg_false_to_formula[OF assms(2)] by (rule C_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    using d_imp_false d_A_thm by (rule C_set_MP)
  then show False
    using assms(3) by blast
qed

lemma C_consistent_insert_neg_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "C_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have consistent: "C_consistent \<Gamma> T"
    using assms by (rule C_consistent_of_not_set_derivable)
  show ?thesis
    using consistent assms by (rule C_consistent_insert_neg_if_not_derivable)
qed

lemma C_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "C_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> C_consistent \<Gamma> (insert A T)"
  shows "C_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have "\<Gamma> ; insert A T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using assms(3) unfolding C_consistent_def by blast
  then have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>C\<^sub>s ObjFalse" .
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule C_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using C_proves_imp_false_to_neg[OF assms(2)] by (rule C_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule C_set_MP)
  have not_d_A: "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  proof
    assume d_A: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
      using d_A d_neg by (rule C_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding C_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A by (rule C_consistent_insert_neg_if_not_derivable)
qed

lemma C_consistent_decidable_extension:
  assumes "C_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "C_consistent \<Gamma> (insert A T) \<or>
    C_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "C_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis by blast
next
  case False
  then have not_consistent: "\<not> C_consistent \<Gamma> (insert A T)" .
  have "C_consistent \<Gamma> (insert (Neg A) T)"
    using assms(1) assms(2) not_consistent
    by (rule C_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis by blast
qed

lemma C_maximal_consistent_deductively_closed:
  assumes "C_maximal_consistent \<Gamma> T"
  shows "C_deductively_closed \<Gamma> T"
proof (unfold C_deductively_closed_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and derivable: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  have consistent: "C_consistent \<Gamma> T"
    using assms unfolding C_maximal_consistent_def by blast
  have complete: "C_negation_complete \<Gamma> T"
    using assms unfolding C_maximal_consistent_def by blast
  show "A \<in> T"
  proof (rule ccontr)
    assume "A \<notin> T"
    then have "Neg A \<in> T"
      using complete A_type unfolding C_negation_complete_def by blast
    then have neg_in: "Neg A \<in> T" .
    have "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
      using consistent neg_in by (rule C_consistent_not_derives_with_neg)
    then show False
      using derivable by blast
  qed
qed

lemma C_maximal_neg_mem_iff:
  assumes "C_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "Neg A \<in> T \<longleftrightarrow> A \<notin> T"
proof
  assume neg_in: "Neg A \<in> T"
  show "A \<notin> T"
  proof
    assume A_in: "A \<in> T"
    have consistent: "C_consistent \<Gamma> T"
      using assms(1) unfolding C_maximal_consistent_def by blast
    have d_A: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
      using A_in assms(2) by (rule C_set_Assumption)
    have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
      using d_A neg_in by (rule C_set_derives_ObjFalse_of_formula_and_neg)
    then show False
      using consistent unfolding C_consistent_def by blast
  qed
next
  assume A_notin: "A \<notin> T"
  have complete: "C_negation_complete \<Gamma> T"
    using assms(1) unfolding C_maximal_consistent_def by blast
  then show "Neg A \<in> T"
    using A_notin assms(2) unfolding C_negation_complete_def by blast
qed

lemma C_maximal_contains_theorems:
  assumes "C_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>C A"
  shows "A \<in> T"
  using C_maximal_consistent_deductively_closed[OF assms(1)] assms(2)
  by (rule C_contains_theorems)

lemma C_Henkin_maximal_consistent:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "C_maximal_consistent \<Gamma> T"
  using assms unfolding C_Henkin_theory_def by blast

lemma C_Henkin_theory_witnessed:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
  using assms unfolding C_Henkin_theory_def by blast

lemma C_Henkin_typed_theory:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "typed_theory \<Gamma> T"
  using C_Henkin_maximal_consistent[OF assms]
  unfolding C_maximal_consistent_def by blast

lemma C_Henkin_consistent:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "C_consistent \<Gamma> T"
  using C_Henkin_maximal_consistent[OF assms]
  unfolding C_maximal_consistent_def by blast

lemma C_Henkin_negation_complete:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "C_negation_complete \<Gamma> T"
  using C_Henkin_maximal_consistent[OF assms]
  unfolding C_maximal_consistent_def by blast

lemma C_Henkin_deductively_closed:
  assumes "C_Henkin_theory \<Gamma> T"
  shows "C_deductively_closed \<Gamma> T"
  using C_Henkin_maximal_consistent[OF assms]
  by (rule C_maximal_consistent_deductively_closed)

lemma C_Henkin_contains_derivable:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "A \<in> T"
  using C_Henkin_deductively_closed[OF assms(1)] assms(2)
  by (rule C_deductively_closedD)

lemma C_Henkin_contains_theorems:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>C A"
  shows "A \<in> T"
  using C_Henkin_deductively_closed[OF assms(1)] assms(2)
  by (rule C_contains_theorems)

lemma C_Henkin_closed_under_MP:
  assumes "C_Henkin_theory \<Gamma> T"
    and "A \<in> T"
    and "Imp A B \<in> T"
  shows "B \<in> T"
  using C_Henkin_typed_theory[OF assms(1)]
    C_Henkin_deductively_closed[OF assms(1)] assms(2,3)
  by (rule C_closed_under_MP)

lemma C_maximal_imp_mem_iff:
  assumes "C_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Imp A B \<in> T \<longleftrightarrow> (A \<in> T \<longrightarrow> B \<in> T)"
proof
  assume imp_in: "Imp A B \<in> T"
  show "A \<in> T \<longrightarrow> B \<in> T"
  proof
    assume A_in: "A \<in> T"
    have typed: "typed_theory \<Gamma> T"
      using assms(1) unfolding C_maximal_consistent_def by blast
    have closed: "C_deductively_closed \<Gamma> T"
      using assms(1) by (rule C_maximal_consistent_deductively_closed)
    show "B \<in> T"
      using typed closed A_in imp_in by (rule C_closed_under_MP)
  qed
next
  assume semantic_condition: "A \<in> T \<longrightarrow> B \<in> T"
  have closed: "C_deductively_closed \<Gamma> T"
    using assms(1) by (rule C_maximal_consistent_deductively_closed)
  show "Imp A B \<in> T"
  proof (cases "A \<in> T")
    case True
    then have B_in: "B \<in> T"
      using semantic_condition by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>C Imp B (Imp A B)"
      using assms(2,3) by (intro C_proves.H H_proves.PC prop_tautology_imp_of_right)
    have "Imp B (Imp A B) \<in> T"
      using closed taut by (rule C_contains_theorems)
    then show ?thesis
    proof -
      have typed: "typed_theory \<Gamma> T"
        using assms(1) unfolding C_maximal_consistent_def by blast
      show ?thesis
        using typed closed B_in \<open>Imp B (Imp A B) \<in> T\<close>
        by (rule C_closed_under_MP)
    qed
  next
    case False
    then have neg_in: "Neg A \<in> T"
      using C_maximal_neg_mem_iff[OF assms(1,2)] by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>C Imp (Neg A) (Imp A B)"
      using assms(2,3) by (intro C_proves.H H_proves.PC prop_tautology_imp_of_neg_left)
    have "Imp (Neg A) (Imp A B) \<in> T"
      using closed taut by (rule C_contains_theorems)
    then show ?thesis
    proof -
      have typed: "typed_theory \<Gamma> T"
        using assms(1) unfolding C_maximal_consistent_def by blast
      show ?thesis
        using typed closed neg_in \<open>Imp (Neg A) (Imp A B) \<in> T\<close>
        by (rule C_closed_under_MP)
    qed
  qed
qed

lemma C_maximal_conj_mem_iff:
  assumes "C_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Conj A B \<in> T \<longleftrightarrow> A \<in> T \<and> B \<in> T"
proof
  assume conj_in: "Conj A B \<in> T"
  have closed: "C_deductively_closed \<Gamma> T"
    using assms(1) by (rule C_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding C_maximal_consistent_def by blast
  have left_taut: "\<Gamma> \<turnstile>\<^sub>C Imp (Conj A B) A"
    using assms(2,3) by (intro C_proves.H H_proves.PC prop_tautology_conj_left)
  have right_taut: "\<Gamma> \<turnstile>\<^sub>C Imp (Conj A B) B"
    using assms(2,3) by (intro C_proves.H H_proves.PC prop_tautology_conj_right)
  have left_in: "Imp (Conj A B) A \<in> T"
    using closed left_taut by (rule C_contains_theorems)
  have right_in: "Imp (Conj A B) B \<in> T"
    using closed right_taut by (rule C_contains_theorems)
  have A_in: "A \<in> T"
    using typed closed conj_in left_in by (rule C_closed_under_MP)
  have B_in: "B \<in> T"
    using typed closed conj_in right_in by (rule C_closed_under_MP)
  show "A \<in> T \<and> B \<in> T"
    using A_in B_in by blast
next
  assume both: "A \<in> T \<and> B \<in> T"
  have closed: "C_deductively_closed \<Gamma> T"
    using assms(1) by (rule C_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding C_maximal_consistent_def by blast
  have taut: "\<Gamma> \<turnstile>\<^sub>C Imp A (Imp B (Conj A B))"
    using assms(2,3) by (intro C_proves.H H_proves.PC prop_tautology_conj_intro)
  have taut_in: "Imp A (Imp B (Conj A B)) \<in> T"
    using closed taut by (rule C_contains_theorems)
  have imp_in: "Imp B (Conj A B) \<in> T"
    using typed closed conjunct1[OF both] taut_in by (rule C_closed_under_MP)
  show "Conj A B \<in> T"
    using typed closed conjunct2[OF both] imp_in by (rule C_closed_under_MP)
qed

lemma C_maximal_disj_mem_iff:
  assumes "C_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Disj A B \<in> T \<longleftrightarrow> A \<in> T \<or> B \<in> T"
proof
  assume disj_in: "Disj A B \<in> T"
  show "A \<in> T \<or> B \<in> T"
  proof (cases "A \<in> T")
    case True
    then show ?thesis
      by blast
  next
    case False
    have neg_A_in: "Neg A \<in> T"
      using C_maximal_neg_mem_iff[OF assms(1,2)] False by blast
    have closed: "C_deductively_closed \<Gamma> T"
      using assms(1) by (rule C_maximal_consistent_deductively_closed)
    have typed: "typed_theory \<Gamma> T"
      using assms(1) unfolding C_maximal_consistent_def by blast
    have taut: "\<Gamma> \<turnstile>\<^sub>C Imp (Disj A B) (Imp (Neg A) B)"
      using assms(2,3)
      by (intro C_proves.H H_proves.PC prop_tautology_disj_elim_neg_left)
    have taut_in: "Imp (Disj A B) (Imp (Neg A) B) \<in> T"
      using closed taut by (rule C_contains_theorems)
    have imp_in: "Imp (Neg A) B \<in> T"
      using typed closed disj_in taut_in by (rule C_closed_under_MP)
    have B_in: "B \<in> T"
      using typed closed neg_A_in imp_in by (rule C_closed_under_MP)
    then show ?thesis
      by blast
  qed
next
  assume disj_condition: "A \<in> T \<or> B \<in> T"
  have closed: "C_deductively_closed \<Gamma> T"
    using assms(1) by (rule C_maximal_consistent_deductively_closed)
  have typed: "typed_theory \<Gamma> T"
    using assms(1) unfolding C_maximal_consistent_def by blast
  show "Disj A B \<in> T"
  proof (rule disj_condition[THEN disjE])
    assume A_in: "A \<in> T"
    have taut: "\<Gamma> \<turnstile>\<^sub>C Imp A (Disj A B)"
      using assms(2,3)
      by (intro C_proves.H H_proves.PC prop_tautology_disj_left_intro)
    have taut_in: "Imp A (Disj A B) \<in> T"
      using closed taut by (rule C_contains_theorems)
    show ?thesis
      using typed closed A_in taut_in by (rule C_closed_under_MP)
  next
    assume B_in: "B \<in> T"
    have taut: "\<Gamma> \<turnstile>\<^sub>C Imp B (Disj A B)"
      using assms(2,3)
      by (intro C_proves.H H_proves.PC prop_tautology_disj_right_intro)
    have taut_in: "Imp B (Disj A B) \<in> T"
      using closed taut by (rule C_contains_theorems)
    show ?thesis
      using typed closed B_in taut_in by (rule C_closed_under_MP)
  qed
qed

lemma C_universal_instantiation_in:
  assumes "C_deductively_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "Forall \<sigma> A \<in> T"
  shows "subst0 W A \<in> T"
proof -
  have forall_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    using assms(2) by auto
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using assms(2,3) by (rule subst0_preserves_typing)
  have ui: "\<Gamma> \<turnstile>\<^sub>C Imp (Forall \<sigma> A) (subst0 W A)"
    using assms(2,3) by (intro C_proves.H H_proves.UI)
  have d_forall: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Forall \<sigma> A"
    using assms(4) forall_type by (rule C_set_Assumption)
  have d_ui: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Forall \<sigma> A) (subst0 W A)"
    using ui by (rule C_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s subst0 W A"
    using d_forall d_ui by (rule C_set_MP)
  then show ?thesis
    using assms(1) subst_type unfolding C_deductively_closed_def by blast
qed

lemma C_existential_generalization_in:
  assumes "C_deductively_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "subst0 W A \<in> T"
  shows "Exists \<sigma> A \<in> T"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using assms(2,3) by (rule subst0_preserves_typing)
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(2) by auto
  have eg: "\<Gamma> \<turnstile>\<^sub>C Imp (subst0 W A) (Exists \<sigma> A)"
    using assms(2,3) by (intro C_proves.H H_proves.EG)
  have d_subst: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s subst0 W A"
    using assms(4) subst_type by (rule C_set_Assumption)
  have d_eg: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (subst0 W A) (Exists \<sigma> A)"
    using eg by (rule C_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Exists \<sigma> A"
    using d_subst d_eg by (rule C_set_MP)
  then show ?thesis
    using assms(1) exists_type unfolding C_deductively_closed_def by blast
qed

lemma C_identity_refl_in:
  assumes "C_deductively_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "Eq \<sigma> M M \<in> T"
  using assms(1) C_proves.H[OF H_proves.Ref[OF assms(2)]]
  by (rule C_contains_theorems)

lemma C_identity_subst_in:
  assumes "typed_theory \<Gamma> T"
    and "C_deductively_closed \<Gamma> T"
    and "Eq \<sigma> M N \<in> T"
    and "App F M \<in> T"
    and "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "App F N \<in> T"
proof -
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using assms(5,6) by auto
  have appM_type: "\<Gamma> \<turnstile> App F M : Prop"
    using assms(5,7) by auto
  have appN_type: "\<Gamma> \<turnstile> App F N : Prop"
    using assms(6,7) by auto
  have ll: "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using assms(5,6,7) by (intro C_proves.H H_proves.LL)
  have d_eq: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Eq \<sigma> M N"
    using assms(3) eq_type by (rule C_set_Assumption)
  have d_ll: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using ll by (rule C_set_Theorem)
  have d_appM: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s App F M"
    using assms(4) appM_type by (rule C_set_Assumption)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s Imp (App F M) (App F N)"
    using d_eq d_ll by (rule C_set_MP)
  then have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s App F N"
    using d_appM by (metis C_set_MP)
  then show ?thesis
    using assms(2) appN_type unfolding C_deductively_closed_def by blast
qed

lemma C_Henkin_neg_mem_iff:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "Neg A \<in> T \<longleftrightarrow> A \<notin> T"
proof -
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2) by (rule C_maximal_neg_mem_iff)
qed

lemma C_Henkin_imp_mem_iff:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Imp A B \<in> T \<longleftrightarrow> (A \<in> T \<longrightarrow> B \<in> T)"
proof -
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule C_maximal_imp_mem_iff)
qed

lemma C_Henkin_conj_mem_iff:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Conj A B \<in> T \<longleftrightarrow> A \<in> T \<and> B \<in> T"
proof -
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule C_maximal_conj_mem_iff)
qed

lemma C_Henkin_disj_mem_iff:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "Disj A B \<in> T \<longleftrightarrow> A \<in> T \<or> B \<in> T"
proof -
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  show ?thesis
    using maximal assms(2,3) by (rule C_maximal_disj_mem_iff)
qed

lemma C_Henkin_forall_instance:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> W : \<sigma>"
    and "Forall \<sigma> A \<in> T"
  shows "subst0 W A \<in> T"
proof -
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  have closed: "C_deductively_closed \<Gamma> T"
    using maximal by (rule C_maximal_consistent_deductively_closed)
  show ?thesis
    using closed assms(2,3,4) by (rule C_universal_instantiation_in)
qed

lemma C_Henkin_forall_mem_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "Forall \<sigma> A \<in> T \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T)"
proof
  assume forall_in: "Forall \<sigma> A \<in> T"
  show "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
  proof (intro allI impI)
    fix W
    assume W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    show "subst0 W A \<in> T"
      using henkin A_type W_type forall_in
      by (rule C_Henkin_forall_instance)
  qed
next
  assume all_instances: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
  show "Forall \<sigma> A \<in> T"
  proof (rule ccontr)
    assume forall_notin: "Forall \<sigma> A \<notin> T"
    let ?F = "Forall \<sigma> A"
    let ?E = "Exists \<sigma> (Neg A)"
    have F_type: "\<Gamma> \<turnstile> ?F : Prop"
      using A_type by auto
    have neg_A_type: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop"
      using A_type by auto
    have not_F_in: "Neg ?F \<in> T"
      using C_Henkin_neg_mem_iff[OF henkin F_type] forall_notin by blast
    have imp_theorem: "\<Gamma> \<turnstile>\<^sub>C Imp (Neg ?F) ?E"
      using A_type by (rule C_proves_not_forall_imp_exists_neg)
    have imp_in: "Imp (Neg ?F) ?E \<in> T"
      using henkin imp_theorem by (rule C_Henkin_contains_theorems)
    have exists_in: "?E \<in> T"
      using henkin not_F_in imp_in by (rule C_Henkin_closed_under_MP)
    have witnessed: "Henkin_witnessed \<Gamma> T"
      using henkin unfolding C_Henkin_theory_def by blast
    obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
      and neg_inst_in: "subst0 W (Neg A) \<in> T"
      using witnessed neg_A_type exists_in
      unfolding Henkin_witnessed_def by blast
    have inst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
      using A_type W_type by (rule subst0_preserves_typing)
    have inst_in: "subst0 W A \<in> T"
      using all_instances W_type by blast
    have "Neg (subst0 W A) \<in> T"
      using neg_inst_in by (simp add: subst0_def)
    then have "subst0 W A \<notin> T"
      using C_Henkin_neg_mem_iff[OF henkin inst_type] by blast
    then show False
      using inst_in by blast
  qed
qed

lemma C_Henkin_exists_mem_iff:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "Exists \<sigma> A \<in> T \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T)"
proof
  assume exists_in: "Exists \<sigma> A \<in> T"
  have witnessed: "Henkin_witnessed \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  then show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using assms(2) exists_in unfolding Henkin_witnessed_def by blast
next
  assume "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
  then obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_in: "subst0 W A \<in> T"
    by blast
  have maximal: "C_maximal_consistent \<Gamma> T"
    using assms(1) unfolding C_Henkin_theory_def by blast
  have closed: "C_deductively_closed \<Gamma> T"
    using maximal by (rule C_maximal_consistent_deductively_closed)
  show "Exists \<sigma> A \<in> T"
    using closed assms(2) W_type subst_in
    by (rule C_existential_generalization_in)
qed

lemma C_Henkin_exists_witness:
  assumes "C_Henkin_theory \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "Exists \<sigma> A \<in> T"
  obtains W where "\<Gamma> \<turnstile> W : \<sigma>" and "subst0 W A \<in> T"
  using C_Henkin_exists_mem_iff[OF assms(1,2)] assms(3) by blast

definition C_lindenbaum_step :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "C_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if C_consistent \<Gamma> (insert A T) then insert A T else insert (Neg A) T)
     else T)"

primrec C_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "C_lindenbaum_chain \<Gamma> T enum 0 = T"
| "C_lindenbaum_chain \<Gamma> T enum (Suc n) =
    C_lindenbaum_step \<Gamma> (enum n) (C_lindenbaum_chain \<Gamma> T enum n)"

definition C_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "C_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. C_lindenbaum_chain \<Gamma> T enum n)"

lemma C_lindenbaum_step_extends:
  "T \<subseteq> C_lindenbaum_step \<Gamma> A T"
  unfolding C_lindenbaum_step_def by auto

lemma C_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (C_lindenbaum_step \<Gamma> A T)"
  using assms unfolding C_lindenbaum_step_def typed_theory_def by auto

lemma C_lindenbaum_step_consistent:
  assumes "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (C_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding C_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "C_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> unfolding C_lindenbaum_step_def by simp
  next
    case False
    have "C_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule C_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False unfolding C_lindenbaum_step_def by simp
  qed
qed

lemma C_lindenbaum_chain_step:
  "C_lindenbaum_chain \<Gamma> T enum n \<subseteq> C_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using C_lindenbaum_step_extends[of
      "C_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma C_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (C_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: C_lindenbaum_step_typed)
qed

lemma C_lindenbaum_chain_consistent:
  assumes "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (C_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: C_lindenbaum_step_consistent)
qed

lemma C_lindenbaum_extension_extends:
  "T \<subseteq> C_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> C_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> C_lindenbaum_extension \<Gamma> T enum"
    unfolding C_lindenbaum_extension_def by blast
qed

lemma C_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (C_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule C_lindenbaum_chain_typed)
  then show ?thesis
    unfolding C_lindenbaum_extension_def by (rule typed_theory_nat_union)
qed

lemma C_lindenbaum_extension_consistent:
  assumes "C_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof (unfold C_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; C_lindenbaum_extension \<Gamma> T enum \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> C_lindenbaum_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using d_false by (rule C_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. C_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding C_lindenbaum_extension_def .
  have step: "\<And>n. C_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      C_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule C_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> C_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  obtain n where U_sub_chain: "U \<subseteq> C_lindenbaum_chain \<Gamma> T enum n"
    using \<open>\<exists>n. U \<subseteq> C_lindenbaum_chain \<Gamma> T enum n\<close> by (elim exE)
  have "\<Gamma> ; C_lindenbaum_chain \<Gamma> T enum n \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule C_set_derivable_mono)
  moreover have "C_consistent \<Gamma> (C_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule C_lindenbaum_chain_consistent)
  ultimately show False
    unfolding C_consistent_def by contradiction
qed

lemma C_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "C_negation_complete \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof (unfold C_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "C_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "C_lindenbaum_chain \<Gamma> T enum (Suc n) =
      C_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> C_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> C_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "C_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> C_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding C_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> C_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding C_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> C_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> C_lindenbaum_extension \<Gamma> T enum"
  proof
    assume A_in_chain: "A \<in> C_lindenbaum_chain \<Gamma> T enum (Suc n)"
    have chain_in_range:
      "C_lindenbaum_chain \<Gamma> T enum (Suc n) \<in> range (C_lindenbaum_chain \<Gamma> T enum)"
      by (rule rangeI)
    then have "A \<in> C_lindenbaum_extension \<Gamma> T enum"
      unfolding C_lindenbaum_extension_def
      using A_in_chain by (rule UnionI)
    then show ?thesis
      by (rule disjI1)
  next
    assume neg_in_chain: "Neg A \<in> C_lindenbaum_chain \<Gamma> T enum (Suc n)"
    have chain_in_range:
      "C_lindenbaum_chain \<Gamma> T enum (Suc n) \<in> range (C_lindenbaum_chain \<Gamma> T enum)"
      by (rule rangeI)
    then have "Neg A \<in> C_lindenbaum_extension \<Gamma> T enum"
      unfolding C_lindenbaum_extension_def
      using neg_in_chain by (rule UnionI)
    then show ?thesis
      by (rule disjI2)
  qed
qed

theorem C_lindenbaum_extension_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "C_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "C_maximal_consistent \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule C_lindenbaum_extension_typed)
  have consistent: "C_consistent \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule C_lindenbaum_extension_consistent)
  have complete: "C_negation_complete \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule C_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete unfolding C_maximal_consistent_def by simp
qed

theorem C_lindenbaum_extension_Henkin_theory_from_scheme:
  assumes "typed_theory \<Gamma> T"
    and "C_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
    and "Henkin_scheme_in \<Gamma> (C_lindenbaum_extension \<Gamma> T enum) W"
  shows "C_Henkin_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof -
  have maximal: "C_maximal_consistent \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(1,2,3) by (rule C_lindenbaum_extension_maximal_consistent)
  have typed: "typed_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using maximal unfolding C_maximal_consistent_def by simp
  have closed: "C_deductively_closed \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using maximal by (rule C_maximal_consistent_deductively_closed)
  have witnessed: "Henkin_witnessed \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using typed closed assms(4) by (rule C_Henkin_witnessed_from_scheme)
  show ?thesis
    using maximal witnessed unfolding C_Henkin_theory_def by simp
qed

theorem C_lindenbaum_extension_Henkin_theory_from_available:
  assumes "typed_theory \<Gamma> T"
    and "C_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
    and "Henkin_witness_axioms_available \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
proof -
  have maximal: "C_maximal_consistent \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(1,2,3) by (rule C_lindenbaum_extension_maximal_consistent)
  have typed: "typed_theory \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using maximal unfolding C_maximal_consistent_def by simp
  have closed: "C_deductively_closed \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using maximal by (rule C_maximal_consistent_deductively_closed)
  have available: "Henkin_witness_axioms_available \<Gamma>
      (C_lindenbaum_extension \<Gamma> T enum)"
    using assms(4) C_lindenbaum_extension_extends
    by (rule Henkin_witness_axioms_available_mono)
  have witnessed: "Henkin_witnessed \<Gamma> (C_lindenbaum_extension \<Gamma> T enum)"
    using typed closed available by (rule C_Henkin_witnessed_from_available)
  show ?thesis
    using maximal witnessed unfolding C_Henkin_theory_def by simp
qed

theorem C_lindenbaum_extension_Henkin_theory_from_staged_witnesses:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "C_consistent \<Gamma> T"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  shows "C_Henkin_theory \<Gamma>
    (C_lindenbaum_extension \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum) formula_enum)"
proof -
  have typed_base: "typed_theory \<Gamma> (staged_henkin_extension \<Gamma> T body_enum)"
    using typed by (rule staged_henkin_extension_typed)
  have consistent_base: "C_consistent \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum)"
    using finite_T typed consistent by (rule C_staged_henkin_extension_consistent)
  have available_base: "Henkin_witness_axioms_available \<Gamma>
      (staged_henkin_extension \<Gamma> T body_enum)"
    using body_enum by (rule staged_henkin_extension_witness_axioms_available)
  show ?thesis
    using typed_base consistent_base formula_enum available_base
    by (rule C_lindenbaum_extension_Henkin_theory_from_available)
qed

theorem C_lindenbaum_extension_Henkin_theory_from_witness_axioms:
  assumes "typed_theory \<Gamma> T"
    and "C_consistent \<Gamma> (T \<union> Henkin_axioms \<Gamma> h)"
    and "enumerates_formulas \<Gamma> enum"
  shows "C_Henkin_theory \<Gamma>
    (C_lindenbaum_extension \<Gamma> (T \<union> Henkin_axioms \<Gamma> h) enum)"
proof -
  have typed_base: "typed_theory \<Gamma> (T \<union> Henkin_axioms \<Gamma> h)"
    using assms(1) typed_theory_Henkin_axioms by (rule typed_theory_Un)
  let ?E = "C_lindenbaum_extension \<Gamma> (T \<union> Henkin_axioms \<Gamma> h) enum"
  have extension: "T \<union> Henkin_axioms \<Gamma> h \<subseteq> ?E"
    by (rule C_lindenbaum_extension_extends)
  then have henkin_subset: "Henkin_axioms \<Gamma> h \<subseteq> ?E"
    by blast
  have scheme: "Henkin_scheme_in \<Gamma> ?E (\<lambda>\<sigma> A. Const (h \<sigma> A) \<sigma>)"
    using henkin_subset by (rule henkin_scheme_in_if_Henkin_axioms_subset)
  show ?thesis
    using typed_base assms(2,3) scheme
    by (rule C_lindenbaum_extension_Henkin_theory_from_scheme)
qed

theorem C_canonical_Henkin_theory_for_unprovable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>C A"
    and "enumerates_formulas \<Gamma> enum"
    and "C_Henkin_axioms_consistency_preserving \<Gamma> h"
  obtains T where "C_Henkin_theory \<Gamma> T" and "Neg A \<in> T"
proof -
  let ?Base = "{Neg A}"
  let ?T = "C_lindenbaum_extension \<Gamma> (?Base \<union> Henkin_axioms \<Gamma> h) enum"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using neg_type by (rule typed_theory_singleton)
  have consistent_base: "C_consistent \<Gamma> ?Base"
    using assms(1,2) by (rule C_consistent_singleton_neg_of_not_proves)
  have consistent_with_witnesses: "C_consistent \<Gamma> (?Base \<union> Henkin_axioms \<Gamma> h)"
    using assms(4) typed_base consistent_base
    unfolding C_Henkin_axioms_consistency_preserving_def by blast
  have henkin: "C_Henkin_theory \<Gamma> ?T"
    using typed_base consistent_with_witnesses assms(3)
    by (rule C_lindenbaum_extension_Henkin_theory_from_witness_axioms)
  have "?Base \<union> Henkin_axioms \<Gamma> h \<subseteq> ?T"
    by (rule C_lindenbaum_extension_extends)
  then have neg_in: "Neg A \<in> ?T"
    by blast
  show ?thesis
    using that henkin neg_in by blast
qed

theorem C_canonical_Henkin_theory_for_unprovable_staged:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>C A"
    and "enumerates_witness_bodies \<Gamma> body_enum"
    and "enumerates_formulas \<Gamma> formula_enum"
  obtains T where "C_Henkin_theory \<Gamma> T" and "Neg A \<in> T"
proof -
  let ?Base = "{Neg A}"
  let ?S = "staged_henkin_extension \<Gamma> ?Base body_enum"
  let ?T = "C_lindenbaum_extension \<Gamma> ?S formula_enum"
  have finite_base: "finite ?Base"
    by simp
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using neg_type by (rule typed_theory_singleton)
  have consistent_base: "C_consistent \<Gamma> ?Base"
    using assms(1,2) by (rule C_consistent_singleton_neg_of_not_proves)
  have henkin: "C_Henkin_theory \<Gamma> ?T"
    using finite_base typed_base consistent_base assms(3,4)
    by (rule C_lindenbaum_extension_Henkin_theory_from_staged_witnesses)
  have base_sub_staged: "?Base \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have staged_sub_lindenbaum: "?S \<subseteq> ?T"
    by (rule C_lindenbaum_extension_extends)
  have neg_in: "Neg A \<in> ?T"
    using base_sub_staged staged_sub_lindenbaum by auto
  show ?thesis
    using that henkin neg_in by blast
qed

theorem C_canonical_Henkin_theory_for_underivable_staged:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  obtains U where "C_Henkin_theory \<Gamma> U" and "T \<subseteq> U" and "Neg A \<in> U"
proof -
  let ?Base = "insert (Neg A) T"
  let ?S = "staged_henkin_extension \<Gamma> ?Base body_enum"
  let ?U = "C_lindenbaum_extension \<Gamma> ?S formula_enum"
  have finite_base: "finite ?Base"
    using finite_T by simp
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have typed_base: "typed_theory \<Gamma> ?Base"
    using typed neg_type by (rule typed_theory_insert)
  have consistent_base: "C_consistent \<Gamma> ?Base"
    using A_type not_derivable by (rule C_consistent_insert_neg_of_not_set_derivable)
  have henkin: "C_Henkin_theory \<Gamma> ?U"
    using finite_base typed_base consistent_base body_enum formula_enum
    by (rule C_lindenbaum_extension_Henkin_theory_from_staged_witnesses)
  have base_sub_staged: "?Base \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have staged_sub_lindenbaum: "?S \<subseteq> ?U"
    by (rule C_lindenbaum_extension_extends)
  have T_sub: "T \<subseteq> ?U"
    using base_sub_staged staged_sub_lindenbaum by auto
  have neg_in: "Neg A \<in> ?U"
    using base_sub_staged staged_sub_lindenbaum by auto
  show ?thesis
    using that henkin T_sub neg_in by blast
qed

theorem C_canonical_Henkin_theory_for_underivable_list_staged:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    and body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enum: "enumerates_formulas \<Gamma> formula_enum"
  obtains U where "C_Henkin_theory \<Gamma> U" and "set \<Delta> \<subseteq> U" and "Neg A \<in> U"
proof -
  have typed_set: "typed_theory \<Gamma> (set \<Delta>)"
    using typed_assms by (rule typed_theory_set)
  have not_set_derivable: "\<not> \<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
  proof
    assume "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
    then have "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
      by (rule C_derivable_of_set_derivable)
    then show False
      using not_derivable by blast
  qed
  have finite_set: "finite (set \<Delta>)"
    by simp
  obtain U where henkin: "C_Henkin_theory \<Gamma> U"
    and assms_sub: "set \<Delta> \<subseteq> U"
    and neg_in: "Neg A \<in> U"
    using finite_set typed_set A_type not_set_derivable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_underivable_staged)
  show ?thesis
    using that henkin assms_sub neg_in by blast
qed

section \<open>Syntactic canonical truth clauses\<close>

text \<open>
  The semantic truth lemma will eventually identify model-theoretic truth with
  membership in a canonical Henkin theory.  The following definitions and
  lemmas isolate the purely syntactic half of that argument: once a maximal
  Henkin theory is fixed, membership already has the expected Boolean,
  existential, equality, and conversion behavior.
\<close>

definition H_canonical_truth :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_canonical_truth \<Gamma> T A \<longleftrightarrow>
    H_Henkin_theory \<Gamma> T \<and> \<Gamma> \<turnstile> A : Prop \<and> A \<in> T"

definition C_canonical_truth :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_canonical_truth \<Gamma> T A \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> \<Gamma> \<turnstile> A : Prop \<and> A \<in> T"

lemma H_canonical_truth_mem:
  assumes "H_canonical_truth \<Gamma> T A"
  shows "A \<in> T"
  using assms unfolding H_canonical_truth_def by blast

lemma C_canonical_truth_mem:
  assumes "C_canonical_truth \<Gamma> T A"
  shows "A \<in> T"
  using assms unfolding C_canonical_truth_def by blast

definition H_subst_truth ::
    "ctx \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> oterm env \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_subst_truth \<Delta> \<Gamma> T s A \<longleftrightarrow>
    H_Henkin_theory \<Gamma> T \<and> term_subst_typed \<Delta> \<Gamma> s \<and>
    \<Delta> \<turnstile> A : Prop \<and> H_canonical_truth \<Gamma> T (subst s A)"

definition C_subst_truth ::
    "ctx \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> oterm env \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_subst_truth \<Delta> \<Gamma> T s A \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> term_subst_typed \<Delta> \<Gamma> s \<and>
    \<Delta> \<turnstile> A : Prop \<and> C_canonical_truth \<Gamma> T (subst s A)"

lemma H_subst_truth_identity:
  assumes "H_canonical_truth \<Gamma> T A"
  shows "H_subst_truth \<Gamma> \<Gamma> T Var A"
  using assms term_subst_typed_Var
  unfolding H_subst_truth_def H_canonical_truth_def by simp

lemma C_subst_truth_identity:
  assumes "C_canonical_truth \<Gamma> T A"
  shows "C_subst_truth \<Gamma> \<Gamma> T Var A"
  using assms term_subst_typed_Var
  unfolding C_subst_truth_def C_canonical_truth_def by simp

lemma H_subst_truth_identity_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "H_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow>
    H_canonical_truth \<Gamma> T A"
  using henkin A_type term_subst_typed_Var
  unfolding H_subst_truth_def H_canonical_truth_def by auto

lemma C_subst_truth_identity_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "C_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow>
    C_canonical_truth \<Gamma> T A"
  using henkin A_type term_subst_typed_Var
  unfolding C_subst_truth_def C_canonical_truth_def by auto

lemma H_subst_truth_identity_mem_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "H_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow> A \<in> T"
  using H_subst_truth_identity_iff[OF henkin A_type] henkin A_type
  unfolding H_canonical_truth_def by auto

lemma C_subst_truth_identity_mem_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "C_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow> A \<in> T"
  using C_subst_truth_identity_iff[OF henkin A_type] henkin A_type
  unfolding C_canonical_truth_def by auto

lemma H_canonical_truth_neg_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "H_canonical_truth \<Gamma> T (Neg A) \<longleftrightarrow>
    \<not> H_canonical_truth \<Gamma> T A"
  using henkin A_type H_Henkin_neg_mem_iff[OF henkin A_type]
  unfolding H_canonical_truth_def by auto

lemma H_canonical_truth_imp_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "H_canonical_truth \<Gamma> T (Imp A B) \<longleftrightarrow>
    (H_canonical_truth \<Gamma> T A \<longrightarrow> H_canonical_truth \<Gamma> T B)"
  using henkin A_type B_type H_Henkin_imp_mem_iff[OF henkin A_type B_type]
  unfolding H_canonical_truth_def by auto

lemma H_canonical_truth_conj_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "H_canonical_truth \<Gamma> T (Conj A B) \<longleftrightarrow>
    H_canonical_truth \<Gamma> T A \<and> H_canonical_truth \<Gamma> T B"
  using henkin A_type B_type H_Henkin_conj_mem_iff[OF henkin A_type B_type]
  unfolding H_canonical_truth_def by auto

lemma H_canonical_truth_disj_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "H_canonical_truth \<Gamma> T (Disj A B) \<longleftrightarrow>
    H_canonical_truth \<Gamma> T A \<or> H_canonical_truth \<Gamma> T B"
  using henkin A_type B_type H_Henkin_disj_mem_iff[OF henkin A_type B_type]
  unfolding H_canonical_truth_def by auto

lemma H_canonical_truth_forall_instance:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and truth: "H_canonical_truth \<Gamma> T (Forall \<sigma> A)"
  shows "H_canonical_truth \<Gamma> T (subst0 W A)"
proof -
  have forall_in: "Forall \<sigma> A \<in> T"
    using truth unfolding H_canonical_truth_def by blast
  have subst_in: "subst0 W A \<in> T"
    using henkin A_type W_type forall_in
    by (rule H_Henkin_forall_instance)
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  show ?thesis
    using henkin subst_type subst_in
    unfolding H_canonical_truth_def by blast
qed

lemma H_canonical_truth_forall_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "H_canonical_truth \<Gamma> T (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> H_canonical_truth \<Gamma> T (subst0 W A))"
proof
  assume truth: "H_canonical_truth \<Gamma> T (Forall \<sigma> A)"
  show "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> H_canonical_truth \<Gamma> T (subst0 W A)"
    using H_canonical_truth_forall_instance[OF henkin A_type _ truth] by blast
next
  assume all_truth: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> H_canonical_truth \<Gamma> T (subst0 W A)"
  have all_mem: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
    using all_truth H_canonical_truth_mem by blast
  have forall_in: "Forall \<sigma> A \<in> T"
    using H_Henkin_forall_mem_iff[OF henkin A_type] all_mem by blast
  show "H_canonical_truth \<Gamma> T (Forall \<sigma> A)"
    using henkin A_type forall_in
    unfolding H_canonical_truth_def by auto
qed

lemma H_canonical_truth_exists_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "H_canonical_truth \<Gamma> T (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> H_canonical_truth \<Gamma> T (subst0 W A))"
proof
  assume truth: "H_canonical_truth \<Gamma> T (Exists \<sigma> A)"
  then have exists_in: "Exists \<sigma> A \<in> T"
    unfolding H_canonical_truth_def by blast
  obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_in: "subst0 W A \<in> T"
    using H_Henkin_exists_witness[OF henkin A_type exists_in] by blast
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> H_canonical_truth \<Gamma> T (subst0 W A)"
    using W_type henkin subst_type subst_in
    unfolding H_canonical_truth_def by blast
next
  assume "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> H_canonical_truth \<Gamma> T (subst0 W A)"
  then obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_truth: "H_canonical_truth \<Gamma> T (subst0 W A)"
    by blast
  have subst_in: "subst0 W A \<in> T"
    using subst_truth by (rule H_canonical_truth_mem)
  have exists_in: "Exists \<sigma> A \<in> T"
    using H_Henkin_exists_mem_iff[OF henkin A_type] W_type subst_in by blast
  show "H_canonical_truth \<Gamma> T (Exists \<sigma> A)"
    using henkin A_type exists_in
    unfolding H_canonical_truth_def by auto
qed

lemma H_canonical_truth_refl:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "H_canonical_truth \<Gamma> T (Eq \<sigma> M M)"
proof -
  have closed: "H_deductively_closed \<Gamma> T"
    using henkin by (rule H_Henkin_deductively_closed)
  have eq_in: "Eq \<sigma> M M \<in> T"
    using closed M_type by (rule H_identity_refl_in)
  show ?thesis
    using henkin M_type eq_in
    unfolding H_canonical_truth_def by auto
qed

lemma H_canonical_truth_leibniz:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and eq_truth: "H_canonical_truth \<Gamma> T (Eq \<sigma> M N)"
    and app_truth: "H_canonical_truth \<Gamma> T (App F M)"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "H_canonical_truth \<Gamma> T (App F N)"
proof -
  have typed: "typed_theory \<Gamma> T"
    using henkin by (rule H_Henkin_typed_theory)
  have closed: "H_deductively_closed \<Gamma> T"
    using henkin by (rule H_Henkin_deductively_closed)
  have eq_in: "Eq \<sigma> M N \<in> T"
    using eq_truth by (rule H_canonical_truth_mem)
  have appM_in: "App F M \<in> T"
    using app_truth by (rule H_canonical_truth_mem)
  have appN_in: "App F N \<in> T"
    using typed closed eq_in appM_in M_type N_type F_type
    by (rule H_identity_subst_in)
  have appN_type: "\<Gamma> \<turnstile> App F N : Prop"
    using F_type N_type by auto
  show ?thesis
    using henkin appN_type appN_in
    unfolding H_canonical_truth_def by blast
qed

lemma H_canonical_truth_beta_eta_imp:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and equiv: "beta_eta_equiv \<Gamma> Prop A B"
    and truth: "H_canonical_truth \<Gamma> T A"
  shows "H_canonical_truth \<Gamma> T B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using equiv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using equiv by (rule beta_eta_equiv_right_type)
  have AB_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using A_type B_type by auto
  have BA_type: "\<Gamma> \<turnstile> Imp B A : Prop"
    using A_type B_type by auto
  have closed: "H_deductively_closed \<Gamma> T"
    using henkin by (rule H_Henkin_deductively_closed)
  have bicond_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
    using closed equiv by (rule H_beta_eta_equiv_in)
  have imp_in: "Imp A B \<in> T"
    using H_Henkin_conj_mem_iff[OF henkin AB_type BA_type] bicond_in by blast
  have A_in: "A \<in> T"
    using truth by (rule H_canonical_truth_mem)
  have B_in: "B \<in> T"
    using henkin A_in imp_in by (rule H_Henkin_closed_under_MP)
  show ?thesis
    using henkin B_type B_in
    unfolding H_canonical_truth_def by blast
qed

lemma H_canonical_truth_beta_eta_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and equiv: "beta_eta_equiv \<Gamma> Prop A B"
  shows "H_canonical_truth \<Gamma> T A \<longleftrightarrow> H_canonical_truth \<Gamma> T B"
  using H_canonical_truth_beta_eta_imp[OF henkin equiv]
    H_canonical_truth_beta_eta_imp[OF henkin beta_eta_equiv.Sym[OF equiv]]
  by blast

lemma H_subst_truth_neg_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Neg A) \<longleftrightarrow>
    \<not> H_subst_truth \<Delta> \<Gamma> T s A"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type subst_type
      H_canonical_truth_neg_iff[OF henkin subst_type]
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_imp_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Imp A B) \<longleftrightarrow>
    (H_subst_truth \<Delta> \<Gamma> T s A \<longrightarrow> H_subst_truth \<Delta> \<Gamma> T s B)"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      H_canonical_truth_imp_iff[OF henkin subst_A_type subst_B_type]
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_conj_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Conj A B) \<longleftrightarrow>
    H_subst_truth \<Delta> \<Gamma> T s A \<and> H_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      H_canonical_truth_conj_iff[OF henkin subst_A_type subst_B_type]
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_disj_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Disj A B) \<longleftrightarrow>
    H_subst_truth \<Delta> \<Gamma> T s A \<or> H_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      H_canonical_truth_disj_iff[OF henkin subst_A_type subst_B_type]
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_forall_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow>
      H_subst_truth (\<sigma> # \<Delta>) \<Gamma> T (case_nat W s) A)"
proof -
  have lift_typed: "term_subst_typed (\<sigma> # \<Delta>) (\<sigma> # \<Gamma>) (lift_subst s)"
    using s_typed by (rule term_subst_typed_lift)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> subst (lift_subst s) A : Prop"
    using A_type lift_typed by (rule term_subst_preserves_typing)
  have canon: "H_canonical_truth \<Gamma> T
      (Forall \<sigma> (subst (lift_subst s) A)) \<longleftrightarrow>
      (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow>
        H_canonical_truth \<Gamma> T (subst0 W (subst (lift_subst s) A)))"
    using H_canonical_truth_forall_iff[OF henkin body_type] .
  show ?thesis
    using henkin s_typed A_type canon
    unfolding H_subst_truth_def
    by (auto simp: subst0_subst_lift intro: term_subst_typed_extend)
qed

lemma H_subst_truth_exists_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and>
      H_subst_truth (\<sigma> # \<Delta>) \<Gamma> T (case_nat W s) A)"
proof -
  have lift_typed: "term_subst_typed (\<sigma> # \<Delta>) (\<sigma> # \<Gamma>) (lift_subst s)"
    using s_typed by (rule term_subst_typed_lift)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> subst (lift_subst s) A : Prop"
    using A_type lift_typed by (rule term_subst_preserves_typing)
  have canon: "H_canonical_truth \<Gamma> T
      (Exists \<sigma> (subst (lift_subst s) A)) \<longleftrightarrow>
      (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and>
        H_canonical_truth \<Gamma> T (subst0 W (subst (lift_subst s) A)))"
    using H_canonical_truth_exists_iff[OF henkin body_type] .
  show ?thesis
    using henkin s_typed A_type canon
    unfolding H_subst_truth_def
    by (auto simp: subst0_subst_lift intro: term_subst_typed_extend)
qed

lemma H_subst_truth_refl:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
  shows "H_subst_truth \<Delta> \<Gamma> T s (Eq \<sigma> M M)"
proof -
  have subst_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have truth: "H_canonical_truth \<Gamma> T
      (Eq \<sigma> (subst s M) (subst s M))"
    using henkin subst_M_type by (rule H_canonical_truth_refl)
  show ?thesis
    using henkin s_typed M_type truth
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_leibniz:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and eq_truth: "H_subst_truth \<Delta> \<Gamma> T s (Eq \<sigma> M N)"
    and app_truth: "H_subst_truth \<Delta> \<Gamma> T s (App F M)"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and F_type: "\<Delta> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "H_subst_truth \<Delta> \<Gamma> T s (App F N)"
proof -
  have subst_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have subst_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have subst_F_type: "\<Gamma> \<turnstile> subst s F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using F_type s_typed by (rule term_subst_preserves_typing)
  have eq_canon: "H_canonical_truth \<Gamma> T
      (Eq \<sigma> (subst s M) (subst s N))"
    using eq_truth unfolding H_subst_truth_def by auto
  have app_canon: "H_canonical_truth \<Gamma> T (App (subst s F) (subst s M))"
    using app_truth unfolding H_subst_truth_def by auto
  have canon: "H_canonical_truth \<Gamma> T (App (subst s F) (subst s N))"
    using henkin eq_canon app_canon subst_M_type subst_N_type subst_F_type
    by (rule H_canonical_truth_leibniz)
  have appN_type: "\<Delta> \<turnstile> App F N : Prop"
    using F_type N_type by auto
  show ?thesis
    using henkin s_typed appN_type canon
    unfolding H_subst_truth_def by auto
qed

lemma H_subst_truth_beta_eta_iff:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and equiv: "beta_eta_equiv \<Delta> Prop A B"
  shows "H_subst_truth \<Delta> \<Gamma> T s A \<longleftrightarrow>
    H_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have A_type: "\<Delta> \<turnstile> A : Prop"
    using equiv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Delta> \<turnstile> B : Prop"
    using equiv by (rule beta_eta_equiv_right_type)
  have subst_equiv: "beta_eta_equiv \<Gamma> Prop (subst s A) (subst s B)"
    using s_typed by (rule beta_eta_equiv_subst[OF equiv])
  show ?thesis
    using henkin s_typed A_type B_type
      H_canonical_truth_beta_eta_iff[OF henkin subst_equiv]
    unfolding H_subst_truth_def by auto
qed

lemma C_canonical_truth_neg_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "C_canonical_truth \<Gamma> T (Neg A) \<longleftrightarrow>
    \<not> C_canonical_truth \<Gamma> T A"
  using henkin A_type C_Henkin_neg_mem_iff[OF henkin A_type]
  unfolding C_canonical_truth_def by auto

lemma C_canonical_truth_imp_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "C_canonical_truth \<Gamma> T (Imp A B) \<longleftrightarrow>
    (C_canonical_truth \<Gamma> T A \<longrightarrow> C_canonical_truth \<Gamma> T B)"
  using henkin A_type B_type C_Henkin_imp_mem_iff[OF henkin A_type B_type]
  unfolding C_canonical_truth_def by auto

lemma C_canonical_truth_conj_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "C_canonical_truth \<Gamma> T (Conj A B) \<longleftrightarrow>
    C_canonical_truth \<Gamma> T A \<and> C_canonical_truth \<Gamma> T B"
  using henkin A_type B_type C_Henkin_conj_mem_iff[OF henkin A_type B_type]
  unfolding C_canonical_truth_def by auto

lemma C_canonical_truth_disj_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "C_canonical_truth \<Gamma> T (Disj A B) \<longleftrightarrow>
    C_canonical_truth \<Gamma> T A \<or> C_canonical_truth \<Gamma> T B"
  using henkin A_type B_type C_Henkin_disj_mem_iff[OF henkin A_type B_type]
  unfolding C_canonical_truth_def by auto

lemma C_canonical_truth_forall_instance:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and truth: "C_canonical_truth \<Gamma> T (Forall \<sigma> A)"
  shows "C_canonical_truth \<Gamma> T (subst0 W A)"
proof -
  have forall_in: "Forall \<sigma> A \<in> T"
    using truth unfolding C_canonical_truth_def by blast
  have subst_in: "subst0 W A \<in> T"
    using henkin A_type W_type forall_in
    by (rule C_Henkin_forall_instance)
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  show ?thesis
    using henkin subst_type subst_in
    unfolding C_canonical_truth_def by blast
qed

lemma C_canonical_truth_forall_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "C_canonical_truth \<Gamma> T (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> C_canonical_truth \<Gamma> T (subst0 W A))"
proof
  assume truth: "C_canonical_truth \<Gamma> T (Forall \<sigma> A)"
  show "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> C_canonical_truth \<Gamma> T (subst0 W A)"
    using C_canonical_truth_forall_instance[OF henkin A_type _ truth] by blast
next
  assume all_truth: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> C_canonical_truth \<Gamma> T (subst0 W A)"
  have all_mem: "\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow> subst0 W A \<in> T"
    using all_truth C_canonical_truth_mem by blast
  have forall_in: "Forall \<sigma> A \<in> T"
    using C_Henkin_forall_mem_iff[OF henkin A_type] all_mem by blast
  show "C_canonical_truth \<Gamma> T (Forall \<sigma> A)"
    using henkin A_type forall_in
    unfolding C_canonical_truth_def by auto
qed

lemma C_canonical_truth_exists_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "C_canonical_truth \<Gamma> T (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> C_canonical_truth \<Gamma> T (subst0 W A))"
proof
  assume truth: "C_canonical_truth \<Gamma> T (Exists \<sigma> A)"
  then have exists_in: "Exists \<sigma> A \<in> T"
    unfolding C_canonical_truth_def by blast
  obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_in: "subst0 W A \<in> T"
    using C_Henkin_exists_witness[OF henkin A_type exists_in] by blast
  have subst_type: "\<Gamma> \<turnstile> subst0 W A : Prop"
    using A_type W_type by (rule subst0_preserves_typing)
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> C_canonical_truth \<Gamma> T (subst0 W A)"
    using W_type henkin subst_type subst_in
    unfolding C_canonical_truth_def by blast
next
  assume "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> C_canonical_truth \<Gamma> T (subst0 W A)"
  then obtain W where W_type: "\<Gamma> \<turnstile> W : \<sigma>"
    and subst_truth: "C_canonical_truth \<Gamma> T (subst0 W A)"
    by blast
  have subst_in: "subst0 W A \<in> T"
    using subst_truth by (rule C_canonical_truth_mem)
  have exists_in: "Exists \<sigma> A \<in> T"
    using C_Henkin_exists_mem_iff[OF henkin A_type] W_type subst_in by blast
  show "C_canonical_truth \<Gamma> T (Exists \<sigma> A)"
    using henkin A_type exists_in
    unfolding C_canonical_truth_def by auto
qed

lemma C_canonical_truth_refl:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "C_canonical_truth \<Gamma> T (Eq \<sigma> M M)"
proof -
  have closed: "C_deductively_closed \<Gamma> T"
    using henkin by (rule C_Henkin_deductively_closed)
  have eq_in: "Eq \<sigma> M M \<in> T"
    using closed M_type by (rule C_identity_refl_in)
  show ?thesis
    using henkin M_type eq_in
    unfolding C_canonical_truth_def by auto
qed

lemma C_canonical_truth_leibniz:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and eq_truth: "C_canonical_truth \<Gamma> T (Eq \<sigma> M N)"
    and app_truth: "C_canonical_truth \<Gamma> T (App F M)"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "C_canonical_truth \<Gamma> T (App F N)"
proof -
  have typed: "typed_theory \<Gamma> T"
    using henkin by (rule C_Henkin_typed_theory)
  have closed: "C_deductively_closed \<Gamma> T"
    using henkin by (rule C_Henkin_deductively_closed)
  have eq_in: "Eq \<sigma> M N \<in> T"
    using eq_truth by (rule C_canonical_truth_mem)
  have appM_in: "App F M \<in> T"
    using app_truth by (rule C_canonical_truth_mem)
  have appN_in: "App F N \<in> T"
    using typed closed eq_in appM_in M_type N_type F_type
    by (rule C_identity_subst_in)
  have appN_type: "\<Gamma> \<turnstile> App F N : Prop"
    using F_type N_type by auto
  show ?thesis
    using henkin appN_type appN_in
    unfolding C_canonical_truth_def by blast
qed

lemma C_canonical_truth_beta_eta_imp:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and equiv: "beta_eta_equiv \<Gamma> Prop A B"
    and truth: "C_canonical_truth \<Gamma> T A"
  shows "C_canonical_truth \<Gamma> T B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using equiv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using equiv by (rule beta_eta_equiv_right_type)
  have AB_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using A_type B_type by auto
  have BA_type: "\<Gamma> \<turnstile> Imp B A : Prop"
    using A_type B_type by auto
  have closed: "C_deductively_closed \<Gamma> T"
    using henkin by (rule C_Henkin_deductively_closed)
  have bicond_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
    using closed C_beta_eta_equiv[OF equiv] by (rule C_contains_theorems)
  have imp_in: "Imp A B \<in> T"
    using C_Henkin_conj_mem_iff[OF henkin AB_type BA_type] bicond_in by blast
  have A_in: "A \<in> T"
    using truth by (rule C_canonical_truth_mem)
  have B_in: "B \<in> T"
    using henkin A_in imp_in by (rule C_Henkin_closed_under_MP)
  show ?thesis
    using henkin B_type B_in
    unfolding C_canonical_truth_def by blast
qed

lemma C_canonical_truth_beta_eta_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and equiv: "beta_eta_equiv \<Gamma> Prop A B"
  shows "C_canonical_truth \<Gamma> T A \<longleftrightarrow> C_canonical_truth \<Gamma> T B"
  using C_canonical_truth_beta_eta_imp[OF henkin equiv]
    C_canonical_truth_beta_eta_imp[OF henkin beta_eta_equiv.Sym[OF equiv]]
  by blast

lemma C_subst_truth_neg_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Neg A) \<longleftrightarrow>
    \<not> C_subst_truth \<Delta> \<Gamma> T s A"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type subst_type
      C_canonical_truth_neg_iff[OF henkin subst_type]
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_imp_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Imp A B) \<longleftrightarrow>
    (C_subst_truth \<Delta> \<Gamma> T s A \<longrightarrow> C_subst_truth \<Delta> \<Gamma> T s B)"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      C_canonical_truth_imp_iff[OF henkin subst_A_type subst_B_type]
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_conj_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Conj A B) \<longleftrightarrow>
    C_subst_truth \<Delta> \<Gamma> T s A \<and> C_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      C_canonical_truth_conj_iff[OF henkin subst_A_type subst_B_type]
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_disj_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Disj A B) \<longleftrightarrow>
    C_subst_truth \<Delta> \<Gamma> T s A \<or> C_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have subst_A_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have subst_B_type: "\<Gamma> \<turnstile> subst s B : Prop"
    using B_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type B_type subst_A_type subst_B_type
      C_canonical_truth_disj_iff[OF henkin subst_A_type subst_B_type]
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_forall_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Forall \<sigma> A) \<longleftrightarrow>
    (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow>
      C_subst_truth (\<sigma> # \<Delta>) \<Gamma> T (case_nat W s) A)"
proof -
  have lift_typed: "term_subst_typed (\<sigma> # \<Delta>) (\<sigma> # \<Gamma>) (lift_subst s)"
    using s_typed by (rule term_subst_typed_lift)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> subst (lift_subst s) A : Prop"
    using A_type lift_typed by (rule term_subst_preserves_typing)
  have canon: "C_canonical_truth \<Gamma> T
      (Forall \<sigma> (subst (lift_subst s) A)) \<longleftrightarrow>
      (\<forall>W. \<Gamma> \<turnstile> W : \<sigma> \<longrightarrow>
        C_canonical_truth \<Gamma> T (subst0 W (subst (lift_subst s) A)))"
    using C_canonical_truth_forall_iff[OF henkin body_type] .
  show ?thesis
    using henkin s_typed A_type canon
    unfolding C_subst_truth_def
    by (auto simp: subst0_subst_lift intro: term_subst_typed_extend)
qed

lemma C_subst_truth_exists_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<sigma> # \<Delta> \<turnstile> A : Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Exists \<sigma> A) \<longleftrightarrow>
    (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and>
      C_subst_truth (\<sigma> # \<Delta>) \<Gamma> T (case_nat W s) A)"
proof -
  have lift_typed: "term_subst_typed (\<sigma> # \<Delta>) (\<sigma> # \<Gamma>) (lift_subst s)"
    using s_typed by (rule term_subst_typed_lift)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> subst (lift_subst s) A : Prop"
    using A_type lift_typed by (rule term_subst_preserves_typing)
  have canon: "C_canonical_truth \<Gamma> T
      (Exists \<sigma> (subst (lift_subst s) A)) \<longleftrightarrow>
      (\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and>
        C_canonical_truth \<Gamma> T (subst0 W (subst (lift_subst s) A)))"
    using C_canonical_truth_exists_iff[OF henkin body_type] .
  show ?thesis
    using henkin s_typed A_type canon
    unfolding C_subst_truth_def
    by (auto simp: subst0_subst_lift intro: term_subst_typed_extend)
qed

lemma C_subst_truth_refl:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
  shows "C_subst_truth \<Delta> \<Gamma> T s (Eq \<sigma> M M)"
proof -
  have subst_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have truth: "C_canonical_truth \<Gamma> T
      (Eq \<sigma> (subst s M) (subst s M))"
    using henkin subst_M_type by (rule C_canonical_truth_refl)
  show ?thesis
    using henkin s_typed M_type truth
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_leibniz:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and eq_truth: "C_subst_truth \<Delta> \<Gamma> T s (Eq \<sigma> M N)"
    and app_truth: "C_subst_truth \<Delta> \<Gamma> T s (App F M)"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and F_type: "\<Delta> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "C_subst_truth \<Delta> \<Gamma> T s (App F N)"
proof -
  have subst_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have subst_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have subst_F_type: "\<Gamma> \<turnstile> subst s F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using F_type s_typed by (rule term_subst_preserves_typing)
  have eq_canon: "C_canonical_truth \<Gamma> T
      (Eq \<sigma> (subst s M) (subst s N))"
    using eq_truth unfolding C_subst_truth_def by auto
  have app_canon: "C_canonical_truth \<Gamma> T (App (subst s F) (subst s M))"
    using app_truth unfolding C_subst_truth_def by auto
  have canon: "C_canonical_truth \<Gamma> T (App (subst s F) (subst s N))"
    using henkin eq_canon app_canon subst_M_type subst_N_type subst_F_type
    by (rule C_canonical_truth_leibniz)
  have appN_type: "\<Delta> \<turnstile> App F N : Prop"
    using F_type N_type by auto
  show ?thesis
    using henkin s_typed appN_type canon
    unfolding C_subst_truth_def by auto
qed

lemma C_subst_truth_beta_eta_iff:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and equiv: "beta_eta_equiv \<Delta> Prop A B"
  shows "C_subst_truth \<Delta> \<Gamma> T s A \<longleftrightarrow>
    C_subst_truth \<Delta> \<Gamma> T s B"
proof -
  have A_type: "\<Delta> \<turnstile> A : Prop"
    using equiv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Delta> \<turnstile> B : Prop"
    using equiv by (rule beta_eta_equiv_right_type)
  have subst_equiv: "beta_eta_equiv \<Gamma> Prop (subst s A) (subst s B)"
    using s_typed by (rule beta_eta_equiv_subst[OF equiv])
  show ?thesis
    using henkin s_typed A_type B_type
      C_canonical_truth_beta_eta_iff[OF henkin subst_equiv]
    unfolding C_subst_truth_def by auto
qed

section \<open>Equivalence-closed Henkin theories\<close>

text \<open>
  The systems \<open>CE\<close> and \<open>CEV\<close> extend \<open>C\<close> by adding propositional and
  vector equivalence rules.  A canonical theory for those systems therefore
  needs the ordinary \<open>C\<close>-Henkin conditions plus closure under the corresponding
  equivalence rule.  These definitions isolate exactly that extra machinery.
\<close>

definition CE_equivalence_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_equivalence_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>A B. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      (A \<longleftrightarrow>\<^sub>o B) \<in> T \<longrightarrow> Eq Prop A B \<in> T)"

definition CE_generalization_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_generalization_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>P \<sigma> Q. \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp (shift P) Q \<longrightarrow>
      Imp P (Forall \<sigma> Q) \<in> T)"

definition CE_instantiation_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_instantiation_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> P Q. \<sigma> # \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q) \<longrightarrow>
      Imp (Exists \<sigma> P) Q \<in> T)"

definition CE_rule_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_rule_closed \<Gamma> T \<longleftrightarrow>
    CE_equivalence_closed \<Gamma> T \<and>
    CE_generalization_closed \<Gamma> T \<and>
    CE_instantiation_closed \<Gamma> T"

definition CEV_vector_equivalence_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_vector_equivalence_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma>s F G. \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<longrightarrow>
      \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<longrightarrow>
      \<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body \<sigma>s F G \<longrightarrow>
      Eq (arrow_type \<sigma>s Prop) F G \<in> T)"

definition CEV_context_vector_equivalence_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_context_vector_equivalence_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma>s A F G. \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<longrightarrow>
      \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<longrightarrow>
      \<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G) \<longrightarrow>
      Imp A (Eq (arrow_type \<sigma>s Prop) F G) \<in> T)"

definition CEV_generalization_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_generalization_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>P \<sigma> Q. \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q \<longrightarrow>
      Imp P (Forall \<sigma> Q) \<in> T)"

definition CEV_instantiation_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_instantiation_closed \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> P Q. \<sigma> # \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q) \<longrightarrow>
      Imp (Exists \<sigma> P) Q \<in> T)"

definition CEV_rule_closed :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_rule_closed \<Gamma> T \<longleftrightarrow>
    CEV_vector_equivalence_closed \<Gamma> T \<and>
    CEV_context_vector_equivalence_closed \<Gamma> T \<and>
    CEV_generalization_closed \<Gamma> T \<and>
    CEV_instantiation_closed \<Gamma> T"

definition CE_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_Henkin_theory \<Gamma> T \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> CE_rule_closed \<Gamma> T"

definition CEV_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_Henkin_theory \<Gamma> T \<longleftrightarrow>
    CE_Henkin_theory \<Gamma> T \<and> CEV_rule_closed \<Gamma> T"

lemma CE_Henkin_C_Henkin:
  assumes "CE_Henkin_theory \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> T"
  using assms unfolding CE_Henkin_theory_def by blast

lemma CE_Henkin_equivalence_closed:
  assumes "CE_Henkin_theory \<Gamma> T"
  shows "CE_equivalence_closed \<Gamma> T"
  using assms unfolding CE_Henkin_theory_def CE_rule_closed_def by blast

lemma CE_Henkin_generalization_closed:
  assumes "CE_Henkin_theory \<Gamma> T"
  shows "CE_generalization_closed \<Gamma> T"
  using assms unfolding CE_Henkin_theory_def CE_rule_closed_def by blast

lemma CE_Henkin_instantiation_closed:
  assumes "CE_Henkin_theory \<Gamma> T"
  shows "CE_instantiation_closed \<Gamma> T"
  using assms unfolding CE_Henkin_theory_def CE_rule_closed_def by blast

lemma CEV_Henkin_CE_Henkin:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
  using assms unfolding CEV_Henkin_theory_def by blast

lemma CEV_Henkin_C_Henkin:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> T"
  using CEV_Henkin_CE_Henkin[OF assms] by (rule CE_Henkin_C_Henkin)

lemma CEV_Henkin_vector_equivalence_closed:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_vector_equivalence_closed \<Gamma> T"
  using assms unfolding CEV_Henkin_theory_def CEV_rule_closed_def by blast

lemma CEV_Henkin_context_vector_equivalence_closed:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_context_vector_equivalence_closed \<Gamma> T"
  using assms unfolding CEV_Henkin_theory_def CEV_rule_closed_def by blast

lemma CEV_Henkin_generalization_closed:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_generalization_closed \<Gamma> T"
  using assms unfolding CEV_Henkin_theory_def CEV_rule_closed_def by blast

lemma CEV_Henkin_instantiation_closed:
  assumes "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_instantiation_closed \<Gamma> T"
  using assms unfolding CEV_Henkin_theory_def CEV_rule_closed_def by blast

lemma CE_equivalence_closedD:
  assumes "CE_equivalence_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
  shows "Eq Prop A B \<in> T"
  using assms unfolding CE_equivalence_closed_def by blast

lemma CEV_vector_equivalence_closedD:
  assumes "CEV_vector_equivalence_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body \<sigma>s F G"
  shows "Eq (arrow_type \<sigma>s Prop) F G \<in> T"
  using assms unfolding CEV_vector_equivalence_closed_def by blast

lemma CEV_context_vector_equivalence_closedD:
  assumes "CEV_context_vector_equivalence_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G)"
  shows "Imp A (Eq (arrow_type \<sigma>s Prop) F G) \<in> T"
  using assms unfolding CEV_context_vector_equivalence_closed_def by blast

lemma CE_generalization_closedD:
  assumes "CE_generalization_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> P : Prop"
    and "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp (shift P) Q"
  shows "Imp P (Forall \<sigma> Q) \<in> T"
  using assms unfolding CE_generalization_closed_def by blast

lemma CE_instantiation_closedD:
  assumes "CE_instantiation_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q)"
  shows "Imp (Exists \<sigma> P) Q \<in> T"
  using assms unfolding CE_instantiation_closed_def by blast

lemma CEV_generalization_closedD:
  assumes "CEV_generalization_closed \<Gamma> T"
    and "\<Gamma> \<turnstile> P : Prop"
    and "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q"
  shows "Imp P (Forall \<sigma> Q) \<in> T"
  using assms unfolding CEV_generalization_closed_def by blast

lemma CEV_instantiation_closedD:
  assumes "CEV_instantiation_closed \<Gamma> T"
    and "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
  shows "Imp (Exists \<sigma> P) Q \<in> T"
  using assms unfolding CEV_instantiation_closed_def by blast

lemma CE_Henkin_contains_theorems:
  assumes proves: "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "\<And>T. CE_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  using proves
proof (induction rule: CE_proves.induct)
  case (C \<Gamma> A)
  show ?case
    using C.hyps C.prems CE_Henkin_C_Henkin C_Henkin_contains_theorems by blast
next
  case (PropEquivalence \<Gamma> A B)
  have closed: "CE_equivalence_closed \<Gamma> T"
    using PropEquivalence.prems by (rule CE_Henkin_equivalence_closed)
  have iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
    using PropEquivalence.prems by (rule PropEquivalence.IH)
  show ?case
    using closed PropEquivalence.hyps(1,2) iff_in
    by (rule CE_equivalence_closedD)
next
  case (MP \<Gamma> A B)
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using MP.prems by (rule CE_Henkin_C_Henkin)
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have closed: "C_deductively_closed \<Gamma> T"
    using c_henkin by (rule C_Henkin_deductively_closed)
  have A_in: "A \<in> T"
    using MP.prems by (rule MP.IH(1))
  have imp_in: "Imp A B \<in> T"
    using MP.prems by (rule MP.IH(2))
  show ?case
    using typed closed A_in imp_in by (rule C_closed_under_MP)
next
  case (Gen \<Gamma> P \<sigma> Q)
  have closed: "CE_generalization_closed \<Gamma> T"
    using Gen.prems by (rule CE_Henkin_generalization_closed)
  show ?case
    using closed Gen.hyps(1,2,3) by (rule CE_generalization_closedD)
next
  case (Inst \<sigma> \<Gamma> P Q)
  have closed: "CE_instantiation_closed \<Gamma> T"
    using Inst.prems by (rule CE_Henkin_instantiation_closed)
  show ?case
    using closed Inst.hyps(1,2,3) by (rule CE_instantiation_closedD)
qed

lemma CE_Henkin_contains_CEV_base:
  assumes "CEV_Henkin_theory \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "A \<in> T"
  using assms(2) CEV_Henkin_CE_Henkin[OF assms(1)]
  by (rule CE_Henkin_contains_theorems)

lemma CEV_Henkin_contains_theorems:
  assumes proves: "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<And>T. CEV_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  using proves
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  show ?case
    using CE.prems CE.hyps by (rule CE_Henkin_contains_CEV_base)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  have closed: "CEV_vector_equivalence_closed \<Gamma> T"
    using VectorEquivalence.prems by (rule CEV_Henkin_vector_equivalence_closed)
  show ?case
    using closed VectorEquivalence.hyps(1,2,3)
    by (rule CEV_vector_equivalence_closedD)
next
  case (ContextVectorEquivalence \<Gamma> A F \<sigma>s G)
  have closed: "CEV_context_vector_equivalence_closed \<Gamma> T"
    using ContextVectorEquivalence.prems
    by (rule CEV_Henkin_context_vector_equivalence_closed)
  show ?case
    using closed ContextVectorEquivalence.hyps(1,2,3,4)
    by (rule CEV_context_vector_equivalence_closedD)
next
  case (MP \<Gamma> A B)
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using MP.prems by (rule CEV_Henkin_C_Henkin)
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have closed: "C_deductively_closed \<Gamma> T"
    using c_henkin by (rule C_Henkin_deductively_closed)
  have A_in: "A \<in> T"
    using MP.prems by (rule MP.IH(1))
  have imp_in: "Imp A B \<in> T"
    using MP.prems by (rule MP.IH(2))
  show ?case
    using typed closed A_in imp_in by (rule C_closed_under_MP)
next
  case (Gen \<Gamma> P \<sigma> Q)
  have closed: "CEV_generalization_closed \<Gamma> T"
    using Gen.prems by (rule CEV_Henkin_generalization_closed)
  show ?case
    using closed Gen.hyps(1,2,3) by (rule CEV_generalization_closedD)
next
  case (Inst \<sigma> \<Gamma> P Q)
  have closed: "CEV_instantiation_closed \<Gamma> T"
    using Inst.prems by (rule CEV_Henkin_instantiation_closed)
  show ?case
    using closed Inst.hyps(1,2,3) by (rule CEV_instantiation_closedD)
qed

section \<open>Local derivability for equivalence extensions\<close>

text \<open>
  To build Lindenbaum-Henkin countermodels for \<open>CE\<close> and \<open>CEV\<close>, consistency
  must be measured against the corresponding theorem relation plus local
  assumptions.  The base theories only supplied local derivability for \<open>H\<close>
  and \<open>C\<close>; the following inductive relations provide the analogous finite
  assumption consequence relations for the equivalence extensions.
\<close>

inductive CE_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>CE\<^sub>s _" [50, 50, 50] 50) where
  Assumption[intro]: "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
| Derive_MP[intro]:
    "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A B \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s B"

lemma CE_set_derivable_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CE_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CE_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case
    by (auto elim: has_type.cases)
qed

lemma CE_set_derivable_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s A"
  using assms
proof (induction rule: CE_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (intro CE_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (intro CE_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  from Derive_MP.IH(1)[OF Derive_MP.prems]
    Derive_MP.IH(2)[OF Derive_MP.prems]
  show ?case
    by (rule CE_set_derivable.Derive_MP)
qed

lemma CE_set_derivable_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  obtains U where "finite U" and "U \<subseteq> T" and "\<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s A"
proof -
  have "\<exists>U. finite U \<and> U \<subseteq> T \<and> \<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s A"
    using assms
  proof (induction rule: CE_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> A T)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (Derive_MP \<Gamma> T A B)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_A: "\<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s A"
      using Derive_MP.IH(1) by auto
    obtain V where V_fin: "finite V" and V_sub: "V \<subseteq> T"
      and V_imp: "\<Gamma> ; V \<turnstile>\<^sub>CE\<^sub>s Imp A B"
      using Derive_MP.IH(2) by auto
    have A_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CE\<^sub>s A"
      using U_A by (rule CE_set_derivable_mono) auto
    have imp_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CE\<^sub>s Imp A B"
      using V_imp by (rule CE_set_derivable_mono) auto
    have B_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CE\<^sub>s B"
      using A_der imp_der by (rule CE_set_derivable.Derive_MP)
    show ?case
      using U_fin U_sub V_fin V_sub B_der by (intro exI[of _ "U \<union> V"]) auto
  qed
  then show ?thesis
    using that by blast
qed

lemma CE_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  using assms by (rule CE_set_derivable.Theorem)

lemma CE_set_MP:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s B"
  using assms by (rule CE_set_derivable.Derive_MP)

lemma CE_set_ex_falso:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
proof -
  have taut_raw: "\<Gamma> \<turnstile>\<^sub>CE Imp (Neg ObjTrue) (Imp ObjTrue A)"
    using typed_ObjTrue assms(2)
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_imp_of_neg_left)
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp ObjFalse (Imp ObjTrue A)"
    using taut_raw by (simp add: ObjFalse_def)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp ObjFalse (Imp ObjTrue A)"
    using taut by (rule CE_set_Theorem)
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp ObjTrue A"
    using assms(1) d_taut by (rule CE_set_MP)
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjTrue"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>CE ObjTrue"
      by (intro CE_proves.C C_proves.H H_proves_ObjTrue)
    then show ?thesis
      by (rule CE_set_Theorem)
  qed
  show ?thesis
    using d_true d_imp by (rule CE_set_MP)
qed

lemma CE_set_empty_imp_proves:
  assumes "\<Gamma> ; {} \<turnstile>\<^sub>CE\<^sub>s A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
proof -
  have empty_imp:
    "\<And>\<Gamma> T A. \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A \<Longrightarrow> T = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  proof -
    fix \<Gamma> T A
    assume "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    then show "T = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
    proof (induction rule: CE_set_derivable.induct)
      case (Assumption A T \<Gamma>)
      then show ?case
        by simp
    next
      case (Theorem \<Gamma> A T)
      then show ?case
        by simp
    next
      case (Derive_MP \<Gamma> T A B)
      have dA: "\<Gamma> \<turnstile>\<^sub>CE A"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have dImp: "\<Gamma> \<turnstile>\<^sub>CE Imp A B"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using dA dImp by (rule CE_proves.MP)
    qed
  qed
  show ?thesis
    using assms by (rule empty_imp[OF _ refl])
qed

lemma CE_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CE B"
  shows "\<Gamma> \<turnstile>\<^sub>CE Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CE_proves_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp B (Imp A B)"
    using assms(1) B_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_imp_of_right)
  show ?thesis
    using assms(2) taut by (rule CE_proves.MP)
qed

lemma CE_proves_imp_false_to_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CE Imp (Imp A ObjFalse) (Neg A)"
  using C_proves_imp_false_to_neg[OF assms] by (rule CE_proves.C)

lemma CE_proves_imp_neg_false_to_formula:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CE Imp (Imp (Neg A) ObjFalse) A"
  using C_proves_imp_neg_false_to_formula[OF assms] by (rule CE_proves.C)

lemma CE_set_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; insert A T \<turnstile>\<^sub>CE\<^sub>s B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A B"
proof -
  have aux: "\<And>X S. \<Gamma> \<turnstile> X : Prop \<Longrightarrow>
      insert A T \<subseteq> insert X S \<Longrightarrow>
      \<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s Imp X B"
    using assms(2)
  proof (induction rule: CE_set_derivable.induct)
    case (Assumption B U \<Gamma>)
    have X_type: "\<Gamma> \<turnstile> X : Prop"
      using Assumption.prems by blast
    have U_sub: "U \<subseteq> insert X S"
      using Assumption.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps by simp
    show ?case
    proof (cases "B = X")
      case True
      have "\<Gamma> \<turnstile>\<^sub>CE Imp X X"
        using X_type by (intro CE_proves.C C_proves.H H_imp_self)
      then have "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s Imp X X"
        by (rule CE_set_Theorem)
      then show ?thesis
        using True by simp
    next
      case False
      have B_in: "B \<in> S"
        using Assumption.hyps U_sub False by blast
      have dB: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s B"
        using B_in B_type by (rule CE_set_derivable.Assumption)
      have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp B (Imp X B)"
        using X_type B_type
        by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_imp_of_right)
      have d_taut: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s Imp B (Imp X B)"
        using taut by (rule CE_set_Theorem)
      show ?thesis
        using dB d_taut by (rule CE_set_MP)
    qed
  next
    case (Theorem \<Gamma> B U)
    have "\<Gamma> \<turnstile>\<^sub>CE Imp X B"
      using Theorem.prems(1) Theorem.hyps by (rule CE_proves_imp_of_right)
    then show ?case
      by (rule CE_set_Theorem)
  next
    case (Derive_MP \<Gamma> U B C)
    have X_type: "\<Gamma> \<turnstile> X : Prop"
      using Derive_MP.prems by blast
    have U_sub: "U \<subseteq> insert X S"
      using Derive_MP.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule CE_set_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2) by (auto dest: CE_set_derivable_formula elim: has_type.cases)
    have taut: "\<Gamma> \<turnstile>\<^sub>CE
        Imp (Imp X B) (Imp (Imp X (Imp B C)) (Imp X C))"
      using X_type B_type C_type
      by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_deduction_mp)
    have d_taut: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s
        Imp (Imp X B) (Imp (Imp X (Imp B C)) (Imp X C))"
      using taut by (rule CE_set_Theorem)
    have IH_B: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s Imp X B"
      using X_type U_sub by (rule Derive_MP.IH(1))
    have IH_imp: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s Imp X (Imp B C)"
      using X_type U_sub by (rule Derive_MP.IH(2))
    have step: "\<Gamma> ; S \<turnstile>\<^sub>CE\<^sub>s
        Imp (Imp X (Imp B C)) (Imp X C)"
      using IH_B d_taut by (rule CE_set_MP)
    show ?case
      using IH_imp step by (rule CE_set_MP)
  qed
  show ?thesis
    using assms(1) by (rule aux) blast
qed

definition CE_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_consistent \<Gamma> T \<longleftrightarrow> \<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"

lemma CE_consistentD:
  assumes "CE_consistent \<Gamma> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  using assms unfolding CE_consistent_def by blast

lemma CE_consistent_mono:
  assumes "CE_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "CE_consistent \<Gamma> T"
  using assms CE_set_derivable_mono unfolding CE_consistent_def by blast

lemma CE_consistent_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "CE_consistent \<Gamma> T"
proof (unfold CE_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  then have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    using assms(1) by (rule CE_set_ex_falso)
  then show False
    using assms(2) by blast
qed

lemma CE_consistent_singleton_neg_of_not_proves:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  shows "CE_consistent \<Gamma> {Neg A}"
proof (unfold CE_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; {Neg A} \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "\<Gamma> ; {} \<turnstile>\<^sub>CE\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule CE_set_derivable_deduction)
  have imp_false: "\<Gamma> \<turnstile>\<^sub>CE Imp (Neg A) ObjFalse"
    using d_imp_false by (rule CE_set_empty_imp_proves)
  have imp_A: "\<Gamma> \<turnstile>\<^sub>CE Imp (Imp (Neg A) ObjFalse) A"
    using assms(1) by (rule CE_proves_imp_neg_false_to_formula)
  have "\<Gamma> \<turnstile>\<^sub>CE A"
    using imp_false imp_A by (rule CE_proves.MP)
  then show False
    using assms(2) by contradiction
qed

lemma CE_set_derives_ObjFalse_of_formula_and_neg:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    and "Neg A \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CE_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule CE_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
    using assms(2) neg_type by (rule CE_set_derivable.Assumption)
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CE_set_MP)
  show ?thesis
    using d_neg d_imp_false by (rule CE_set_MP)
qed

lemma CE_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CE_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule CE_set_Theorem)
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CE_set_MP)
  show ?thesis
    using assms(2) d_imp_false by (rule CE_set_MP)
qed

lemma CE_consistent_not_both_derivable:
  assumes "CE_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
proof
  assume d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
  have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using assms(2) d_neg by (rule CE_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding CE_consistent_def by blast
qed

lemma CE_consistent_not_derives_with_neg:
  assumes "CE_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  then have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using assms(2) by (rule CE_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding CE_consistent_def by blast
qed

lemma CE_consistent_insert_formula_if_not_neg_derivable:
  assumes "CE_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
  shows "CE_consistent \<Gamma> (insert A T)"
proof (unfold CE_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule CE_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using CE_proves_imp_false_to_neg[OF assms(2)] by (rule CE_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule CE_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CE_consistent_insert_neg_if_not_derivable:
  assumes "CE_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "CE_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold CE_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule CE_set_derivable_deduction)
  have d_A_thm: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Imp (Neg A) ObjFalse) A"
    using CE_proves_imp_neg_false_to_formula[OF assms(2)] by (rule CE_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    using d_imp_false d_A_thm by (rule CE_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CE_consistent_insert_neg_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "CE_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have consistent: "CE_consistent \<Gamma> T"
    using assms by (rule CE_consistent_of_not_set_derivable)
  show ?thesis
    using consistent assms by (rule CE_consistent_insert_neg_if_not_derivable)
qed

lemma CE_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "CE_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_consistent \<Gamma> (insert A T)"
  shows "CE_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using assms(3) unfolding CE_consistent_def by blast
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule CE_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using CE_proves_imp_false_to_neg[OF assms(2)] by (rule CE_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule CE_set_MP)
  have not_d_A: "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  proof
    assume d_A: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
      using d_A d_neg by (rule CE_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding CE_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A by (rule CE_consistent_insert_neg_if_not_derivable)
qed

lemma CE_consistent_decidable_extension:
  assumes "CE_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "CE_consistent \<Gamma> (insert A T) \<or>
    CE_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "CE_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis
    by blast
next
  case False
  have "CE_consistent \<Gamma> (insert (Neg A) T)"
    using assms False by (rule CE_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis
    by blast
qed

definition CE_negation_complete :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_negation_complete \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> A \<in> T \<or> Neg A \<in> T)"

definition CE_locally_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_locally_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> CE_consistent \<Gamma> T \<and> CE_negation_complete \<Gamma> T"

definition CE_lindenbaum_step :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CE_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if CE_consistent \<Gamma> (insert A T) then insert A T else insert (Neg A) T)
     else T)"

primrec CE_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CE_lindenbaum_chain \<Gamma> T enum 0 = T"
| "CE_lindenbaum_chain \<Gamma> T enum (Suc n) =
    CE_lindenbaum_step \<Gamma> (enum n) (CE_lindenbaum_chain \<Gamma> T enum n)"

definition CE_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "CE_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. CE_lindenbaum_chain \<Gamma> T enum n)"

lemma CE_lindenbaum_step_extends:
  "T \<subseteq> CE_lindenbaum_step \<Gamma> A T"
  unfolding CE_lindenbaum_step_def by auto

lemma CE_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_lindenbaum_step \<Gamma> A T)"
  using assms unfolding CE_lindenbaum_step_def typed_theory_def by auto

lemma CE_lindenbaum_step_consistent:
  assumes "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (CE_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding CE_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "CE_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> unfolding CE_lindenbaum_step_def by simp
  next
    case False
    have "CE_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule CE_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False unfolding CE_lindenbaum_step_def by simp
  qed
qed

lemma CE_lindenbaum_chain_step:
  "CE_lindenbaum_chain \<Gamma> T enum n \<subseteq> CE_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using CE_lindenbaum_step_extends[of
      "CE_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma CE_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_lindenbaum_step_typed)
qed

lemma CE_lindenbaum_chain_consistent:
  assumes "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (CE_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_lindenbaum_step_consistent)
qed

lemma CE_lindenbaum_extension_extends:
  "T \<subseteq> CE_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> CE_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> CE_lindenbaum_extension \<Gamma> T enum"
    unfolding CE_lindenbaum_extension_def by blast
qed

lemma CE_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (CE_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CE_lindenbaum_chain_typed)
  then show ?thesis
    unfolding CE_lindenbaum_extension_def by (rule typed_theory_nat_union)
qed

lemma CE_lindenbaum_extension_consistent:
  assumes "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CE_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; CE_lindenbaum_extension \<Gamma> T enum \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CE_lindenbaum_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using d_false by (rule CE_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. CE_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding CE_lindenbaum_extension_def .
  have step: "\<And>n. CE_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      CE_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule CE_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> CE_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> CE_lindenbaum_chain \<Gamma> T enum n"
    by blast
  have "\<Gamma> ; CE_lindenbaum_chain \<Gamma> T enum n \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CE_set_derivable_mono)
  moreover have "CE_consistent \<Gamma> (CE_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CE_lindenbaum_chain_consistent)
  ultimately show False
    unfolding CE_consistent_def by blast
qed

lemma CE_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "CE_negation_complete \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CE_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "CE_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "CE_lindenbaum_chain \<Gamma> T enum (Suc n) =
      CE_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> CE_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> CE_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "CE_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> CE_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding CE_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> CE_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding CE_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> CE_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> CE_lindenbaum_extension \<Gamma> T enum"
    unfolding CE_lindenbaum_extension_def by blast
qed

theorem CE_lindenbaum_extension_locally_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "CE_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "CE_locally_maximal_consistent \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule CE_lindenbaum_extension_typed)
  have consistent: "CE_consistent \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule CE_lindenbaum_extension_consistent)
  have complete: "CE_negation_complete \<Gamma> (CE_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule CE_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CE_locally_maximal_consistent_def by simp
qed

lemma CE_locally_maximal_consistent_deductively_closed:
  assumes "CE_locally_maximal_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "A \<in> T"
proof (cases "A \<in> T")
  case True
  then show ?thesis .
next
  case False
  have consistent: "CE_consistent \<Gamma> T"
    using assms(1) unfolding CE_locally_maximal_consistent_def by blast
  have complete: "CE_negation_complete \<Gamma> T"
    using assms(1) unfolding CE_locally_maximal_consistent_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule CE_set_derivable_formula)
  have neg_in: "Neg A \<in> T"
    using complete A_type False unfolding CE_negation_complete_def by blast
  have "\<not> \<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    using consistent neg_in by (rule CE_consistent_not_derives_with_neg)
  then show ?thesis
    using assms(2) by blast
qed

lemma CE_locally_maximal_consistent_contains_theorems:
  assumes "CE_locally_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "A \<in> T"
proof -
  have derivable: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    using assms(2) by (rule CE_set_Theorem)
  show ?thesis
    using assms(1) derivable by (rule CE_locally_maximal_consistent_deductively_closed)
qed

lemma CE_locally_maximal_generalization_closed:
  assumes "CE_locally_maximal_consistent \<Gamma> T"
  shows "CE_generalization_closed \<Gamma> T"
proof (unfold CE_generalization_closed_def, intro allI impI)
  fix P \<sigma> Q
  assume P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp (shift P) Q"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CE Imp P (Forall \<sigma> Q)"
    using P_type Q_type d by (rule CE_proves.Gen)
  show "Imp P (Forall \<sigma> Q) \<in> T"
    using assms d_rule by (rule CE_locally_maximal_consistent_contains_theorems)
qed

lemma CE_locally_maximal_instantiation_closed:
  assumes "CE_locally_maximal_consistent \<Gamma> T"
  shows "CE_instantiation_closed \<Gamma> T"
proof (unfold CE_instantiation_closed_def, intro allI impI)
  fix \<sigma> P Q
  assume P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q)"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CE Imp (Exists \<sigma> P) Q"
    using P_type Q_type d by (rule CE_proves.Inst)
  show "Imp (Exists \<sigma> P) Q \<in> T"
    using assms d_rule by (rule CE_locally_maximal_consistent_contains_theorems)
qed

lemma CE_rule_closed_of_local_maximal_and_equivalence_closed:
  assumes "CE_locally_maximal_consistent \<Gamma> T"
    and "CE_equivalence_closed \<Gamma> T"
  shows "CE_rule_closed \<Gamma> T"
proof -
  have gen: "CE_generalization_closed \<Gamma> T"
    using assms(1) by (rule CE_locally_maximal_generalization_closed)
  have inst: "CE_instantiation_closed \<Gamma> T"
    using assms(1) by (rule CE_locally_maximal_instantiation_closed)
  show ?thesis
    using assms(2) gen inst unfolding CE_rule_closed_def by blast
qed

lemma CE_Henkin_theory_of_C_Henkin_local_maximal_equivalence_closed:
  assumes "C_Henkin_theory \<Gamma> T"
    and "CE_locally_maximal_consistent \<Gamma> T"
    and "CE_equivalence_closed \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have closed: "CE_rule_closed \<Gamma> T"
    using assms(2,3) by (rule CE_rule_closed_of_local_maximal_and_equivalence_closed)
  show ?thesis
    using assms(1) closed unfolding CE_Henkin_theory_def by blast
qed

text \<open>
  The preceding Lindenbaum construction is local only for the theoremhood and
  modus-ponens part of \<open>CE\<close>.  To make propositional equivalence closure a
  consequence of maximality itself, we use a strengthened local consequence
  relation with exactly the local form of the \<open>CE\<close> equivalence rule.
\<close>

inductive CE_equiv_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  Assumption[intro]:
    "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> CE_equiv_set_derivable \<Gamma> T A"
| Theorem[intro]:
    "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> CE_equiv_set_derivable \<Gamma> T A"
| Derive_MP[intro]:
    "CE_equiv_set_derivable \<Gamma> T A \<Longrightarrow>
      CE_equiv_set_derivable \<Gamma> T (Imp A B) \<Longrightarrow>
      CE_equiv_set_derivable \<Gamma> T B"
| LocalPropEquivalence[intro]:
    "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
      CE_equiv_set_derivable \<Gamma> T (A \<longleftrightarrow>\<^sub>o B) \<Longrightarrow>
      CE_equiv_set_derivable \<Gamma> T (Eq Prop A B)"

lemma CE_equiv_set_derivable_formula:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CE_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CE_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (LocalPropEquivalence \<Gamma> A B T)
  then show ?case
    by auto
qed

lemma CE_equiv_set_derivable_mono:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "T \<subseteq> U"
  shows "CE_equiv_set_derivable \<Gamma> U A"
  using assms
proof (induction rule: CE_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (intro CE_equiv_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (intro CE_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  from Derive_MP.IH(1)[OF Derive_MP.prems]
    Derive_MP.IH(2)[OF Derive_MP.prems]
  show ?case
    by (rule CE_equiv_set_derivable.Derive_MP)
next
  case (LocalPropEquivalence \<Gamma> A B T)
  have d_iff: "CE_equiv_set_derivable \<Gamma> U (A \<longleftrightarrow>\<^sub>o B)"
    using LocalPropEquivalence.IH[OF LocalPropEquivalence.prems] .
  show ?case
    using LocalPropEquivalence.hyps(1,2) d_iff
    by (rule CE_equiv_set_derivable.LocalPropEquivalence)
qed

lemma CE_equiv_set_derivable_finite_support:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
  obtains U where "finite U" and "U \<subseteq> T" and "CE_equiv_set_derivable \<Gamma> U A"
proof -
  have "\<exists>U. finite U \<and> U \<subseteq> T \<and> CE_equiv_set_derivable \<Gamma> U A"
    using assms
  proof (induction rule: CE_equiv_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> A T)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (Derive_MP \<Gamma> T A B)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_A: "CE_equiv_set_derivable \<Gamma> U A"
      using Derive_MP.IH(1) by auto
    obtain V where V_fin: "finite V" and V_sub: "V \<subseteq> T"
      and V_imp: "CE_equiv_set_derivable \<Gamma> V (Imp A B)"
      using Derive_MP.IH(2) by auto
    have A_der: "CE_equiv_set_derivable \<Gamma> (U \<union> V) A"
      using U_A by (rule CE_equiv_set_derivable_mono) auto
    have imp_der: "CE_equiv_set_derivable \<Gamma> (U \<union> V) (Imp A B)"
      using V_imp by (rule CE_equiv_set_derivable_mono) auto
    have B_der: "CE_equiv_set_derivable \<Gamma> (U \<union> V) B"
      using A_der imp_der by (rule CE_equiv_set_derivable.Derive_MP)
    show ?case
      using U_fin U_sub V_fin V_sub B_der by (intro exI[of _ "U \<union> V"]) auto
  next
    case (LocalPropEquivalence \<Gamma> A B T)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_iff: "CE_equiv_set_derivable \<Gamma> U (A \<longleftrightarrow>\<^sub>o B)"
      using LocalPropEquivalence.IH by auto
    have eq_der: "CE_equiv_set_derivable \<Gamma> U (Eq Prop A B)"
      using LocalPropEquivalence.hyps(1,2) U_iff
      by (rule CE_equiv_set_derivable.LocalPropEquivalence)
    show ?case
      using U_fin U_sub eq_der by blast
  qed
  then show ?thesis
    using that by blast
qed

lemma CE_equiv_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "CE_equiv_set_derivable \<Gamma> T A"
  using assms by (rule CE_equiv_set_derivable.Theorem)

lemma CE_equiv_set_MP:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "CE_equiv_set_derivable \<Gamma> T (Imp A B)"
  shows "CE_equiv_set_derivable \<Gamma> T B"
  using assms by (rule CE_equiv_set_derivable.Derive_MP)

lemma CE_equiv_set_derivable_of_CE_set_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "CE_equiv_set_derivable \<Gamma> T A"
  using assms
proof (induction rule: CE_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (rule CE_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CE_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  show ?case
    using Derive_MP.IH(1) Derive_MP.IH(2)
    by (rule CE_equiv_set_derivable.Derive_MP)
qed

lemma CE_equiv_set_derivable_subst_const:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
    (subst_const c \<sigma> N A)"
  using assms
proof (induction rule: CE_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule subst_const_preserves_typing)
  have "subst_const c \<sigma> N A \<in> subst_const c \<sigma> N ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_sub_type by (rule CE_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule CE_proves_subst_const)
  then show ?case
    by (rule CE_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A: "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N A)"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw: "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N (Imp A B))"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp: "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B))"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CE_equiv_set_derivable.Derive_MP)
next
  case (LocalPropEquivalence \<Gamma> A B T)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using LocalPropEquivalence.hyps(1) LocalPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using LocalPropEquivalence.hyps(2) LocalPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_iff_raw: "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N (A \<longleftrightarrow>\<^sub>o B))"
    using LocalPropEquivalence.prems by (rule LocalPropEquivalence.IH)
  have d_iff: "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o subst_const c \<sigma> N B)"
    using d_iff_raw by simp
  have "CE_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (Eq Prop (subst_const c \<sigma> N A) (subst_const c \<sigma> N B))"
    using A_sub_type B_sub_type d_iff
    by (rule CE_equiv_set_derivable.LocalPropEquivalence)
  then show ?case
    by simp
qed

lemma CE_equiv_set_derivable_rename:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "CE_equiv_set_derivable \<Delta> (rename r ` T) (rename r A)"
  using assms
proof (induction arbitrary: \<Delta> r rule: CE_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule renaming_preserves_typing)
  have "rename r A \<in> rename r ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_ren_type by (rule CE_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<Delta> \<turnstile>\<^sub>CE rename r A"
    using Theorem.hyps Theorem.prems by (rule CE_proves_rename)
  then show ?case
    by (rule CE_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A: "CE_equiv_set_derivable \<Delta> (rename r ` T) (rename r A)"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw: "CE_equiv_set_derivable \<Delta> (rename r ` T) (rename r (Imp A B))"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp: "CE_equiv_set_derivable \<Delta> (rename r ` T) (Imp (rename r A) (rename r B))"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CE_equiv_set_derivable.Derive_MP)
next
  case (LocalPropEquivalence \<Gamma> A B T)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using LocalPropEquivalence.hyps(1) LocalPropEquivalence.prems
    by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : Prop"
    using LocalPropEquivalence.hyps(2) LocalPropEquivalence.prems
    by (rule renaming_preserves_typing)
  have d_iff_raw: "CE_equiv_set_derivable \<Delta> (rename r ` T)
      (rename r (A \<longleftrightarrow>\<^sub>o B))"
    using LocalPropEquivalence.prems by (rule LocalPropEquivalence.IH)
  have d_iff: "CE_equiv_set_derivable \<Delta> (rename r ` T)
      (rename r A \<longleftrightarrow>\<^sub>o rename r B)"
    using d_iff_raw by simp
  have "CE_equiv_set_derivable \<Delta> (rename r ` T)
      (Eq Prop (rename r A) (rename r B))"
    using A_ren_type B_ren_type d_iff
    by (rule CE_equiv_set_derivable.LocalPropEquivalence)
  then show ?case
    by simp
qed

lemma CE_equiv_set_derivable_shift:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
  shows "CE_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T) (shift A)"
  unfolding shift_def
  using assms by (rule CE_equiv_set_derivable_rename) auto

lemma CE_equiv_set_derivable_abstract_const:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
  shows "CE_equiv_set_derivable (\<sigma> # \<Gamma>) (abstract_const c \<sigma> ` T)
    (abstract_const c \<sigma> A)"
proof -
  have shifted: "CE_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T) (shift A)"
    using assms by (rule CE_equiv_set_derivable_shift)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have "CE_equiv_set_derivable (\<sigma> # \<Gamma>)
      (subst_const c \<sigma> (Var 0) ` (shift ` T))
      (subst_const c \<sigma> (Var 0) (shift A))"
    using shifted var_type by (rule CE_equiv_set_derivable_subst_const)
  moreover have "subst_const c \<sigma> (Var 0) ` (shift ` T) =
      abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  ultimately show ?thesis
    unfolding abstract_const_def by simp
qed

lemma CE_equiv_set_derivable_abstract_const_fresh_set:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "c \<notin> consts_of_set T"
  shows "CE_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
    (abstract_const c \<sigma> A)"
proof -
  have "CE_equiv_set_derivable (\<sigma> # \<Gamma>) (abstract_const c \<sigma> ` T)
      (abstract_const c \<sigma> A)"
    using assms(1) by (rule CE_equiv_set_derivable_abstract_const)
  then show ?thesis
    using abstract_const_image_fresh_set[OF assms(2), of \<sigma>] by simp
qed

lemma CE_equiv_set_derivable_abstract_fresh_witness_false:
  assumes "CE_equiv_set_derivable \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)
      ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "CE_equiv_set_derivable (\<sigma> # \<Gamma>)
    (insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)) ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d: "CE_equiv_set_derivable (\<sigma> # \<Gamma>)
      (abstract_const c \<sigma> ` insert ?W T) (abstract_const c \<sigma> ObjFalse)"
    using assms(1) by (rule CE_equiv_set_derivable_abstract_const)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  have image_eq: "abstract_const c \<sigma> ` insert ?W T =
      insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)"
    using abs_T abs_W by simp
  show ?thesis
    using abs_d image_eq by simp
qed

primrec imp_chain :: "oterm list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "imp_chain [] A = A"
| "imp_chain (P # Ps) A = Imp P (imp_chain Ps A)"

lemma imp_chain_type:
  assumes "\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> imp_chain Ps A : Prop"
  using assms
  by (induction Ps) auto

lemma subst_const_imp_chain[simp]:
  "subst_const c \<sigma> N (imp_chain Ps A) =
    imp_chain (map (subst_const c \<sigma> N) Ps) (subst_const c \<sigma> N A)"
  by (induction Ps) auto

lemma rename_imp_chain[simp]:
  "rename r (imp_chain Ps A) = imp_chain (map (rename r) Ps) (rename r A)"
  by (induction Ps) auto

fun conj_prefix :: "oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "conj_prefix P [] = P"
| "conj_prefix P (Q # Ps) = Conj P (conj_prefix Q Ps)"

lemma conj_prefix_type:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<And>Q. Q \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> \<turnstile> conj_prefix P Ps : Prop"
  using assms
proof (induction Ps arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons Q Ps)
  have Q_type: "\<Gamma> \<turnstile> Q : Prop"
    using Cons.prems(2) by simp
  have tail_types: "\<And>R. R \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> R : Prop"
    using Cons.prems(2) by simp
  have "\<Gamma> \<turnstile> conj_prefix Q Ps : Prop"
    using Q_type tail_types by (rule Cons.IH)
  then show ?case
    using Cons.prems(1)
    by (simp add: has_type.Conj)
qed

lemma prop_eval_imp_chain_conj_prefix:
  "prop_eval v (imp_chain (P # Ps) A) =
    prop_eval v (Imp (conj_prefix P Ps) A)"
proof (induction Ps arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons Q Ps)
  then show ?case
    by simp blast
qed

lemma prop_tautology_imp_chain_to_conj_prefix:
  assumes prefix_types:
      "\<And>Q. Q \<in> set (P # Ps) \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (imp_chain (P # Ps) A) (Imp (conj_prefix P Ps) A))"
proof -
  have chain_type: "\<Gamma> \<turnstile> imp_chain (P # Ps) A : Prop"
    using prefix_types A_type by (rule imp_chain_type)
  have P_type: "\<Gamma> \<turnstile> P : Prop"
    using prefix_types by simp
  have tail_types: "\<And>Q. Q \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
    using prefix_types by simp
  have conjunction_type: "\<Gamma> \<turnstile> conj_prefix P Ps : Prop"
    using P_type tail_types by (rule conj_prefix_type)
  have formula_type:
      "\<Gamma> \<turnstile>
        Imp (imp_chain (P # Ps) A) (Imp (conj_prefix P Ps) A) : Prop"
    using chain_type conjunction_type A_type by auto
  have eval:
      "\<forall>v. prop_eval v
        (Imp (imp_chain (P # Ps) A) (Imp (conj_prefix P Ps) A))"
    using prop_eval_imp_chain_conj_prefix[of _ P Ps A]
    by simp
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_conj_prefix_to_imp_chain:
  assumes prefix_types:
      "\<And>Q. Q \<in> set (P # Ps) \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp (conj_prefix P Ps) A) (imp_chain (P # Ps) A))"
proof -
  have chain_type: "\<Gamma> \<turnstile> imp_chain (P # Ps) A : Prop"
    using prefix_types A_type by (rule imp_chain_type)
  have P_type: "\<Gamma> \<turnstile> P : Prop"
    using prefix_types by simp
  have tail_types: "\<And>Q. Q \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
    using prefix_types by simp
  have conjunction_type: "\<Gamma> \<turnstile> conj_prefix P Ps : Prop"
    using P_type tail_types by (rule conj_prefix_type)
  have formula_type:
      "\<Gamma> \<turnstile>
        Imp (Imp (conj_prefix P Ps) A) (imp_chain (P # Ps) A) : Prop"
    using chain_type conjunction_type A_type by auto
  have eval:
      "\<forall>v. prop_eval v
        (Imp (Imp (conj_prefix P Ps) A) (imp_chain (P # Ps) A))"
    using prop_eval_imp_chain_conj_prefix[of _ P Ps A]
    by simp
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

text \<open>
  The previous strengthened local relation internalizes the zero-context
  equivalence rule.  The following auxiliary relation internalizes equivalence
  under a finite implication prefix.  It is intentionally stronger than \<open>CE\<close>;
  its role is diagnostic and structural: it shows the exact conditionalized
  closure that makes the usual deduction argument go through.
\<close>

inductive CE_context_equiv_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  Assumption[intro]:
    "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> CE_context_equiv_set_derivable \<Gamma> T A"
| Theorem[intro]:
    "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> CE_context_equiv_set_derivable \<Gamma> T A"
| Derive_MP[intro]:
    "CE_context_equiv_set_derivable \<Gamma> T A \<Longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> T (Imp A B) \<Longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> T B"
| ContextPropEquivalence[intro]:
    "(\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop) \<Longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> T (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)) \<Longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> T (imp_chain Ps (Eq Prop A B))"

lemma CE_context_equiv_set_derivable_formula:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CE_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CE_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have eq_type: "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using ContextPropEquivalence.hyps(2,3) by auto
  show ?case
    using ContextPropEquivalence.hyps(1) eq_type by (rule imp_chain_type)
qed

lemma CE_context_equiv_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "CE_context_equiv_set_derivable \<Gamma> T A"
  using assms by (rule CE_context_equiv_set_derivable.Theorem)

lemma CE_context_equiv_set_MP:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "CE_context_equiv_set_derivable \<Gamma> T (Imp A B)"
  shows "CE_context_equiv_set_derivable \<Gamma> T B"
  using assms by (rule CE_context_equiv_set_derivable.Derive_MP)

lemma CE_context_equiv_set_derivable_of_CE_equiv:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
  shows "CE_context_equiv_set_derivable \<Gamma> T A"
  using assms
proof (induction rule: CE_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (rule CE_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  show ?case
    using Theorem.hyps(1)
    by (rule CE_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  show ?case
    using Derive_MP.IH(1) Derive_MP.IH(2)
    by (rule CE_context_equiv_set_derivable.Derive_MP)
next
  case (LocalPropEquivalence \<Gamma> A B T)
  have d_iff: "CE_context_equiv_set_derivable \<Gamma> T (imp_chain [] (A \<longleftrightarrow>\<^sub>o B))"
    using LocalPropEquivalence.IH by simp
  have "CE_context_equiv_set_derivable \<Gamma> T (imp_chain [] (Eq Prop A B))"
  proof (rule CE_context_equiv_set_derivable.ContextPropEquivalence
      [where Ps = "[]" and A = A and B = B])
    show "\<And>P. P \<in> set [] \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
      by simp
    show "\<Gamma> \<turnstile> A : Prop"
      using LocalPropEquivalence.hyps(1) .
    show "\<Gamma> \<turnstile> B : Prop"
      using LocalPropEquivalence.hyps(2) .
    show "CE_context_equiv_set_derivable \<Gamma> T (imp_chain [] (A \<longleftrightarrow>\<^sub>o B))"
      using d_iff .
  qed
  then show ?case
    by simp
qed

lemma CE_context_equiv_set_derivable_mono:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "T \<subseteq> U"
  shows "CE_context_equiv_set_derivable \<Gamma> U A"
proof -
  have aux: "\<And>U. T \<subseteq> U \<Longrightarrow> CE_context_equiv_set_derivable \<Gamma> U A"
    using assms(1)
  proof (induction arbitrary: U rule: CE_context_equiv_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    have A_in_U: "A \<in> U"
      using Assumption.hyps(1) Assumption.prems by auto
    show ?case
      using A_in_U Assumption.hyps(2)
      by (rule CE_context_equiv_set_derivable.Assumption)
  next
    case (Theorem \<Gamma> A T)
    show ?case
      using Theorem.hyps
      by (rule CE_context_equiv_set_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> T A B)
    have d_A: "CE_context_equiv_set_derivable \<Gamma> U A"
      using Derive_MP.prems by (rule Derive_MP.IH(1))
    have d_imp: "CE_context_equiv_set_derivable \<Gamma> U (Imp A B)"
      using Derive_MP.prems by (rule Derive_MP.IH(2))
    show ?case
      using d_A d_imp by (rule CE_context_equiv_set_derivable.Derive_MP)
  next
    case (ContextPropEquivalence Ps \<Gamma> A B T)
    have d_iff: "CE_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
      using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
    show ?case
      using ContextPropEquivalence.hyps(1,2,3) d_iff
      by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
  qed
  show ?thesis
    using assms(2) by (rule aux)
qed

lemma CE_context_equiv_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "CE_context_equiv_set_derivable \<Gamma> T B"
  shows "CE_context_equiv_set_derivable \<Gamma> T (Imp A B)"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CE_context_equiv_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp B (Imp A B)"
    using assms(1) B_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_imp_of_right)
  have d_taut: "CE_context_equiv_set_derivable \<Gamma> T (Imp B (Imp A B))"
    using taut by (rule CE_context_equiv_set_Theorem)
  show ?thesis
    using assms(2) d_taut by (rule CE_context_equiv_set_MP)
qed

lemma CE_context_equiv_set_derivable_deduction:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and d: "CE_context_equiv_set_derivable \<Gamma> (insert X T) B"
  shows "CE_context_equiv_set_derivable \<Gamma> T (Imp X B)"
proof -
  have aux: "\<And>Y S. \<Gamma> \<turnstile> Y : Prop \<Longrightarrow>
      insert X T \<subseteq> insert Y S \<Longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> S (Imp Y B)"
    using d
  proof (induction rule: CE_context_equiv_set_derivable.induct)
    case (Assumption B U \<Gamma>)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Assumption.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using Assumption.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps(2) .
    show ?case
    proof (cases "B = Y")
      case True
      have h_self: "\<Gamma> \<turnstile>\<^sub>H Imp Y Y"
        using Y_type by (rule H_imp_self)
      have c_self: "\<Gamma> \<turnstile>\<^sub>C Imp Y Y"
        using h_self by (rule C_proves.H)
      have ce_self: "\<Gamma> \<turnstile>\<^sub>CE Imp Y Y"
        using c_self by (rule CE_proves.C)
      have d_self: "CE_context_equiv_set_derivable \<Gamma> S (Imp Y Y)"
        using ce_self by (rule CE_context_equiv_set_derivable.Theorem)
      show ?thesis
        using d_self True by simp
    next
      case False
      have B_in_S: "B \<in> S"
        using Assumption.hyps(1) U_sub False by blast
      have d_B: "CE_context_equiv_set_derivable \<Gamma> S B"
        using B_in_S B_type by (rule CE_context_equiv_set_derivable.Assumption)
      show ?thesis
        using Y_type d_B by (rule CE_context_equiv_proves_imp_of_right)
    qed
  next
    case (Theorem \<Gamma> B U)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Theorem.prems by blast
    have ce_imp: "\<Gamma> \<turnstile>\<^sub>CE Imp Y B"
      using Y_type Theorem.hyps by (rule CE_proves_imp_of_right)
    show ?case
      using ce_imp by (rule CE_context_equiv_set_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> U B C)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Derive_MP.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using Derive_MP.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule CE_context_equiv_set_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2)
      by (auto dest: CE_context_equiv_set_derivable_formula elim: has_type.cases)
    have taut: "\<Gamma> \<turnstile>\<^sub>CE
        Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using Y_type B_type C_type
      by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_deduction_mp)
    have d_taut: "CE_context_equiv_set_derivable \<Gamma> S
        (Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C)))"
      using taut by (rule CE_context_equiv_set_derivable.Theorem)
    have IH_B: "CE_context_equiv_set_derivable \<Gamma> S (Imp Y B)"
      using Y_type U_sub by (rule Derive_MP.IH(1))
    have IH_imp: "CE_context_equiv_set_derivable \<Gamma> S (Imp Y (Imp B C))"
      using Y_type U_sub by (rule Derive_MP.IH(2))
    have step: "CE_context_equiv_set_derivable \<Gamma> S
        (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using IH_B d_taut by (rule CE_context_equiv_set_derivable.Derive_MP)
    show ?case
      using IH_imp step by (rule CE_context_equiv_set_derivable.Derive_MP)
  next
    case (ContextPropEquivalence Ps \<Gamma> A C U)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using ContextPropEquivalence.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using ContextPropEquivalence.prems by blast
    have d_cond_raw: "CE_context_equiv_set_derivable \<Gamma> S
        (Imp Y (imp_chain Ps (A \<longleftrightarrow>\<^sub>o C)))"
      using Y_type U_sub by (rule ContextPropEquivalence.IH)
    then have d_cond: "CE_context_equiv_set_derivable \<Gamma> S
        (imp_chain (Y # Ps) (A \<longleftrightarrow>\<^sub>o C))"
      by simp
    have typed_prefix: "\<And>P. P \<in> set (Y # Ps) \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
      using Y_type ContextPropEquivalence.hyps(1) by auto
    have d_eq: "CE_context_equiv_set_derivable \<Gamma> S
        (imp_chain (Y # Ps) (Eq Prop A C))"
      using typed_prefix ContextPropEquivalence.hyps(2,3) d_cond
      by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
    show ?case
      using d_eq by simp
  qed
  show ?thesis
    using assms(1) by (rule aux) blast
qed

lemma CE_context_equiv_set_derivable_finite_support:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
  obtains U where "finite U" and "U \<subseteq> T" and
    "CE_context_equiv_set_derivable \<Gamma> U A"
proof -
  have "\<exists>U. finite U \<and> U \<subseteq> T \<and>
      CE_context_equiv_set_derivable \<Gamma> U A"
    using assms
  proof (induction rule: CE_context_equiv_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> A T)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (Derive_MP \<Gamma> T A B)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_A: "CE_context_equiv_set_derivable \<Gamma> U A"
      using Derive_MP.IH(1) by auto
    obtain V where V_fin: "finite V" and V_sub: "V \<subseteq> T"
      and V_imp: "CE_context_equiv_set_derivable \<Gamma> V (Imp A B)"
      using Derive_MP.IH(2) by auto
    have A_der: "CE_context_equiv_set_derivable \<Gamma> (U \<union> V) A"
      using U_A by (rule CE_context_equiv_set_derivable_mono) auto
    have imp_der: "CE_context_equiv_set_derivable \<Gamma> (U \<union> V) (Imp A B)"
      using V_imp by (rule CE_context_equiv_set_derivable_mono) auto
    have B_der: "CE_context_equiv_set_derivable \<Gamma> (U \<union> V) B"
      using A_der imp_der by (rule CE_context_equiv_set_derivable.Derive_MP)
    show ?case
      using U_fin U_sub V_fin V_sub B_der by (intro exI[of _ "U \<union> V"]) auto
  next
    case (ContextPropEquivalence Ps \<Gamma> A B T)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_iff: "CE_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
      using ContextPropEquivalence.IH by auto
    have eq_der: "CE_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (Eq Prop A B))"
      using ContextPropEquivalence.hyps(1,2,3) U_iff
      by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
    show ?case
      using U_fin U_sub eq_der by blast
  qed
  then show ?thesis
    using that by blast
qed

lemma CE_context_equiv_set_derivable_subst_const:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
    (subst_const c \<sigma> N A)"
  using assms
proof (induction rule: CE_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule subst_const_preserves_typing)
  have "subst_const c \<sigma> N A \<in> subst_const c \<sigma> N ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_sub_type by (rule CE_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule CE_proves_subst_const)
  then show ?case
    by (rule CE_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N A)"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N (Imp A B))"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B))"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CE_context_equiv_set_derivable.Derive_MP)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have typed_prefix:
      "\<And>P. P \<in> set (map (subst_const c \<sigma> N) Ps) \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set (map (subst_const c \<sigma> N) Ps)"
    then obtain Q where Q_in: "Q \<in> set Ps" and P_def: "P = subst_const c \<sigma> N Q"
      by auto
    have "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
      using ContextPropEquivalence.hyps(1)[OF Q_in] ContextPropEquivalence.prems
      by (rule subst_const_preserves_typing)
    then show "\<Gamma> \<turnstile> P : Prop"
      using P_def by simp
  qed
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using ContextPropEquivalence.hyps(2) ContextPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using ContextPropEquivalence.hyps(3) ContextPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_iff_raw: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (subst_const c \<sigma> N (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)))"
    using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
  have d_iff: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (imp_chain (map (subst_const c \<sigma> N) Ps)
        (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o subst_const c \<sigma> N B))"
    using d_iff_raw by simp
  have d_eq: "CE_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
      (imp_chain (map (subst_const c \<sigma> N) Ps)
        (Eq Prop (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)))"
    using typed_prefix A_sub_type B_sub_type d_iff
    by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
  then show ?case
    by simp
qed

lemma CE_context_equiv_set_derivable_rename:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "CE_context_equiv_set_derivable \<Delta> (rename r ` T) (rename r A)"
  using assms
proof (induction arbitrary: \<Delta> r rule: CE_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using Assumption.hyps(2) Assumption.prems by (rule renaming_preserves_typing)
  have "rename r A \<in> rename r ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_ren_type by (rule CE_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<Delta> \<turnstile>\<^sub>CE rename r A"
    using Theorem.hyps Theorem.prems by (rule CE_proves_rename)
  then show ?case
    by (rule CE_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A: "CE_context_equiv_set_derivable \<Delta> (rename r ` T) (rename r A)"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw: "CE_context_equiv_set_derivable \<Delta> (rename r ` T)
      (rename r (Imp A B))"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp: "CE_context_equiv_set_derivable \<Delta> (rename r ` T)
      (Imp (rename r A) (rename r B))"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CE_context_equiv_set_derivable.Derive_MP)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have typed_prefix:
      "\<And>P. P \<in> set (map (rename r) Ps) \<Longrightarrow> \<Delta> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set (map (rename r) Ps)"
    then obtain Q where Q_in: "Q \<in> set Ps" and P_def: "P = rename r Q"
      by auto
    have "\<Delta> \<turnstile> rename r Q : Prop"
      using ContextPropEquivalence.hyps(1)[OF Q_in] ContextPropEquivalence.prems
      by (rule renaming_preserves_typing)
    then show "\<Delta> \<turnstile> P : Prop"
      using P_def by simp
  qed
  have A_ren_type: "\<Delta> \<turnstile> rename r A : Prop"
    using ContextPropEquivalence.hyps(2) ContextPropEquivalence.prems
    by (rule renaming_preserves_typing)
  have B_ren_type: "\<Delta> \<turnstile> rename r B : Prop"
    using ContextPropEquivalence.hyps(3) ContextPropEquivalence.prems
    by (rule renaming_preserves_typing)
  have d_iff_raw: "CE_context_equiv_set_derivable \<Delta> (rename r ` T)
      (rename r (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)))"
    using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
  have d_iff: "CE_context_equiv_set_derivable \<Delta> (rename r ` T)
      (imp_chain (map (rename r) Ps) (rename r A \<longleftrightarrow>\<^sub>o rename r B))"
    using d_iff_raw by simp
  have d_eq: "CE_context_equiv_set_derivable \<Delta> (rename r ` T)
      (imp_chain (map (rename r) Ps) (Eq Prop (rename r A) (rename r B)))"
    using typed_prefix A_ren_type B_ren_type d_iff
    by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
  then show ?case
    by simp
qed

lemma CE_context_equiv_set_derivable_shift:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
  shows "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T) (shift A)"
  unfolding shift_def
  using assms by (rule CE_context_equiv_set_derivable_rename) auto

lemma CE_context_equiv_set_derivable_abstract_const:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
  shows "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (abstract_const c \<sigma> ` T)
    (abstract_const c \<sigma> A)"
proof -
  have shifted: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T) (shift A)"
    using assms by (rule CE_context_equiv_set_derivable_shift)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (subst_const c \<sigma> (Var 0) ` (shift ` T))
      (subst_const c \<sigma> (Var 0) (shift A))"
    using shifted var_type by (rule CE_context_equiv_set_derivable_subst_const)
  moreover have "subst_const c \<sigma> (Var 0) ` (shift ` T) =
      abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  ultimately show ?thesis
    unfolding abstract_const_def by simp
qed

lemma CE_context_equiv_set_derivable_abstract_const_fresh_set:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "c \<notin> consts_of_set T"
  shows "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
    (abstract_const c \<sigma> A)"
proof -
  have "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (abstract_const c \<sigma> ` T)
      (abstract_const c \<sigma> A)"
    using assms(1) by (rule CE_context_equiv_set_derivable_abstract_const)
  then show ?thesis
    using abstract_const_image_fresh_set[OF assms(2), of \<sigma>] by simp
qed

lemma CE_context_equiv_set_derivable_abstract_fresh_witness_false:
  assumes "CE_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>)
    (insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)) ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (abstract_const c \<sigma> ` insert ?W T) (abstract_const c \<sigma> ObjFalse)"
    using assms(1) by (rule CE_context_equiv_set_derivable_abstract_const)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  have image_eq: "abstract_const c \<sigma> ` insert ?W T =
      insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)"
    using abs_T abs_W by simp
  show ?thesis
    using abs_d image_eq by simp
qed

definition CE_context_equiv_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_context_equiv_consistent \<Gamma> T \<longleftrightarrow>
    \<not> CE_context_equiv_set_derivable \<Gamma> T ObjFalse"

lemma CE_context_equiv_consistentD:
  assumes "CE_context_equiv_consistent \<Gamma> T"
  shows "\<not> CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
  using assms unfolding CE_context_equiv_consistent_def by blast

lemma CE_context_equiv_consistent_mono:
  assumes "CE_context_equiv_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "CE_context_equiv_consistent \<Gamma> T"
  using assms CE_context_equiv_set_derivable_mono
  unfolding CE_context_equiv_consistent_def by blast

lemma CE_context_equiv_consistent_singleton_neg_of_not_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_context_equiv_set_derivable \<Gamma> {} A"
  shows "CE_context_equiv_consistent \<Gamma> {Neg A}"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d_false: "CE_context_equiv_set_derivable \<Gamma> {Neg A} ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> {} (Imp (Neg A) ObjFalse)"
    using neg_type d_false by (rule CE_context_equiv_set_derivable_deduction)
  have d_A_thm: "CE_context_equiv_set_derivable \<Gamma> {}
      (Imp (Imp (Neg A) ObjFalse) A)"
    using CE_proves_imp_neg_false_to_formula[OF assms(1)]
    by (rule CE_context_equiv_set_Theorem)
  have "CE_context_equiv_set_derivable \<Gamma> {} A"
    using d_imp_false d_A_thm by (rule CE_context_equiv_set_MP)
  then show False
    using assms(2) by blast
qed

lemma CE_context_equiv_set_derives_ObjFalse_of_formula_and_neg:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "Neg A \<in> T"
  shows "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CE_context_equiv_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp A (Imp (Neg A) ObjFalse))"
    using taut by (rule CE_context_equiv_set_Theorem)
  have d_neg: "CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using assms(2) neg_type by (rule CE_context_equiv_set_derivable.Assumption)
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Neg A) ObjFalse)"
    using assms(1) d_taut by (rule CE_context_equiv_set_MP)
  show ?thesis
    using d_neg d_imp_false by (rule CE_context_equiv_set_MP)
qed

lemma CE_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "CE_context_equiv_set_derivable \<Gamma> T A"
    and "CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
  shows "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CE_context_equiv_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp A (Imp (Neg A) ObjFalse))"
    using taut by (rule CE_context_equiv_set_Theorem)
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Neg A) ObjFalse)"
    using assms(1) d_taut by (rule CE_context_equiv_set_MP)
  show ?thesis
    using assms(2) d_imp_false by (rule CE_context_equiv_set_MP)
qed

lemma CE_context_equiv_consistent_not_both_derivable:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "CE_context_equiv_set_derivable \<Gamma> T A"
  shows "\<not> CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
proof
  assume d_neg: "CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
  have "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using assms(2) d_neg
    by (rule CE_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding CE_context_equiv_consistent_def by blast
qed

lemma CE_context_equiv_consistent_not_derives_with_neg:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> CE_context_equiv_set_derivable \<Gamma> T A"
proof
  assume "CE_context_equiv_set_derivable \<Gamma> T A"
  then have "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using assms(2) by (rule CE_context_equiv_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding CE_context_equiv_consistent_def by blast
qed

lemma CE_context_equiv_consistent_insert_formula_if_not_neg_derivable:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
  shows "CE_context_equiv_consistent \<Gamma> (insert A T)"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d_false: "CE_context_equiv_set_derivable \<Gamma> (insert A T) ObjFalse"
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> T (Imp A ObjFalse)"
    using assms(2) d_false by (rule CE_context_equiv_set_derivable_deduction)
  have d_neg_thm: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp A ObjFalse) (Neg A))"
    using CE_proves_imp_false_to_neg[OF assms(2)]
    by (rule CE_context_equiv_set_Theorem)
  have "CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using d_imp_false d_neg_thm by (rule CE_context_equiv_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CE_context_equiv_consistent_insert_neg_if_not_derivable:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_context_equiv_set_derivable \<Gamma> T A"
  shows "CE_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d_false: "CE_context_equiv_set_derivable \<Gamma> (insert (Neg A) T) ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Neg A) ObjFalse)"
    using neg_type d_false by (rule CE_context_equiv_set_derivable_deduction)
  have d_A_thm: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp (Neg A) ObjFalse) A)"
    using CE_proves_imp_neg_false_to_formula[OF assms(2)]
    by (rule CE_context_equiv_set_Theorem)
  have "CE_context_equiv_set_derivable \<Gamma> T A"
    using d_imp_false d_A_thm by (rule CE_context_equiv_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CE_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_context_equiv_consistent \<Gamma> (insert A T)"
  shows "CE_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have d_false: "CE_context_equiv_set_derivable \<Gamma> (insert A T) ObjFalse"
    using assms(3) unfolding CE_context_equiv_consistent_def by blast
  have d_imp_false: "CE_context_equiv_set_derivable \<Gamma> T (Imp A ObjFalse)"
    using assms(2) d_false by (rule CE_context_equiv_set_derivable_deduction)
  have d_neg_thm: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp A ObjFalse) (Neg A))"
    using CE_proves_imp_false_to_neg[OF assms(2)]
    by (rule CE_context_equiv_set_Theorem)
  have d_neg: "CE_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using d_imp_false d_neg_thm by (rule CE_context_equiv_set_MP)
  have not_d_A: "\<not> CE_context_equiv_set_derivable \<Gamma> T A"
  proof
    assume d_A: "CE_context_equiv_set_derivable \<Gamma> T A"
    have "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
      using d_A d_neg
      by (rule CE_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding CE_context_equiv_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A
    by (rule CE_context_equiv_consistent_insert_neg_if_not_derivable)
qed

lemma CE_context_equiv_consistent_decidable_extension:
  assumes "CE_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "CE_context_equiv_consistent \<Gamma> (insert A T) \<or>
    CE_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "CE_context_equiv_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis
    by blast
next
  case False
  have "CE_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
    using assms False
    by (rule CE_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis
    by blast
qed

text \<open>
  This is the precise instantiation-lowering principle needed to preserve
  consistency when fresh Henkin witnesses are added for the context-prefix
  equivalence relation.  The antecedent is the shifted derivation obtained after
  abstracting away a fresh witness constant; the consequent is the original
  context derivation needed to contradict consistency before the witness was
  inserted.
\<close>

definition CE_context_equiv_shifted_inst_admissible :: bool where
  "CE_context_equiv_shifted_inst_admissible \<longleftrightarrow>
    (\<forall>\<Gamma> T \<sigma> P Q. typed_theory \<Gamma> T \<longrightarrow>
      CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T) (Imp P (shift Q)) \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      CE_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q))"

lemma CE_context_equiv_set_derivable_fresh_witness_eigen_imp_false:
  assumes "CE_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
    (Imp (Imp (shift (Exists \<sigma> A)) A) ObjFalse)"
proof -
  let ?E = "Imp (shift (Exists \<sigma> A)) A"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(4) by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have E_type: "\<sigma> # \<Gamma> \<turnstile> ?E : Prop"
    using shifted_exists_type assms(4) by auto
  have d_false: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (insert ?E (shift ` T)) ObjFalse"
    using assms(1,2,3)
    by (rule CE_context_equiv_set_derivable_abstract_fresh_witness_false)
  show ?thesis
    using E_type d_false by (rule CE_context_equiv_set_derivable_deduction)
qed

lemma CE_context_equiv_set_derivable_fresh_witness_false:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and typed: "typed_theory \<Gamma> T"
    and d: "CE_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_imp_false: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp ?P ObjFalse)"
    using d fresh_T fresh_A A_type
    by (rule CE_context_equiv_set_derivable_fresh_witness_eigen_imp_false)
  have d_imp_shift_false: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp ?P (shift ObjFalse))"
    using d_imp_false by simp
  have lower: "CE_context_equiv_set_derivable \<Gamma> T (Imp ?Q ObjFalse)"
    using inst typed d_imp_shift_false P_type typed_ObjFalse
    unfolding CE_context_equiv_shifted_inst_admissible_def by blast
  have c_Q: "\<Gamma> \<turnstile>\<^sub>C ?Q"
    using A_type by (rule C_proves_exists_imp_shift_exists)
  have ce_Q: "\<Gamma> \<turnstile>\<^sub>CE ?Q"
    using c_Q by (rule CE_proves.C)
  have d_Q: "CE_context_equiv_set_derivable \<Gamma> T ?Q"
    using ce_Q by (rule CE_context_equiv_set_Theorem)
  show ?thesis
    using d_Q lower by (rule CE_context_equiv_set_MP)
qed

lemma CE_context_equiv_consistent_insert_fresh_witness_axiom:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_context_equiv_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CE_context_equiv_consistent \<Gamma>
    (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d: "CE_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
  have "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using inst typed d fresh_T fresh_A A_type
    by (rule CE_context_equiv_set_derivable_fresh_witness_false)
  then show False
    using consistent unfolding CE_context_equiv_consistent_def by blast
qed

lemma CE_context_equiv_staged_henkin_step_consistent:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CE_context_equiv_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using inst typed consistent fresh_T fresh_A True
      by (rule CE_context_equiv_consistent_insert_fresh_witness_axiom)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma CE_context_equiv_staged_henkin_chain_consistent:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(2) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(3) by (rule staged_henkin_chain_typed)
  have consistent_n: "CE_context_equiv_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1) finite_n typed_n consistent_n
    by (simp add: CE_context_equiv_staged_henkin_step_consistent)
qed

lemma CE_context_equiv_staged_henkin_extension_consistent:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d_false: "CE_context_equiv_set_derivable \<Gamma>
      (staged_henkin_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "CE_context_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CE_context_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  have "\<exists>n. U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    by blast
  have "CE_context_equiv_set_derivable \<Gamma> (staged_henkin_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CE_context_equiv_set_derivable_mono)
  moreover have "CE_context_equiv_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule CE_context_equiv_staged_henkin_chain_consistent)
  ultimately show False
    unfolding CE_context_equiv_consistent_def by blast
qed

definition CE_equiv_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_equiv_consistent \<Gamma> T \<longleftrightarrow> \<not> CE_equiv_set_derivable \<Gamma> T ObjFalse"

lemma CE_equiv_consistentD:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "\<not> CE_equiv_set_derivable \<Gamma> T ObjFalse"
  using assms unfolding CE_equiv_consistent_def by blast

lemma CE_consistent_of_CE_equiv_consistent:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> T"
proof (unfold CE_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  then have "CE_equiv_set_derivable \<Gamma> T ObjFalse"
    by (rule CE_equiv_set_derivable_of_CE_set_derivable)
  then show False
    using assms unfolding CE_equiv_consistent_def by blast
qed

lemma CE_equiv_consistent_of_CE_context_equiv_consistent:
  assumes "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_equiv_consistent \<Gamma> T"
proof (unfold CE_equiv_consistent_def, intro notI)
  assume "CE_equiv_set_derivable \<Gamma> T ObjFalse"
  then have "CE_context_equiv_set_derivable \<Gamma> T ObjFalse"
    by (rule CE_context_equiv_set_derivable_of_CE_equiv)
  then show False
    using assms unfolding CE_context_equiv_consistent_def by blast
qed

definition CE_equiv_locally_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_equiv_locally_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> CE_equiv_consistent \<Gamma> T \<and> CE_negation_complete \<Gamma> T"

definition CE_context_equiv_locally_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_context_equiv_locally_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> CE_context_equiv_consistent \<Gamma> T \<and>
    CE_negation_complete \<Gamma> T"

lemma CE_equiv_locally_maximal_consistent_of_CE_context_equiv:
  assumes "CE_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_equiv_locally_maximal_consistent \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using assms unfolding CE_context_equiv_locally_maximal_consistent_def by blast
  have context_consistent: "CE_context_equiv_consistent \<Gamma> T"
    using assms unfolding CE_context_equiv_locally_maximal_consistent_def by blast
  have equiv_consistent: "CE_equiv_consistent \<Gamma> T"
    using context_consistent by (rule CE_equiv_consistent_of_CE_context_equiv_consistent)
  have complete: "CE_negation_complete \<Gamma> T"
    using assms unfolding CE_context_equiv_locally_maximal_consistent_def by blast
  show ?thesis
    using typed equiv_consistent complete
    unfolding CE_equiv_locally_maximal_consistent_def by blast
qed

definition CE_context_equiv_lindenbaum_step ::
    "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CE_context_equiv_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if CE_context_equiv_consistent \<Gamma> (insert A T) then insert A T
       else insert (Neg A) T)
     else T)"

primrec CE_context_equiv_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CE_context_equiv_lindenbaum_chain \<Gamma> T enum 0 = T"
| "CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) =
    CE_context_equiv_lindenbaum_step \<Gamma> (enum n)
      (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"

definition CE_context_equiv_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "CE_context_equiv_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"

lemma CE_context_equiv_lindenbaum_step_extends:
  "T \<subseteq> CE_context_equiv_lindenbaum_step \<Gamma> A T"
  unfolding CE_context_equiv_lindenbaum_step_def by auto

lemma CE_context_equiv_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_context_equiv_lindenbaum_step \<Gamma> A T)"
  using assms unfolding CE_context_equiv_lindenbaum_step_def typed_theory_def by auto

lemma CE_context_equiv_lindenbaum_step_consistent:
  assumes "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma> (CE_context_equiv_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding CE_context_equiv_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "CE_context_equiv_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close>
      unfolding CE_context_equiv_lindenbaum_step_def by simp
  next
    case False
    have "CE_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule CE_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      unfolding CE_context_equiv_lindenbaum_step_def by simp
  qed
qed

lemma CE_context_equiv_lindenbaum_chain_step:
  "CE_context_equiv_lindenbaum_chain \<Gamma> T enum n \<subseteq>
    CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using CE_context_equiv_lindenbaum_step_extends[of
      "CE_context_equiv_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma CE_context_equiv_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_context_equiv_lindenbaum_step_typed)
qed

lemma CE_context_equiv_lindenbaum_chain_consistent:
  assumes "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma>
    (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_context_equiv_lindenbaum_step_consistent)
qed

lemma CE_context_equiv_lindenbaum_extension_extends:
  "T \<subseteq> CE_context_equiv_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> CE_context_equiv_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> CE_context_equiv_lindenbaum_extension \<Gamma> T enum"
    unfolding CE_context_equiv_lindenbaum_extension_def by blast
qed

lemma CE_context_equiv_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CE_context_equiv_lindenbaum_chain_typed)
  then show ?thesis
    unfolding CE_context_equiv_lindenbaum_extension_def by (rule typed_theory_nat_union)
qed

lemma CE_context_equiv_lindenbaum_extension_consistent:
  assumes "CE_context_equiv_consistent \<Gamma> T"
  shows "CE_context_equiv_consistent \<Gamma>
    (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CE_context_equiv_consistent_def, intro notI)
  assume d_false: "CE_context_equiv_set_derivable \<Gamma>
      (CE_context_equiv_lindenbaum_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CE_context_equiv_lindenbaum_extension \<Gamma> T enum"
    and d_U: "CE_context_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CE_context_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding CE_context_equiv_lindenbaum_extension_def .
  have step: "\<And>n. CE_context_equiv_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule CE_context_equiv_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> CE_context_equiv_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain:
      "U \<subseteq> CE_context_equiv_lindenbaum_chain \<Gamma> T enum n"
    by blast
  have "CE_context_equiv_set_derivable \<Gamma>
      (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CE_context_equiv_set_derivable_mono)
  moreover have "CE_context_equiv_consistent \<Gamma>
      (CE_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CE_context_equiv_lindenbaum_chain_consistent)
  ultimately show False
    unfolding CE_context_equiv_consistent_def by blast
qed

lemma CE_context_equiv_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "CE_negation_complete \<Gamma>
    (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CE_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "CE_context_equiv_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) =
      CE_context_equiv_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> CE_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "CE_context_equiv_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> CE_context_equiv_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding CE_context_equiv_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> CE_context_equiv_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding CE_context_equiv_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> CE_context_equiv_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> CE_context_equiv_lindenbaum_extension \<Gamma> T enum"
    unfolding CE_context_equiv_lindenbaum_extension_def by blast
qed

theorem CE_context_equiv_lindenbaum_extension_locally_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "CE_context_equiv_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "CE_context_equiv_locally_maximal_consistent \<Gamma>
    (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule CE_context_equiv_lindenbaum_extension_typed)
  have consistent: "CE_context_equiv_consistent \<Gamma>
      (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule CE_context_equiv_lindenbaum_extension_consistent)
  have complete: "CE_negation_complete \<Gamma>
      (CE_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule CE_context_equiv_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CE_context_equiv_locally_maximal_consistent_def by simp
qed

theorem CE_context_equiv_locally_maximal_extension_exists:
  assumes "typed_theory \<Gamma> T"
    and "CE_context_equiv_consistent \<Gamma> T"
  shows "\<exists>U. T \<subseteq> U \<and> CE_context_equiv_locally_maximal_consistent \<Gamma> U"
proof -
  obtain enum where enum: "enumerates_formulas \<Gamma> enum"
    using enumerates_formulas_exists by blast
  let ?U = "CE_context_equiv_lindenbaum_extension \<Gamma> T enum"
  have sub: "T \<subseteq> ?U"
    by (rule CE_context_equiv_lindenbaum_extension_extends)
  have local: "CE_context_equiv_locally_maximal_consistent \<Gamma> ?U"
    using assms enum by (rule CE_context_equiv_lindenbaum_extension_locally_maximal_consistent)
  show ?thesis
    using sub local by blast
qed

theorem CE_context_equiv_locally_maximal_countermodel_extension:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CE_context_equiv_set_derivable \<Gamma> {} A"
  shows "\<exists>T. CE_context_equiv_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T"
proof -
  have typed: "typed_theory \<Gamma> {Neg A}"
    using assms(1) unfolding typed_theory_def by auto
  have consistent: "CE_context_equiv_consistent \<Gamma> {Neg A}"
    using assms by (rule CE_context_equiv_consistent_singleton_neg_of_not_derivable)
  obtain T where sub: "{Neg A} \<subseteq> T"
    and local: "CE_context_equiv_locally_maximal_consistent \<Gamma> T"
    using CE_context_equiv_locally_maximal_extension_exists[OF typed consistent] by blast
  have neg_in: "Neg A \<in> T"
    using sub by blast
  show ?thesis
    using local neg_in by blast
qed

definition CE_context_equiv_conservative :: bool where
  "CE_context_equiv_conservative \<longleftrightarrow>
    (\<forall>\<Gamma> A. CE_context_equiv_set_derivable \<Gamma> {} A \<longrightarrow> \<Gamma> \<turnstile>\<^sub>CE A)"

definition CE_prefix_equivalence_internalized :: bool where
  "CE_prefix_equivalence_internalized \<longleftrightarrow>
    (\<forall>\<Gamma> Ps A B.
      (\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop) \<longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (A \<longleftrightarrow>\<^sub>o B) \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (Eq Prop A B))"

definition CE_nonempty_prefix_equivalence_internalized :: bool where
  "CE_nonempty_prefix_equivalence_internalized \<longleftrightarrow>
    (\<forall>\<Gamma> P Ps A B.
      (\<forall>R \<in> set (P # Ps). \<Gamma> \<turnstile> R : Prop) \<longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CE imp_chain (P # Ps) (A \<longleftrightarrow>\<^sub>o B) \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CE imp_chain (P # Ps) (Eq Prop A B))"

lemma CE_prefix_equivalence_internalized_if_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_prefix_equivalence_internalized"
proof (unfold CE_prefix_equivalence_internalized_def, intro allI impI)
  fix \<Gamma> Ps A B
  assume typed_prefix: "\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_iff: "\<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
  show "\<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (Eq Prop A B)"
  proof (cases Ps)
    case Nil
    have d_iff': "\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o B)"
      using d_iff Nil by simp
    have "\<Gamma> \<turnstile>\<^sub>CE Eq Prop A B"
      using A_type B_type d_iff' by (rule CE_proves.PropEquivalence)
    then show ?thesis
      using Nil by simp
  next
    case (Cons P Ps')
    have typed_nonempty: "\<forall>R \<in> set (P # Ps'). \<Gamma> \<turnstile> R : Prop"
      using typed_prefix Cons by simp
    show ?thesis
      using nonempty typed_nonempty A_type B_type d_iff Cons
      unfolding CE_nonempty_prefix_equivalence_internalized_def by blast
  qed
qed

lemma CE_nonempty_prefix_equivalence_internalized_if_prefix:
  assumes prefix: "CE_prefix_equivalence_internalized"
  shows "CE_nonempty_prefix_equivalence_internalized"
  using prefix unfolding CE_prefix_equivalence_internalized_def
    CE_nonempty_prefix_equivalence_internalized_def by blast

theorem CE_prefix_equivalence_internalized_iff_nonempty_prefix:
  "CE_prefix_equivalence_internalized \<longleftrightarrow>
    CE_nonempty_prefix_equivalence_internalized"
  using CE_prefix_equivalence_internalized_if_nonempty_prefix
    CE_nonempty_prefix_equivalence_internalized_if_prefix by blast

lemma CE_prefix_equivalence_internalized_if_context_conservative:
  assumes conservative: "CE_context_equiv_conservative"
  shows "CE_prefix_equivalence_internalized"
proof (unfold CE_prefix_equivalence_internalized_def, intro allI impI)
  fix \<Gamma> Ps A B
  assume typed_prefix: "\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_iff: "\<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
  have d_context_iff: "CE_context_equiv_set_derivable \<Gamma> {}
      (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
    using d_iff by (rule CE_context_equiv_set_derivable.Theorem)
  have typed_prefix': "\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    using typed_prefix by blast
  have d_context_eq: "CE_context_equiv_set_derivable \<Gamma> {}
      (imp_chain Ps (Eq Prop A B))"
    using typed_prefix' A_type B_type d_context_iff
    by (rule CE_context_equiv_set_derivable.ContextPropEquivalence)
  show "\<Gamma> \<turnstile>\<^sub>CE imp_chain Ps (Eq Prop A B)"
    using conservative d_context_eq
    unfolding CE_context_equiv_conservative_def by blast
qed

lemma CE_context_equiv_conservative_if_prefix_equivalence_internalized:
  assumes prefix: "CE_prefix_equivalence_internalized"
  shows "CE_context_equiv_conservative"
proof (unfold CE_context_equiv_conservative_def, intro allI impI)
  fix \<Gamma> A
  assume d: "CE_context_equiv_set_derivable \<Gamma> {} A"
  have aux: "\<And>\<Delta> T B. CE_context_equiv_set_derivable \<Delta> T B \<Longrightarrow>
      T = {} \<Longrightarrow> \<Delta> \<turnstile>\<^sub>CE B"
  proof -
    fix \<Delta> T B
    assume dB: "CE_context_equiv_set_derivable \<Delta> T B"
    then show "T = {} \<Longrightarrow> \<Delta> \<turnstile>\<^sub>CE B"
    proof (induction rule: CE_context_equiv_set_derivable.induct)
      case (Assumption B T \<Delta>)
      then show ?case
        by simp
    next
      case (Theorem \<Delta> B T)
      then show ?case
        by simp
    next
      case (Derive_MP \<Delta> T B C)
      have d_B: "\<Delta> \<turnstile>\<^sub>CE B"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have d_imp: "\<Delta> \<turnstile>\<^sub>CE Imp B C"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using d_B d_imp by (rule CE_proves.MP)
    next
      case (ContextPropEquivalence Ps \<Delta> B C T)
      have d_iff: "\<Delta> \<turnstile>\<^sub>CE imp_chain Ps (B \<longleftrightarrow>\<^sub>o C)"
        using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
      show ?case
        using prefix ContextPropEquivalence.hyps(1,2,3) d_iff
        unfolding CE_prefix_equivalence_internalized_def by blast
    qed
  qed
  show "\<Gamma> \<turnstile>\<^sub>CE A"
    using d by (rule aux) simp
qed

theorem CE_context_equiv_conservative_iff_prefix_equivalence_internalized:
  "CE_context_equiv_conservative \<longleftrightarrow> CE_prefix_equivalence_internalized"
  using CE_context_equiv_conservative_if_prefix_equivalence_internalized
    CE_prefix_equivalence_internalized_if_context_conservative by blast

lemma CE_context_equiv_set_derivable_shifted_inst_finite:
  assumes conservative: "CE_context_equiv_conservative"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and d: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift Q))"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "CE_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q)"
  using finite_T typed d Q_type
proof (induction T arbitrary: Q rule: finite_induct)
  case empty
  have d_empty: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) {}
      (Imp P (shift Q))"
    using empty.prems(2) by simp
  have ce_imp: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q)"
    using conservative d_empty
    unfolding CE_context_equiv_conservative_def by blast
  have inst: "\<Gamma> \<turnstile>\<^sub>CE Imp (Exists \<sigma> P) Q"
    using P_type empty.prems(3) ce_imp by (rule CE_proves.Inst)
  then show ?case
    by (rule CE_context_equiv_set_Theorem)
next
  case (insert A T)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using insert.prems(1) unfolding typed_theory_def by auto
  have typed_T: "typed_theory \<Gamma> T"
    using insert.prems(1) unfolding typed_theory_def by auto
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using insert.prems(3) by (rule weakening_front)
  have d_insert: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (insert (shift A) (shift ` T)) (Imp P (shift Q))"
    using insert.prems(2) by simp
  have d_deduct: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp (shift A) (Imp P (shift Q)))"
    using shift_A_type d_insert by (rule CE_context_equiv_set_derivable_deduction)
  have taut: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_swap_imp)
  have d_taut: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q))))"
    using taut by (rule CE_context_equiv_set_Theorem)
  have d_swapped_raw: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (Imp (shift A) (shift Q)))"
    using d_deduct d_taut by (rule CE_context_equiv_set_MP)
  have shift_imp: "shift (Imp A Q) = Imp (shift A) (shift Q)"
    by (simp add: shift_def)
  have d_swapped: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift (Imp A Q)))"
    using d_swapped_raw by (simp add: shift_imp)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type insert.prems(3) by auto
  have IH: "CE_context_equiv_set_derivable \<Gamma> T
      (Imp (Exists \<sigma> P) (Imp A Q))"
    using typed_T d_swapped AQ_type by (rule insert.IH)
  let ?E = "Exists \<sigma> P"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using P_type by auto
  have IH_lift: "CE_context_equiv_set_derivable \<Gamma> (insert A T)
      (Imp ?E (Imp A Q))"
    using IH by (rule CE_context_equiv_set_derivable_mono) auto
  have IH_lift': "CE_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T))
      (Imp ?E (Imp A Q))"
    using IH_lift by (rule CE_context_equiv_set_derivable_mono) auto
  have d_E: "CE_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) ?E"
    by (intro CE_context_equiv_set_derivable.Assumption E_type) simp
  have d_A: "CE_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) A"
    by (intro CE_context_equiv_set_derivable.Assumption A_type) simp
  have d_imp_AQ: "CE_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T))
      (Imp A Q)"
    using d_E IH_lift' by (rule CE_context_equiv_set_MP)
  have d_Q: "CE_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) Q"
    using d_A d_imp_AQ by (rule CE_context_equiv_set_MP)
  show ?case
    using E_type d_Q by (rule CE_context_equiv_set_derivable_deduction)
qed

lemma CE_context_equiv_set_derivable_shifted_inst:
  assumes conservative: "CE_context_equiv_conservative"
    and typed: "typed_theory \<Gamma> T"
    and d: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift Q))"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "CE_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q)"
proof -
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> shift ` T"
    and d_U: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) U
      (Imp P (shift Q))"
    using d by (rule CE_context_equiv_set_derivable_finite_support)
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> U \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> U"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using U_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  define S where "S = pre ` U"
  have finite_S: "finite S"
    using finite_U unfolding S_def by simp
  have S_sub: "S \<subseteq> T"
    using pre_prop unfolding S_def by auto
  have shift_S: "shift ` S = U"
  proof
    show "shift ` S \<subseteq> U"
    proof
      fix B
      assume "B \<in> shift ` S"
      then obtain C where C_in: "C \<in> U" and B_def: "B = shift (pre C)"
        unfolding S_def by auto
      have "C = shift (pre C)"
        using pre_prop[OF C_in] by simp
      then show "B \<in> U"
        using C_in B_def by simp
    qed
  next
    show "U \<subseteq> shift ` S"
    proof
      fix B
      assume B_in: "B \<in> U"
      have "pre B \<in> S"
        using B_in unfolding S_def by blast
      moreover have "B = shift (pre B)"
        using pre_prop[OF B_in] by simp
      ultimately show "B \<in> shift ` S"
        by blast
    qed
  qed
  have typed_S: "typed_theory \<Gamma> S"
    using typed S_sub unfolding typed_theory_def by blast
  have d_S: "CE_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` S)
      (Imp P (shift Q))"
    using d_U shift_S by simp
  have lower_S: "CE_context_equiv_set_derivable \<Gamma> S
      (Imp (Exists \<sigma> P) Q)"
    using conservative finite_S typed_S d_S P_type Q_type
    by (rule CE_context_equiv_set_derivable_shifted_inst_finite)
  show ?thesis
    using lower_S S_sub by (rule CE_context_equiv_set_derivable_mono)
qed

theorem CE_context_equiv_shifted_inst_admissible_if_context_conservative:
  assumes conservative: "CE_context_equiv_conservative"
  shows "CE_context_equiv_shifted_inst_admissible"
  using conservative CE_context_equiv_set_derivable_shifted_inst
  unfolding CE_context_equiv_shifted_inst_admissible_def by blast

theorem CE_context_equiv_shifted_inst_admissible_if_prefix_equivalence_internalized:
  assumes prefix: "CE_prefix_equivalence_internalized"
  shows "CE_context_equiv_shifted_inst_admissible"
  using CE_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
  by (rule CE_context_equiv_shifted_inst_admissible_if_context_conservative)

theorem CE_context_equiv_shifted_inst_admissible_if_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_context_equiv_shifted_inst_admissible"
  using CE_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
  by (rule CE_context_equiv_shifted_inst_admissible_if_prefix_equivalence_internalized)

theorem CE_context_equiv_available_countermodel_for_context_nonderivable:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> CE_context_equiv_set_derivable \<Gamma> {} A"
  shows "\<exists>T. CE_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T"
proof -
  let ?T0 = "{Neg A}"
  have finite0: "finite ?T0"
    by simp
  have typed0: "typed_theory \<Gamma> ?T0"
    using A_type unfolding typed_theory_def by auto
  have consistent0: "CE_context_equiv_consistent \<Gamma> ?T0"
    using A_type not_derivable
    by (rule CE_context_equiv_consistent_singleton_neg_of_not_derivable)
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?B = "staged_henkin_extension \<Gamma> ?T0 body_enum"
  have T0_sub_B: "?T0 \<subseteq> ?B"
    by (rule staged_henkin_extension_extends)
  have typed_B: "typed_theory \<Gamma> ?B"
    using typed0 by (rule staged_henkin_extension_typed)
  have consistent_B: "CE_context_equiv_consistent \<Gamma> ?B"
    using inst finite0 typed0 consistent0
    by (rule CE_context_equiv_staged_henkin_extension_consistent)
  have available_B: "Henkin_witness_axioms_available \<Gamma> ?B"
    using body_enum by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?U = "CE_context_equiv_lindenbaum_extension \<Gamma> ?B formula_enum"
  have B_sub_U: "?B \<subseteq> ?U"
    by (rule CE_context_equiv_lindenbaum_extension_extends)
  have local_U: "CE_context_equiv_locally_maximal_consistent \<Gamma> ?U"
    using typed_B consistent_B formula_enum
    by (rule CE_context_equiv_lindenbaum_extension_locally_maximal_consistent)
  have available_U: "Henkin_witness_axioms_available \<Gamma> ?U"
    using available_B B_sub_U by (rule Henkin_witness_axioms_available_mono)
  have neg_in: "Neg A \<in> ?U"
    using T0_sub_B B_sub_U by blast
  show ?thesis
    using local_U available_U neg_in by blast
qed

lemma CE_locally_maximal_consistent_of_CE_equiv:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_locally_maximal_consistent \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def by blast
  have consistent: "CE_consistent \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def
    by (blast intro: CE_consistent_of_CE_equiv_consistent)
  have complete: "CE_negation_complete \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def by blast
  show ?thesis
    using typed consistent complete unfolding CE_locally_maximal_consistent_def by blast
qed

lemma CE_equiv_set_derives_ObjFalse_of_formula_and_neg:
  assumes "CE_equiv_set_derivable \<Gamma> T A"
    and "Neg A \<in> T"
  shows "CE_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CE_equiv_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CE Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CE_proves.C C_proves.H H_proves.PC prop_tautology_contradiction)
  have d_taut: "CE_equiv_set_derivable \<Gamma> T (Imp A (Imp (Neg A) ObjFalse))"
    using taut by (rule CE_equiv_set_Theorem)
  have d_neg: "CE_equiv_set_derivable \<Gamma> T (Neg A)"
    using assms(2) neg_type by (rule CE_equiv_set_derivable.Assumption)
  have d_imp_false: "CE_equiv_set_derivable \<Gamma> T (Imp (Neg A) ObjFalse)"
    using assms(1) d_taut by (rule CE_equiv_set_MP)
  show ?thesis
    using d_neg d_imp_false by (rule CE_equiv_set_MP)
qed

lemma CE_equiv_consistent_not_derives_with_neg:
  assumes "CE_equiv_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> CE_equiv_set_derivable \<Gamma> T A"
proof
  assume "CE_equiv_set_derivable \<Gamma> T A"
  then have "CE_equiv_set_derivable \<Gamma> T ObjFalse"
    using assms(2) by (rule CE_equiv_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding CE_equiv_consistent_def by blast
qed

lemma CE_equiv_locally_maximal_consistent_deductively_closed:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and "CE_equiv_set_derivable \<Gamma> T A"
  shows "A \<in> T"
proof (cases "A \<in> T")
  case True
  then show ?thesis .
next
  case False
  have consistent: "CE_equiv_consistent \<Gamma> T"
    using assms(1) unfolding CE_equiv_locally_maximal_consistent_def by blast
  have complete: "CE_negation_complete \<Gamma> T"
    using assms(1) unfolding CE_equiv_locally_maximal_consistent_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule CE_equiv_set_derivable_formula)
  have neg_in: "Neg A \<in> T"
    using complete A_type False unfolding CE_negation_complete_def by blast
  have "\<not> CE_equiv_set_derivable \<Gamma> T A"
    using consistent neg_in by (rule CE_equiv_consistent_not_derives_with_neg)
  then show ?thesis
    using assms(2) by blast
qed

lemma CE_equiv_locally_maximal_equivalence_closed:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_equivalence_closed \<Gamma> T"
proof (unfold CE_equivalence_closed_def, intro allI impI)
  fix A B
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
  have iff_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have d_iff: "CE_equiv_set_derivable \<Gamma> T (A \<longleftrightarrow>\<^sub>o B)"
    using iff_in iff_type by (rule CE_equiv_set_derivable.Assumption)
  have d_eq: "CE_equiv_set_derivable \<Gamma> T (Eq Prop A B)"
    using A_type B_type d_iff by (rule CE_equiv_set_derivable.LocalPropEquivalence)
  show "Eq Prop A B \<in> T"
    using assms d_eq by (rule CE_equiv_locally_maximal_consistent_deductively_closed)
qed

lemma CE_rule_closed_of_equiv_local_maximal:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_rule_closed \<Gamma> T"
proof -
  have local: "CE_locally_maximal_consistent \<Gamma> T"
    using assms by (rule CE_locally_maximal_consistent_of_CE_equiv)
  have equiv_closed: "CE_equivalence_closed \<Gamma> T"
    using assms by (rule CE_equiv_locally_maximal_equivalence_closed)
  show ?thesis
    using local equiv_closed
    by (rule CE_rule_closed_of_local_maximal_and_equivalence_closed)
qed

lemma CE_Henkin_theory_of_C_Henkin_equiv_local_maximal:
  assumes "C_Henkin_theory \<Gamma> T"
    and "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have local: "CE_locally_maximal_consistent \<Gamma> T"
    using assms(2) by (rule CE_locally_maximal_consistent_of_CE_equiv)
  have equiv_closed: "CE_equivalence_closed \<Gamma> T"
    using assms(2) by (rule CE_equiv_locally_maximal_equivalence_closed)
  show ?thesis
    using assms(1) local equiv_closed
    by (rule CE_Henkin_theory_of_C_Henkin_local_maximal_equivalence_closed)
qed

lemma CE_equiv_set_derivable_cut:
  assumes d_A: "CE_equiv_set_derivable \<Gamma> T A"
    and d_B: "CE_equiv_set_derivable \<Gamma> (insert A T) B"
  shows "CE_equiv_set_derivable \<Gamma> T B"
proof -
  have aux: "\<And>\<Delta> U C. CE_equiv_set_derivable \<Delta> U C \<Longrightarrow>
      \<Delta> = \<Gamma> \<Longrightarrow> U = insert A T \<Longrightarrow> CE_equiv_set_derivable \<Gamma> T C"
  proof -
    fix \<Delta> U C
    assume d: "CE_equiv_set_derivable \<Delta> U C"
    then show "\<Delta> = \<Gamma> \<Longrightarrow> U = insert A T \<Longrightarrow>
        CE_equiv_set_derivable \<Gamma> T C"
    proof (induction rule: CE_equiv_set_derivable.induct)
      case (Assumption C U \<Delta>)
      have Delta_eq: "\<Delta> = \<Gamma>"
        using Assumption.prems(1) .
      have U_eq: "U = insert A T"
        using Assumption.prems(2) .
      have C_in: "C \<in> insert A T"
        using Assumption.hyps(1) U_eq by simp
      have C_type: "\<Gamma> \<turnstile> C : Prop"
        using Assumption.hyps(2) Delta_eq by simp
      show ?case
      proof (cases "C = A")
        case True
        then show ?thesis
          using d_A by simp
      next
        case False
        have "C \<in> T"
          using C_in False by blast
        then show ?thesis
          using C_type by (rule CE_equiv_set_derivable.Assumption)
      qed
    next
      case (Theorem \<Delta> C U)
      have "\<Gamma> \<turnstile>\<^sub>CE C"
        using Theorem.hyps Theorem.prems(1) by simp
      then show ?case
        by (rule CE_equiv_set_derivable.Theorem)
    next
      case (Derive_MP \<Delta> U C D)
      have d_C: "CE_equiv_set_derivable \<Gamma> T C"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have d_imp: "CE_equiv_set_derivable \<Gamma> T (Imp C D)"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using d_C d_imp by (rule CE_equiv_set_derivable.Derive_MP)
    next
      case (LocalPropEquivalence \<Delta> C D U)
      have Delta_eq: "\<Delta> = \<Gamma>"
        using LocalPropEquivalence.prems(1) .
      have C_type: "\<Gamma> \<turnstile> C : Prop"
        using LocalPropEquivalence.hyps(1) Delta_eq by simp
      have D_type: "\<Gamma> \<turnstile> D : Prop"
        using LocalPropEquivalence.hyps(2) Delta_eq by simp
      have d_iff: "CE_equiv_set_derivable \<Gamma> T (C \<longleftrightarrow>\<^sub>o D)"
        using LocalPropEquivalence.prems by (rule LocalPropEquivalence.IH)
      show ?case
        using C_type D_type d_iff
        by (rule CE_equiv_set_derivable.LocalPropEquivalence)
    qed
  qed
  show ?thesis
    using d_B refl refl by (rule aux)
qed

lemma CE_equiv_consistent_insert_derivable:
  assumes consistent: "CE_equiv_consistent \<Gamma> T"
    and d_A: "CE_equiv_set_derivable \<Gamma> T A"
  shows "CE_equiv_consistent \<Gamma> (insert A T)"
proof (unfold CE_equiv_consistent_def, intro notI)
  assume d_false: "CE_equiv_set_derivable \<Gamma> (insert A T) ObjFalse"
  have "CE_equiv_set_derivable \<Gamma> T ObjFalse"
    using d_A d_false by (rule CE_equiv_set_derivable_cut)
  then show False
    using consistent unfolding CE_equiv_consistent_def by blast
qed

lemma CE_equiv_consistent_insert_equivalence_instance:
  assumes consistent: "CE_equiv_consistent \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
  shows "CE_equiv_consistent \<Gamma> (insert (Eq Prop A B) T)"
proof -
  have iff_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have d_iff: "CE_equiv_set_derivable \<Gamma> T (A \<longleftrightarrow>\<^sub>o B)"
    using iff_in iff_type by (rule CE_equiv_set_derivable.Assumption)
  have d_eq: "CE_equiv_set_derivable \<Gamma> T (Eq Prop A B)"
    using A_type B_type d_iff by (rule CE_equiv_set_derivable.LocalPropEquivalence)
  show ?thesis
    using consistent d_eq by (rule CE_equiv_consistent_insert_derivable)
qed

definition CE_equivalence_closure_step ::
    "ctx \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CE_equivalence_closure_step \<Gamma> A B T =
    (if \<Gamma> \<turnstile> A : Prop \<and> \<Gamma> \<turnstile> B : Prop \<and> (A \<longleftrightarrow>\<^sub>o B) \<in> T
     then insert (Eq Prop A B) T
     else T)"

primrec CE_equivalence_closure_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm \<times> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CE_equivalence_closure_chain \<Gamma> T enum 0 = T"
| "CE_equivalence_closure_chain \<Gamma> T enum (Suc n) =
    CE_equivalence_closure_step \<Gamma> (fst (enum n)) (snd (enum n))
      (CE_equivalence_closure_chain \<Gamma> T enum n)"

definition CE_equivalence_closure_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm \<times> oterm) \<Rightarrow> oterm set" where
  "CE_equivalence_closure_extension \<Gamma> T enum =
    (\<Union>n. CE_equivalence_closure_chain \<Gamma> T enum n)"

definition repeatedly_enumerates_formula_pairs ::
    "ctx \<Rightarrow> (nat \<Rightarrow> oterm \<times> oterm) \<Rightarrow> bool" where
  "repeatedly_enumerates_formula_pairs \<Gamma> enum \<longleftrightarrow>
    (\<forall>A B n. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      (\<exists>m\<ge>n. enum m = (A, B)))"

lemma repeatedly_enumerates_formula_pairs_from_nat:
  "repeatedly_enumerates_formula_pairs \<Gamma>
    (\<lambda>m. (from_nat (fst (prod_decode m)) :: oterm \<times> oterm))"
proof (unfold repeatedly_enumerates_formula_pairs_def, intro allI impI)
  fix A B n
  assume "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  obtain k where k: "(from_nat k :: oterm \<times> oterm) = (A, B)"
    using surj_from_nat[where ?'a = "oterm \<times> oterm"]
    unfolding surj_def by metis
  let ?m = "prod_encode (k, n)"
  have "?m \<ge> n"
    using le_prod_encode_2[of n k] by simp
  moreover have "((\<lambda>m. (from_nat (fst (prod_decode m)) :: oterm \<times> oterm)) ?m) =
      (A, B)"
    using k by simp
  ultimately show "\<exists>m\<ge>n.
      ((\<lambda>m. (from_nat (fst (prod_decode m)) :: oterm \<times> oterm)) m) =
      (A, B)"
    by blast
qed

lemma repeatedly_enumerates_formula_pairs_exists:
  "\<exists>enum. repeatedly_enumerates_formula_pairs \<Gamma> enum"
  using repeatedly_enumerates_formula_pairs_from_nat by blast

lemma CE_equivalence_closure_step_extends:
  "T \<subseteq> CE_equivalence_closure_step \<Gamma> A B T"
  unfolding CE_equivalence_closure_step_def by auto

lemma CE_equivalence_closure_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_equivalence_closure_step \<Gamma> A B T)"
  using assms unfolding CE_equivalence_closure_step_def typed_theory_def by auto

lemma CE_equivalence_closure_step_consistent:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "CE_equiv_consistent \<Gamma> (CE_equivalence_closure_step \<Gamma> A B T)"
  using assms
  unfolding CE_equivalence_closure_step_def
  by (auto intro: CE_equiv_consistent_insert_equivalence_instance)

lemma CE_equivalence_closure_chain_step:
  "CE_equivalence_closure_chain \<Gamma> T enum n \<subseteq>
    CE_equivalence_closure_chain \<Gamma> T enum (Suc n)"
  using CE_equivalence_closure_step_extends[of
      "CE_equivalence_closure_chain \<Gamma> T enum n" \<Gamma>
      "fst (enum n)" "snd (enum n)"]
  by simp

lemma CE_equivalence_closure_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_equivalence_closure_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_equivalence_closure_step_typed)
qed

lemma CE_equivalence_closure_chain_consistent:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "CE_equiv_consistent \<Gamma> (CE_equivalence_closure_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CE_equivalence_closure_step_consistent)
qed

lemma CE_equivalence_closure_extension_extends:
  "T \<subseteq> CE_equivalence_closure_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> CE_equivalence_closure_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> CE_equivalence_closure_extension \<Gamma> T enum"
    unfolding CE_equivalence_closure_extension_def by blast
qed

lemma CE_equivalence_closure_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (CE_equivalence_closure_chain \<Gamma> T enum n)"
    using assms by (rule CE_equivalence_closure_chain_typed)
  then show ?thesis
    unfolding CE_equivalence_closure_extension_def by (rule typed_theory_nat_union)
qed

lemma CE_equivalence_closure_extension_consistent:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "CE_equiv_consistent \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
proof (unfold CE_equiv_consistent_def, intro notI)
  assume d_false: "CE_equiv_set_derivable \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CE_equivalence_closure_extension \<Gamma> T enum"
    and d_U: "CE_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CE_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. CE_equivalence_closure_chain \<Gamma> T enum n)"
    using U_sub unfolding CE_equivalence_closure_extension_def .
  have step: "\<And>n. CE_equivalence_closure_chain \<Gamma> T enum n \<subseteq>
      CE_equivalence_closure_chain \<Gamma> T enum (Suc n)"
    by (rule CE_equivalence_closure_chain_step)
  have "\<exists>n. U \<subseteq> CE_equivalence_closure_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain:
      "U \<subseteq> CE_equivalence_closure_chain \<Gamma> T enum n"
    by blast
  have "CE_equiv_set_derivable \<Gamma>
      (CE_equivalence_closure_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CE_equiv_set_derivable_mono)
  moreover have "CE_equiv_consistent \<Gamma> (CE_equivalence_closure_chain \<Gamma> T enum n)"
    using assms by (rule CE_equivalence_closure_chain_consistent)
  ultimately show False
    unfolding CE_equiv_consistent_def by blast
qed

lemma CE_equivalence_closure_extension_equivalence_closed:
  assumes enum: "repeatedly_enumerates_formula_pairs \<Gamma> enum"
  shows "CE_equivalence_closed \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
proof (unfold CE_equivalence_closed_def, intro allI impI)
  fix A B
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> CE_equivalence_closure_extension \<Gamma> T enum"
  obtain n where iff_in_n:
      "(A \<longleftrightarrow>\<^sub>o B) \<in> CE_equivalence_closure_chain \<Gamma> T enum n"
    using iff_in unfolding CE_equivalence_closure_extension_def by blast
  obtain m where m_ge: "m \<ge> n" and enum_m: "enum m = (A, B)"
    using enum A_type B_type unfolding repeatedly_enumerates_formula_pairs_def by blast
  have step: "\<And>k. CE_equivalence_closure_chain \<Gamma> T enum k \<subseteq>
      CE_equivalence_closure_chain \<Gamma> T enum (Suc k)"
    by (rule CE_equivalence_closure_chain_step)
  have chain_mono: "CE_equivalence_closure_chain \<Gamma> T enum n \<subseteq>
      CE_equivalence_closure_chain \<Gamma> T enum m"
    by (rule nat_chain_mono[
        where S = "\<lambda>k. CE_equivalence_closure_chain \<Gamma> T enum k",
        OF step m_ge])
  have iff_in_m: "(A \<longleftrightarrow>\<^sub>o B) \<in>
      CE_equivalence_closure_chain \<Gamma> T enum m"
    using iff_in_n chain_mono by blast
  have cond: "\<Gamma> \<turnstile> A : Prop \<and> \<Gamma> \<turnstile> B : Prop \<and>
      (A \<longleftrightarrow>\<^sub>o B) \<in> CE_equivalence_closure_chain \<Gamma> T enum m"
    using A_type B_type iff_in_m by blast
  have step_eq: "CE_equivalence_closure_step \<Gamma> A B
      (CE_equivalence_closure_chain \<Gamma> T enum m) =
      insert (Eq Prop A B) (CE_equivalence_closure_chain \<Gamma> T enum m)"
    using cond unfolding CE_equivalence_closure_step_def by simp
  have "Eq Prop A B \<in> CE_equivalence_closure_chain \<Gamma> T enum (Suc m)"
    using enum_m step_eq by simp
  then show "Eq Prop A B \<in> CE_equivalence_closure_extension \<Gamma> T enum"
    unfolding CE_equivalence_closure_extension_def by blast
qed

lemma CE_negation_complete_mono:
  assumes "CE_negation_complete \<Gamma> T"
    and "T \<subseteq> U"
  shows "CE_negation_complete \<Gamma> U"
  using assms unfolding CE_negation_complete_def by blast

lemma CE_equivalence_closure_extension_negation_complete:
  assumes "CE_negation_complete \<Gamma> T"
  shows "CE_negation_complete \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
  using assms CE_equivalence_closure_extension_extends
  by (rule CE_negation_complete_mono)

lemma CE_equivalence_closure_extension_equiv_locally_maximal_consistent:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_equiv_locally_maximal_consistent \<Gamma>
    (CE_equivalence_closure_extension \<Gamma> T enum)"
proof -
  have typed_T: "typed_theory \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def by blast
  have consistent_T: "CE_equiv_consistent \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def by blast
  have complete_T: "CE_negation_complete \<Gamma> T"
    using assms unfolding CE_equiv_locally_maximal_consistent_def by blast
  have typed: "typed_theory \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
    using typed_T by (rule CE_equivalence_closure_extension_typed)
  have consistent: "CE_equiv_consistent \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using consistent_T by (rule CE_equivalence_closure_extension_consistent)
  have complete: "CE_negation_complete \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using complete_T by (rule CE_equivalence_closure_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CE_equiv_locally_maximal_consistent_def by blast
qed

theorem CE_equivalence_saturated_extension_exists:
  assumes "typed_theory \<Gamma> T"
    and "CE_equiv_consistent \<Gamma> T"
  shows "\<exists>U. T \<subseteq> U \<and> typed_theory \<Gamma> U \<and>
    CE_equiv_consistent \<Gamma> U \<and> CE_equivalence_closed \<Gamma> U"
proof -
  obtain enum where enum: "repeatedly_enumerates_formula_pairs \<Gamma> enum"
    using repeatedly_enumerates_formula_pairs_exists by blast
  let ?U = "CE_equivalence_closure_extension \<Gamma> T enum"
  have extends: "T \<subseteq> ?U"
    by (rule CE_equivalence_closure_extension_extends)
  have typed: "typed_theory \<Gamma> ?U"
    using assms(1) by (rule CE_equivalence_closure_extension_typed)
  have consistent: "CE_equiv_consistent \<Gamma> ?U"
    using assms(2) by (rule CE_equivalence_closure_extension_consistent)
  have closed: "CE_equivalence_closed \<Gamma> ?U"
    using enum by (rule CE_equivalence_closure_extension_equivalence_closed)
  show ?thesis
    using extends typed consistent closed by blast
qed

theorem CE_equiv_locally_maximal_saturated_extension_exists:
  assumes "CE_equiv_locally_maximal_consistent \<Gamma> T"
  shows "\<exists>U. T \<subseteq> U \<and> CE_equiv_locally_maximal_consistent \<Gamma> U \<and>
    CE_equivalence_closed \<Gamma> U"
proof -
  obtain enum where enum: "repeatedly_enumerates_formula_pairs \<Gamma> enum"
    using repeatedly_enumerates_formula_pairs_exists by blast
  let ?U = "CE_equivalence_closure_extension \<Gamma> T enum"
  have extends: "T \<subseteq> ?U"
    by (rule CE_equivalence_closure_extension_extends)
  have local: "CE_equiv_locally_maximal_consistent \<Gamma> ?U"
    using assms by (rule CE_equivalence_closure_extension_equiv_locally_maximal_consistent)
  have closed: "CE_equivalence_closed \<Gamma> ?U"
    using enum by (rule CE_equivalence_closure_extension_equivalence_closed)
  show ?thesis
    using extends local closed by blast
qed

lemma CE_Henkin_closed_under_CE_equiv_set_derivable:
  assumes henkin: "CE_Henkin_theory \<Gamma> T"
    and d: "CE_equiv_set_derivable \<Gamma> T A"
  shows "A \<in> T"
proof -
  have aux: "\<And>\<Gamma> T A. CE_equiv_set_derivable \<Gamma> T A \<Longrightarrow>
      CE_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix \<Gamma> T A
    assume d: "CE_equiv_set_derivable \<Gamma> T A"
    then show "CE_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
    proof (induction rule: CE_equiv_set_derivable.induct)
      case (Assumption A T \<Gamma>)
      then show ?case
        by simp
    next
      case (Theorem \<Gamma> A T)
      show ?case
        using Theorem.hyps Theorem.prems by (rule CE_Henkin_contains_theorems)
    next
      case (Derive_MP \<Gamma> T A B)
      have c_henkin: "C_Henkin_theory \<Gamma> T"
        using Derive_MP.prems by (rule CE_Henkin_C_Henkin)
      have typed: "typed_theory \<Gamma> T"
        using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
      have closed: "C_deductively_closed \<Gamma> T"
        using c_henkin by (rule C_Henkin_deductively_closed)
      have A_in: "A \<in> T"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have imp_in: "Imp A B \<in> T"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using typed closed A_in imp_in by (rule C_closed_under_MP)
    next
      case (LocalPropEquivalence \<Gamma> A B T)
      have equiv_closed: "CE_equivalence_closed \<Gamma> T"
        using LocalPropEquivalence.prems by (rule CE_Henkin_equivalence_closed)
      have iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
        using LocalPropEquivalence.prems by (rule LocalPropEquivalence.IH)
      show ?case
        using equiv_closed LocalPropEquivalence.hyps(1,2) iff_in
        by (rule CE_equivalence_closedD)
    qed
  qed
  show ?thesis
    using d henkin by (rule aux)
qed

lemma CE_Henkin_CE_equiv_consistent:
  assumes henkin: "CE_Henkin_theory \<Gamma> T"
  shows "CE_equiv_consistent \<Gamma> T"
proof (unfold CE_equiv_consistent_def, intro notI)
  assume d_false: "CE_equiv_set_derivable \<Gamma> T ObjFalse"
  have false_in: "ObjFalse \<in> T"
    using henkin d_false by (rule CE_Henkin_closed_under_CE_equiv_set_derivable)
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using henkin by (rule CE_Henkin_C_Henkin)
  have consistent: "C_consistent \<Gamma> T"
    using c_henkin by (rule C_Henkin_consistent)
  have false_type: "\<Gamma> \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using false_in false_type by (rule C_set_Assumption)
  then show False
    using consistent unfolding C_consistent_def by blast
qed

lemma CE_Henkin_equiv_locally_maximal_consistent:
  assumes henkin: "CE_Henkin_theory \<Gamma> T"
  shows "CE_equiv_locally_maximal_consistent \<Gamma> T"
proof -
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using henkin by (rule CE_Henkin_C_Henkin)
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have consistent: "CE_equiv_consistent \<Gamma> T"
    using henkin by (rule CE_Henkin_CE_equiv_consistent)
  have complete: "CE_negation_complete \<Gamma> T"
  proof (unfold CE_negation_complete_def, intro allI impI)
    fix A
    assume A_type: "\<Gamma> \<turnstile> A : Prop"
    have maximal: "C_maximal_consistent \<Gamma> T"
      using c_henkin unfolding C_Henkin_theory_def by blast
    have "C_negation_complete \<Gamma> T"
      using maximal unfolding C_maximal_consistent_def by blast
    then show "A \<in> T \<or> Neg A \<in> T"
      using A_type unfolding C_negation_complete_def by blast
  qed
  show ?thesis
    using typed consistent complete
    unfolding CE_equiv_locally_maximal_consistent_def by blast
qed

lemma CE_Henkin_theory_iff_C_Henkin_equiv_local_maximal:
  "CE_Henkin_theory \<Gamma> T \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> CE_equiv_locally_maximal_consistent \<Gamma> T"
proof
  assume henkin: "CE_Henkin_theory \<Gamma> T"
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using henkin by (rule CE_Henkin_C_Henkin)
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    using henkin by (rule CE_Henkin_equiv_locally_maximal_consistent)
  show "C_Henkin_theory \<Gamma> T \<and> CE_equiv_locally_maximal_consistent \<Gamma> T"
    using c_henkin equiv_local by blast
next
  assume "C_Henkin_theory \<Gamma> T \<and> CE_equiv_locally_maximal_consistent \<Gamma> T"
  then show "CE_Henkin_theory \<Gamma> T"
    by (blast intro: CE_Henkin_theory_of_C_Henkin_equiv_local_maximal)
qed

lemma CE_equiv_set_derivable_of_C_set_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "CE_equiv_set_derivable \<Gamma> T A"
proof -
  have list_lift: "\<And>\<Delta> A. \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A \<Longrightarrow>
      CE_equiv_set_derivable \<Gamma> (set \<Delta>) A"
  proof -
    fix \<Delta> A
    assume d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    then show "CE_equiv_set_derivable \<Gamma> (set \<Delta>) A"
    proof (induction rule: C_derivable.induct)
      case (Assumption A \<Delta> \<Gamma>)
      then show ?case
        by (rule CE_equiv_set_derivable.Assumption)
    next
      case (Theorem \<Gamma> A \<Delta>)
      have "\<Gamma> \<turnstile>\<^sub>CE A"
        using Theorem.hyps by (rule CE_proves.C)
      then show ?case
        by (rule CE_equiv_set_derivable.Theorem)
    next
      case (Derive_MP \<Gamma> \<Delta> A B)
      show ?case
        using Derive_MP.IH(1) Derive_MP.IH(2)
        by (rule CE_equiv_set_derivable.Derive_MP)
    qed
  qed
  obtain \<Delta> where sub: "set \<Delta> \<subseteq> T"
    and d_list: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms unfolding C_set_derivable_def by blast
  have "CE_equiv_set_derivable \<Gamma> (set \<Delta>) A"
    using d_list by (rule list_lift)
  then show ?thesis
    using sub by (rule CE_equiv_set_derivable_mono)
qed

lemma C_consistent_of_CE_equiv_consistent:
  assumes "CE_equiv_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> T"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  then have "CE_equiv_set_derivable \<Gamma> T ObjFalse"
    by (rule CE_equiv_set_derivable_of_C_set_derivable)
  then show False
    using assms unfolding CE_equiv_consistent_def by blast
qed

lemma C_negation_complete_mono:
  assumes "C_negation_complete \<Gamma> T"
    and "T \<subseteq> U"
  shows "C_negation_complete \<Gamma> U"
  using assms unfolding C_negation_complete_def by blast

lemma Henkin_witnessed_extension_no_new_exists:
  assumes "Henkin_witnessed \<Gamma> T"
    and "T \<subseteq> U"
    and "\<And>\<sigma> A. Exists \<sigma> A \<in> U \<Longrightarrow> Exists \<sigma> A \<in> T"
  shows "Henkin_witnessed \<Gamma> U"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume type_A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  assume exists_in_U: "Exists \<sigma> A \<in> U"
  have exists_in_T: "Exists \<sigma> A \<in> T"
    using exists_in_U by (rule assms(3))
  from assms(1) type_A exists_in_T obtain W where
    "\<Gamma> \<turnstile> W : \<sigma>" and "subst0 W A \<in> T"
    unfolding Henkin_witnessed_def by blast
  then show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> U"
    using assms(2) by blast
qed

lemma CE_negation_complete_of_C_negation_complete:
  assumes "C_negation_complete \<Gamma> T"
  shows "CE_negation_complete \<Gamma> T"
  using assms unfolding C_negation_complete_def CE_negation_complete_def by blast

lemma C_negation_complete_of_CE_negation_complete:
  assumes "CE_negation_complete \<Gamma> T"
  shows "C_negation_complete \<Gamma> T"
  using assms unfolding C_negation_complete_def CE_negation_complete_def by blast

lemma CE_equiv_locally_maximal_consistent_of_C_Henkin_CE_equiv_consistent:
  assumes c_henkin: "C_Henkin_theory \<Gamma> T"
    and consistent: "CE_equiv_consistent \<Gamma> T"
  shows "CE_equiv_locally_maximal_consistent \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have c_complete: "C_negation_complete \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have complete: "CE_negation_complete \<Gamma> T"
    using c_complete by (rule CE_negation_complete_of_C_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CE_equiv_locally_maximal_consistent_def by blast
qed

lemma CE_Henkin_theory_of_C_Henkin_CE_equiv_consistent:
  assumes c_henkin: "C_Henkin_theory \<Gamma> T"
    and consistent: "CE_equiv_consistent \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    using c_henkin consistent
    by (rule CE_equiv_locally_maximal_consistent_of_C_Henkin_CE_equiv_consistent)
  show ?thesis
    using c_henkin equiv_local
    by (rule CE_Henkin_theory_of_C_Henkin_equiv_local_maximal)
qed

lemma C_Henkin_theory_of_CE_equiv_local_maximal_available:
  assumes local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using local unfolding CE_equiv_locally_maximal_consistent_def by blast
  have equiv_consistent: "CE_equiv_consistent \<Gamma> T"
    using local unfolding CE_equiv_locally_maximal_consistent_def by blast
  have c_consistent: "C_consistent \<Gamma> T"
    using equiv_consistent by (rule C_consistent_of_CE_equiv_consistent)
  have ce_complete: "CE_negation_complete \<Gamma> T"
    using local unfolding CE_equiv_locally_maximal_consistent_def by blast
  have c_complete: "C_negation_complete \<Gamma> T"
    using ce_complete by (rule C_negation_complete_of_CE_negation_complete)
  have maximal: "C_maximal_consistent \<Gamma> T"
    using typed c_consistent c_complete
    unfolding C_maximal_consistent_def by blast
  have closed: "C_deductively_closed \<Gamma> T"
    using maximal by (rule C_maximal_consistent_deductively_closed)
  have witnessed: "Henkin_witnessed \<Gamma> T"
    using typed closed available by (rule C_Henkin_witnessed_from_available)
  show ?thesis
    using maximal witnessed unfolding C_Henkin_theory_def by blast
qed

lemma CE_Henkin_theory_of_CE_equiv_local_maximal_available:
  assumes local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using local available by (rule C_Henkin_theory_of_CE_equiv_local_maximal_available)
  show ?thesis
    using c_henkin local by (rule CE_Henkin_theory_of_C_Henkin_equiv_local_maximal)
qed

lemma C_Henkin_theory_of_CE_context_equiv_local_maximal_available:
  assumes local: "CE_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> T"
proof -
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    using local by (rule CE_equiv_locally_maximal_consistent_of_CE_context_equiv)
  show ?thesis
    using equiv_local available by (rule C_Henkin_theory_of_CE_equiv_local_maximal_available)
qed

lemma CE_Henkin_theory_of_CE_context_equiv_local_maximal_available:
  assumes local: "CE_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    using local by (rule CE_equiv_locally_maximal_consistent_of_CE_context_equiv)
  show ?thesis
    using equiv_local available by (rule CE_Henkin_theory_of_CE_equiv_local_maximal_available)
qed

lemma C_Henkin_theory_extension_no_new_exists_of_CE_equiv_consistent:
  assumes c_henkin: "C_Henkin_theory \<Gamma> T"
    and sub: "T \<subseteq> U"
    and typed: "typed_theory \<Gamma> U"
    and consistent: "CE_equiv_consistent \<Gamma> U"
    and no_new_exists: "\<And>\<sigma> A. Exists \<sigma> A \<in> U \<Longrightarrow> Exists \<sigma> A \<in> T"
  shows "C_Henkin_theory \<Gamma> U"
proof -
  have c_consistent: "C_consistent \<Gamma> U"
    using consistent by (rule C_consistent_of_CE_equiv_consistent)
  have c_complete_T: "C_negation_complete \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have c_complete_U: "C_negation_complete \<Gamma> U"
    using c_complete_T sub by (rule C_negation_complete_mono)
  have maximal: "C_maximal_consistent \<Gamma> U"
    using typed c_consistent c_complete_U
    unfolding C_maximal_consistent_def by blast
  have witnessed_T: "Henkin_witnessed \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def by blast
  have witnessed_U: "Henkin_witnessed \<Gamma> U"
    using witnessed_T sub no_new_exists
    by (rule Henkin_witnessed_extension_no_new_exists)
  show ?thesis
    using maximal witnessed_U unfolding C_Henkin_theory_def by blast
qed

lemma CE_equivalence_closure_step_no_new_exists:
  assumes "Exists \<sigma> C \<in> CE_equivalence_closure_step \<Gamma> A B T"
  shows "Exists \<sigma> C \<in> T"
proof (cases "\<Gamma> \<turnstile> A : Prop \<and> \<Gamma> \<turnstile> B : Prop \<and> (A \<longleftrightarrow>\<^sub>o B) \<in> T")
  case True
  then have "CE_equivalence_closure_step \<Gamma> A B T = insert (Eq Prop A B) T"
    unfolding CE_equivalence_closure_step_def by simp
  then show ?thesis
    using assms by auto
next
  case False
  then show ?thesis
    using assms unfolding CE_equivalence_closure_step_def by auto
qed

lemma CE_equivalence_closure_chain_no_new_exists:
  assumes "Exists \<sigma> A \<in> CE_equivalence_closure_chain \<Gamma> T enum n"
  shows "Exists \<sigma> A \<in> T"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "Exists \<sigma> A \<in> CE_equivalence_closure_step \<Gamma> (fst (enum n)) (snd (enum n))
      (CE_equivalence_closure_chain \<Gamma> T enum n)"
    using Suc.prems by simp
  then have "Exists \<sigma> A \<in> CE_equivalence_closure_chain \<Gamma> T enum n"
    by (rule CE_equivalence_closure_step_no_new_exists)
  then show ?case
    by (rule Suc.IH)
qed

lemma CE_equivalence_closure_extension_no_new_exists:
  assumes "Exists \<sigma> A \<in> CE_equivalence_closure_extension \<Gamma> T enum"
  shows "Exists \<sigma> A \<in> T"
proof -
  obtain n where "Exists \<sigma> A \<in> CE_equivalence_closure_chain \<Gamma> T enum n"
    using assms unfolding CE_equivalence_closure_extension_def by blast
  then show ?thesis
    by (rule CE_equivalence_closure_chain_no_new_exists)
qed

lemma CE_equivalence_closure_extension_C_Henkin:
  assumes c_henkin: "C_Henkin_theory \<Gamma> T"
    and consistent: "CE_equiv_consistent \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
proof -
  have typed_T: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have sub: "T \<subseteq> CE_equivalence_closure_extension \<Gamma> T enum"
    by (rule CE_equivalence_closure_extension_extends)
  have typed: "typed_theory \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
    using typed_T by (rule CE_equivalence_closure_extension_typed)
  have consistent_ext: "CE_equiv_consistent \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using consistent by (rule CE_equivalence_closure_extension_consistent)
  have no_new_exists: "\<And>\<sigma> A. Exists \<sigma> A \<in>
      CE_equivalence_closure_extension \<Gamma> T enum \<Longrightarrow> Exists \<sigma> A \<in> T"
    by (rule CE_equivalence_closure_extension_no_new_exists)
  show ?thesis
    using c_henkin sub typed consistent_ext no_new_exists
    by (rule C_Henkin_theory_extension_no_new_exists_of_CE_equiv_consistent)
qed

lemma CE_Henkin_theory_of_C_Henkin_CE_equiv_consistent_saturation:
  assumes c_henkin: "C_Henkin_theory \<Gamma> T"
    and consistent: "CE_equiv_consistent \<Gamma> T"
    and enum: "repeatedly_enumerates_formula_pairs \<Gamma> enum"
  shows "CE_Henkin_theory \<Gamma> (CE_equivalence_closure_extension \<Gamma> T enum)"
proof -
  have c_henkin_ext: "C_Henkin_theory \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using c_henkin consistent by (rule CE_equivalence_closure_extension_C_Henkin)
  have equiv_closed: "CE_equivalence_closed \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using enum by (rule CE_equivalence_closure_extension_equivalence_closed)
  have equiv_consistent: "CE_equiv_consistent \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using consistent by (rule CE_equivalence_closure_extension_consistent)
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma>
      (CE_equivalence_closure_extension \<Gamma> T enum)"
    using c_henkin_ext equiv_consistent
    by (rule CE_equiv_locally_maximal_consistent_of_C_Henkin_CE_equiv_consistent)
  show ?thesis
    using c_henkin_ext equiv_local
    by (rule CE_Henkin_theory_of_C_Henkin_equiv_local_maximal)
qed

inductive CEV_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>CEV\<^sub>s _" [50, 50, 50] 50) where
  Assumption[intro]: "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
| Derive_MP[intro]:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"

lemma CEV_set_derivable_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CEV_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case
    by (auto elim: has_type.cases)
qed

lemma CEV_set_derivable_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (intro CEV_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (intro CEV_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  from Derive_MP.IH(1)[OF Derive_MP.prems]
    Derive_MP.IH(2)[OF Derive_MP.prems]
  show ?case
    by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_set_derivable_finite_support:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  obtains U where "finite U" and "U \<subseteq> T" and "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
proof -
  have "\<exists>U. finite U \<and> U \<subseteq> T \<and> \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
    using assms
  proof (induction rule: CEV_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> A T)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (Derive_MP \<Gamma> T A B)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_A: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
      using Derive_MP.IH(1) by auto
    obtain V where V_fin: "finite V" and V_sub: "V \<subseteq> T"
      and V_imp: "\<Gamma> ; V \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
      using Derive_MP.IH(2) by auto
    have A_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sub>s A"
      using U_A by (rule CEV_set_derivable_mono) auto
    have imp_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
      using V_imp by (rule CEV_set_derivable_mono) auto
    have B_der: "\<Gamma> ; U \<union> V \<turnstile>\<^sub>CEV\<^sub>s B"
      using A_der imp_der by (rule CEV_set_derivable.Derive_MP)
    show ?case
      using U_fin U_sub V_fin V_sub B_der by (intro exI[of _ "U \<union> V"]) auto
  qed
  then show ?thesis
    using that by blast
qed

lemma CEV_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms by (rule CEV_set_derivable.Theorem)

lemma CEV_set_MP:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"
  using assms by (rule CEV_set_derivable.Derive_MP)

lemma CEV_set_ex_falso:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
proof -
  have taut_raw: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg ObjTrue) (Imp ObjTrue A)"
    using typed_ObjTrue assms(2)
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_imp_of_neg_left)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjFalse (Imp ObjTrue A)"
    using taut_raw by (simp add: ObjFalse_def)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp ObjFalse (Imp ObjTrue A)"
    using taut by (rule CEV_set_Theorem)
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp ObjTrue A"
    using assms(1) d_taut by (rule CEV_set_MP)
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjTrue"
    using CEV_proves_ObjTrue by (rule CEV_set_Theorem)
  show ?thesis
    using d_true d_imp by (rule CEV_set_MP)
qed

lemma CEV_set_empty_imp_proves:
  assumes "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
proof -
  have empty_imp:
    "\<And>\<Gamma> T A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow> T = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  proof -
    fix \<Gamma> T A
    assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    then show "T = {} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
    proof (induction rule: CEV_set_derivable.induct)
      case (Assumption A T \<Gamma>)
      then show ?case
        by simp
    next
      case (Theorem \<Gamma> A T)
      then show ?case
        by simp
    next
      case (Derive_MP \<Gamma> T A B)
      have dA: "\<Gamma> \<turnstile>\<^sub>CEV A"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have dImp: "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using dA dImp by (rule CEV_proves.MP)
    qed
  qed
  show ?thesis
    using assms by (rule empty_imp[OF _ refl])
qed

lemma CEV_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_proves_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp A B)"
    using assms(1) B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_imp_of_right)
  show ?thesis
    using assms(2) taut by (rule CEV_proves.MP)
qed

lemma CEV_proves_imp_false_to_neg:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A ObjFalse) (Neg A)"
  using CE_proves_imp_false_to_neg[OF assms] by (rule CEV_proves.CE)

lemma CEV_proves_imp_neg_false_to_formula:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp (Neg A) ObjFalse) A"
  using CE_proves_imp_neg_false_to_formula[OF assms] by (rule CEV_proves.CE)

lemma CEV_set_derivable_deduction:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; insert A T \<turnstile>\<^sub>CEV\<^sub>s B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
proof -
  have aux: "\<And>X S. \<Gamma> \<turnstile> X : Prop \<Longrightarrow>
      insert A T \<subseteq> insert X S \<Longrightarrow>
      \<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp X B"
    using assms(2)
  proof (induction rule: CEV_set_derivable.induct)
    case (Assumption B U \<Gamma>)
    have X_type: "\<Gamma> \<turnstile> X : Prop"
      using Assumption.prems by blast
    have U_sub: "U \<subseteq> insert X S"
      using Assumption.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps by simp
    show ?case
    proof (cases "B = X")
      case True
      have "\<Gamma> \<turnstile>\<^sub>CEV Imp X X"
        using X_type by (intro CEV_proves.CE CE_proves.C C_proves.H H_imp_self)
      then have "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp X X"
        by (rule CEV_set_Theorem)
      then show ?thesis
        using True by simp
    next
      case False
      have B_in: "B \<in> S"
        using Assumption.hyps U_sub False by blast
      have dB: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s B"
        using B_in B_type by (rule CEV_set_derivable.Assumption)
      have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp X B)"
        using X_type B_type
        by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
            prop_tautology_imp_of_right)
      have d_taut: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp B (Imp X B)"
        using taut by (rule CEV_set_Theorem)
      show ?thesis
        using dB d_taut by (rule CEV_set_MP)
    qed
  next
    case (Theorem \<Gamma> B U)
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp X B"
      using Theorem.prems(1) Theorem.hyps by (rule CEV_proves_imp_of_right)
    then show ?case
      by (rule CEV_set_Theorem)
  next
    case (Derive_MP \<Gamma> U B C)
    have X_type: "\<Gamma> \<turnstile> X : Prop"
      using Derive_MP.prems by blast
    have U_sub: "U \<subseteq> insert X S"
      using Derive_MP.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule CEV_set_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2) by (auto dest: CEV_set_derivable_formula elim: has_type.cases)
    have taut: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp X B) (Imp (Imp X (Imp B C)) (Imp X C))"
      using X_type B_type C_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
          prop_tautology_deduction_mp)
    have d_taut: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Imp X B) (Imp (Imp X (Imp B C)) (Imp X C))"
      using taut by (rule CEV_set_Theorem)
    have IH_B: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp X B"
      using X_type U_sub by (rule Derive_MP.IH(1))
    have IH_imp: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp X (Imp B C)"
      using X_type U_sub by (rule Derive_MP.IH(2))
    have step: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Imp X (Imp B C)) (Imp X C)"
      using IH_B d_taut by (rule CEV_set_MP)
    show ?case
      using IH_imp step by (rule CEV_set_MP)
  qed
  show ?thesis
    using assms(1) by (rule aux) blast
qed

lemma CEV_Henkin_closed_under_CEV_set_derivable:
  assumes henkin: "CEV_Henkin_theory \<Gamma> T"
    and d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "A \<in> T"
proof -
  have aux: "\<And>\<Gamma> T A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow>
      CEV_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix \<Gamma> T A
    assume d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    then show "CEV_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
    proof (induction rule: CEV_set_derivable.induct)
      case (Assumption A T \<Gamma>)
      then show ?case
        by simp
    next
      case (Theorem \<Gamma> A T)
      show ?case
        using Theorem.hyps Theorem.prems by (rule CEV_Henkin_contains_theorems)
    next
      case (Derive_MP \<Gamma> T A B)
      have c_henkin: "C_Henkin_theory \<Gamma> T"
        using Derive_MP.prems by (rule CEV_Henkin_C_Henkin)
      have typed: "typed_theory \<Gamma> T"
        using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
      have closed: "C_deductively_closed \<Gamma> T"
        using c_henkin by (rule C_Henkin_deductively_closed)
      have A_in: "A \<in> T"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have imp_in: "Imp A B \<in> T"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using typed closed A_in imp_in by (rule C_closed_under_MP)
    qed
  qed
  show ?thesis
    using d henkin by (rule aux)
qed

definition CEV_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_consistent \<Gamma> T \<longleftrightarrow> \<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"

lemma CEV_consistentD:
  assumes "CEV_consistent \<Gamma> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  using assms unfolding CEV_consistent_def by blast

lemma CEV_Henkin_CEV_consistent:
  assumes henkin: "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_consistent \<Gamma> T"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  have false_in: "ObjFalse \<in> T"
    using henkin d_false by (rule CEV_Henkin_closed_under_CEV_set_derivable)
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using henkin by (rule CEV_Henkin_C_Henkin)
  have consistent: "C_consistent \<Gamma> T"
    using c_henkin by (rule C_Henkin_consistent)
  have false_type: "\<Gamma> \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  have "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
    using false_in false_type by (rule C_set_Assumption)
  then show False
    using consistent unfolding C_consistent_def by blast
qed

lemma CEV_consistent_mono:
  assumes "CEV_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "CEV_consistent \<Gamma> T"
  using assms CEV_set_derivable_mono unfolding CEV_consistent_def by blast

lemma CEV_consistent_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "CEV_consistent \<Gamma> T"
proof (unfold CEV_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using assms(1) by (rule CEV_set_ex_falso)
  then show False
    using assms(2) by blast
qed

lemma CEV_consistent_singleton_neg_of_not_proves:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  shows "CEV_consistent \<Gamma> {Neg A}"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; {Neg A} \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule CEV_set_derivable_deduction)
  have imp_false: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg A) ObjFalse"
    using d_imp_false by (rule CEV_set_empty_imp_proves)
  have imp_A: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp (Neg A) ObjFalse) A"
    using assms(1) by (rule CEV_proves_imp_neg_false_to_formula)
  have "\<Gamma> \<turnstile>\<^sub>CEV A"
    using imp_false imp_A by (rule CEV_proves.MP)
  then show False
    using assms(2) by contradiction
qed

lemma CEV_set_derives_ObjFalse_of_formula_and_neg:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "Neg A \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule CEV_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
    using assms(2) neg_type by (rule CEV_set_derivable.Assumption)
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CEV_set_MP)
  show ?thesis
    using d_neg d_imp_false by (rule CEV_set_MP)
qed

lemma CEV_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A (Imp (Neg A) ObjFalse)"
    using taut by (rule CEV_set_Theorem)
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CEV_set_MP)
  show ?thesis
    using assms(2) d_imp_false by (rule CEV_set_MP)
qed

lemma CEV_consistent_not_both_derivable:
  assumes "CEV_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
proof
  assume d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using assms(2) d_neg by (rule CEV_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding CEV_consistent_def by blast
qed

lemma CEV_consistent_not_derives_with_neg:
  assumes "CEV_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
proof
  assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using assms(2) by (rule CEV_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding CEV_consistent_def by blast
qed

lemma CEV_consistent_insert_formula_if_not_neg_derivable:
  assumes "CEV_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
  shows "CEV_consistent \<Gamma> (insert A T)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule CEV_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using CEV_proves_imp_false_to_neg[OF assms(2)] by (rule CEV_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule CEV_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CEV_consistent_insert_neg_if_not_derivable:
  assumes "CEV_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "CEV_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; insert (Neg A) T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Neg A) ObjFalse"
    using neg_type d_false by (rule CEV_set_derivable_deduction)
  have d_A_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Imp (Neg A) ObjFalse) A"
    using CEV_proves_imp_neg_false_to_formula[OF assms(2)] by (rule CEV_set_Theorem)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using d_imp_false d_A_thm by (rule CEV_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CEV_consistent_insert_neg_of_not_set_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "CEV_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have consistent: "CEV_consistent \<Gamma> T"
    using assms by (rule CEV_consistent_of_not_set_derivable)
  show ?thesis
    using consistent assms by (rule CEV_consistent_insert_neg_if_not_derivable)
qed

lemma CEV_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "CEV_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_consistent \<Gamma> (insert A T)"
  shows "CEV_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have d_false: "\<Gamma> ; insert A T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using assms(3) unfolding CEV_consistent_def by blast
  have d_imp_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A ObjFalse"
    using assms(2) d_false by (rule CEV_set_derivable_deduction)
  have d_neg_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Imp A ObjFalse) (Neg A)"
    using CEV_proves_imp_false_to_neg[OF assms(2)] by (rule CEV_set_Theorem)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg A"
    using d_imp_false d_neg_thm by (rule CEV_set_MP)
  have not_d_A: "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  proof
    assume d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
      using d_A d_neg by (rule CEV_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding CEV_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A by (rule CEV_consistent_insert_neg_if_not_derivable)
qed

lemma CEV_consistent_decidable_extension:
  assumes "CEV_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "CEV_consistent \<Gamma> (insert A T) \<or>
    CEV_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "CEV_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis
    by blast
next
  case False
  have "CEV_consistent \<Gamma> (insert (Neg A) T)"
    using assms False by (rule CEV_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis
    by blast
qed

definition CEV_negation_complete :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_negation_complete \<Gamma> T \<longleftrightarrow>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> A \<in> T \<or> Neg A \<in> T)"

definition CEV_locally_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_locally_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> CEV_consistent \<Gamma> T \<and> CEV_negation_complete \<Gamma> T"

lemma CEV_Henkin_locally_maximal_consistent:
  assumes henkin: "CEV_Henkin_theory \<Gamma> T"
  shows "CEV_locally_maximal_consistent \<Gamma> T"
proof -
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using henkin by (rule CEV_Henkin_C_Henkin)
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have consistent: "CEV_consistent \<Gamma> T"
    using henkin by (rule CEV_Henkin_CEV_consistent)
  have c_complete: "C_negation_complete \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have complete: "CEV_negation_complete \<Gamma> T"
    using c_complete unfolding C_negation_complete_def CEV_negation_complete_def by blast
  show ?thesis
    using typed consistent complete
    unfolding CEV_locally_maximal_consistent_def by blast
qed

definition CEV_lindenbaum_step :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if CEV_consistent \<Gamma> (insert A T) then insert A T else insert (Neg A) T)
     else T)"

primrec CEV_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CEV_lindenbaum_chain \<Gamma> T enum 0 = T"
| "CEV_lindenbaum_chain \<Gamma> T enum (Suc n) =
    CEV_lindenbaum_step \<Gamma> (enum n) (CEV_lindenbaum_chain \<Gamma> T enum n)"

definition CEV_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "CEV_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. CEV_lindenbaum_chain \<Gamma> T enum n)"

lemma CEV_lindenbaum_step_extends:
  "T \<subseteq> CEV_lindenbaum_step \<Gamma> A T"
  unfolding CEV_lindenbaum_step_def by auto

lemma CEV_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_lindenbaum_step \<Gamma> A T)"
  using assms unfolding CEV_lindenbaum_step_def typed_theory_def by auto

lemma CEV_lindenbaum_step_consistent:
  assumes "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (CEV_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding CEV_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "CEV_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> unfolding CEV_lindenbaum_step_def by simp
  next
    case False
    have "CEV_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule CEV_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False unfolding CEV_lindenbaum_step_def by simp
  qed
qed

lemma CEV_lindenbaum_chain_step:
  "CEV_lindenbaum_chain \<Gamma> T enum n \<subseteq> CEV_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using CEV_lindenbaum_step_extends[of
      "CEV_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma CEV_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_lindenbaum_step_typed)
qed

lemma CEV_lindenbaum_chain_consistent:
  assumes "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (CEV_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_lindenbaum_step_consistent)
qed

lemma CEV_lindenbaum_extension_extends:
  "T \<subseteq> CEV_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> CEV_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> CEV_lindenbaum_extension \<Gamma> T enum"
    unfolding CEV_lindenbaum_extension_def by blast
qed

lemma CEV_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (CEV_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CEV_lindenbaum_chain_typed)
  then show ?thesis
    unfolding CEV_lindenbaum_extension_def by (rule typed_theory_nat_union)
qed

lemma CEV_lindenbaum_extension_consistent:
  assumes "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false: "\<Gamma> ; CEV_lindenbaum_extension \<Gamma> T enum \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CEV_lindenbaum_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_false by (rule CEV_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. CEV_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding CEV_lindenbaum_extension_def .
  have step: "\<And>n. CEV_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      CEV_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule CEV_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> CEV_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> CEV_lindenbaum_chain \<Gamma> T enum n"
    by blast
  have "\<Gamma> ; CEV_lindenbaum_chain \<Gamma> T enum n \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_set_derivable_mono)
  moreover have "CEV_consistent \<Gamma> (CEV_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CEV_lindenbaum_chain_consistent)
  ultimately show False
    unfolding CEV_consistent_def by blast
qed

lemma CEV_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "CEV_negation_complete \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CEV_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "CEV_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "CEV_lindenbaum_chain \<Gamma> T enum (Suc n) =
      CEV_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> CEV_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> CEV_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "CEV_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> CEV_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding CEV_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> CEV_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding CEV_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> CEV_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> CEV_lindenbaum_extension \<Gamma> T enum"
    unfolding CEV_lindenbaum_extension_def by blast
qed

theorem CEV_lindenbaum_extension_locally_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "CEV_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "CEV_locally_maximal_consistent \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule CEV_lindenbaum_extension_typed)
  have consistent: "CEV_consistent \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule CEV_lindenbaum_extension_consistent)
  have complete: "CEV_negation_complete \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule CEV_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CEV_locally_maximal_consistent_def by simp
qed

lemma CEV_locally_maximal_consistent_deductively_closed:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "A \<in> T"
proof (cases "A \<in> T")
  case True
  then show ?thesis .
next
  case False
  have consistent: "CEV_consistent \<Gamma> T"
    using assms(1) unfolding CEV_locally_maximal_consistent_def by blast
  have complete: "CEV_negation_complete \<Gamma> T"
    using assms(1) unfolding CEV_locally_maximal_consistent_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule CEV_set_derivable_formula)
  have neg_in: "Neg A \<in> T"
    using complete A_type False unfolding CEV_negation_complete_def by blast
  have "\<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using consistent neg_in by (rule CEV_consistent_not_derives_with_neg)
  then show ?thesis
    using assms(2) by blast
qed

lemma CEV_locally_maximal_consistent_contains_theorems:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "A \<in> T"
proof -
  have derivable: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using assms(2) by (rule CEV_set_Theorem)
  show ?thesis
    using assms(1) derivable by (rule CEV_locally_maximal_consistent_deductively_closed)
qed

lemma CEV_locally_maximal_vector_equivalence_closed:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_vector_equivalence_closed \<Gamma> T"
proof (unfold CEV_vector_equivalence_closed_def, intro allI impI)
  fix \<sigma>s F G
  assume F_type: "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type: "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and d: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body \<sigma>s F G"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type \<sigma>s Prop) F G"
    using F_type G_type d by (rule CEV_proves.VectorEquivalence)
  show "Eq (arrow_type \<sigma>s Prop) F G \<in> T"
    using assms d_rule by (rule CEV_locally_maximal_consistent_contains_theorems)
qed

lemma CEV_locally_maximal_context_vector_equivalence_closed:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_context_vector_equivalence_closed \<Gamma> T"
proof (unfold CEV_context_vector_equivalence_closed_def, intro allI impI)
  fix \<sigma>s A F G
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and F_type: "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type: "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and d: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G)"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (arrow_type \<sigma>s Prop) F G)"
    using A_type F_type G_type d by (rule CEV_proves.ContextVectorEquivalence)
  show "Imp A (Eq (arrow_type \<sigma>s Prop) F G) \<in> T"
    using assms d_rule by (rule CEV_locally_maximal_consistent_contains_theorems)
qed

lemma CEV_locally_maximal_generalization_closed:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_generalization_closed \<Gamma> T"
proof (unfold CEV_generalization_closed_def, intro allI impI)
  fix P \<sigma> Q
  assume P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Forall \<sigma> Q)"
    using P_type Q_type d by (rule CEV_proves.Gen)
  show "Imp P (Forall \<sigma> Q) \<in> T"
    using assms d_rule by (rule CEV_locally_maximal_consistent_contains_theorems)
qed

lemma CEV_locally_maximal_instantiation_closed:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_instantiation_closed \<Gamma> T"
proof (unfold CEV_instantiation_closed_def, intro allI impI)
  fix \<sigma> P Q
  assume P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
  have d_rule: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using P_type Q_type d by (rule CEV_proves.Inst)
  show "Imp (Exists \<sigma> P) Q \<in> T"
    using assms d_rule by (rule CEV_locally_maximal_consistent_contains_theorems)
qed

lemma CEV_rule_closed_of_local_maximal:
  assumes "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_rule_closed \<Gamma> T"
proof -
  have vector: "CEV_vector_equivalence_closed \<Gamma> T"
    using assms by (rule CEV_locally_maximal_vector_equivalence_closed)
  have context_vector: "CEV_context_vector_equivalence_closed \<Gamma> T"
    using assms by (rule CEV_locally_maximal_context_vector_equivalence_closed)
  have gen: "CEV_generalization_closed \<Gamma> T"
    using assms by (rule CEV_locally_maximal_generalization_closed)
  have inst: "CEV_instantiation_closed \<Gamma> T"
    using assms by (rule CEV_locally_maximal_instantiation_closed)
  show ?thesis
    using vector context_vector gen inst unfolding CEV_rule_closed_def by blast
qed

lemma CEV_Henkin_theory_of_CE_Henkin_local_maximal:
  assumes "CE_Henkin_theory \<Gamma> T"
    and "CEV_locally_maximal_consistent \<Gamma> T"
  shows "CEV_Henkin_theory \<Gamma> T"
proof -
  have closed: "CEV_rule_closed \<Gamma> T"
    using assms(2) by (rule CEV_rule_closed_of_local_maximal)
  show ?thesis
    using assms(1) closed unfolding CEV_Henkin_theory_def by blast
qed

lemma CEV_Henkin_theory_iff_CE_Henkin_local_maximal:
  "CEV_Henkin_theory \<Gamma> T \<longleftrightarrow>
    CE_Henkin_theory \<Gamma> T \<and> CEV_locally_maximal_consistent \<Gamma> T"
proof
  assume henkin: "CEV_Henkin_theory \<Gamma> T"
  have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    using henkin by (rule CEV_Henkin_CE_Henkin)
  have local: "CEV_locally_maximal_consistent \<Gamma> T"
    using henkin by (rule CEV_Henkin_locally_maximal_consistent)
  show "CE_Henkin_theory \<Gamma> T \<and> CEV_locally_maximal_consistent \<Gamma> T"
    using ce_henkin local by blast
next
  assume pair: "CE_Henkin_theory \<Gamma> T \<and> CEV_locally_maximal_consistent \<Gamma> T"
  from pair have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    by blast
  from pair have local_maximal: "CEV_locally_maximal_consistent \<Gamma> T"
    by blast
  show "CEV_Henkin_theory \<Gamma> T"
    using ce_henkin local_maximal
    by (rule CEV_Henkin_theory_of_CE_Henkin_local_maximal)
qed

inductive CEV_context_equiv_set_derivable :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  Assumption[intro]:
    "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> CEV_context_equiv_set_derivable \<Gamma> T A"
| Theorem[intro]:
    "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> CEV_context_equiv_set_derivable \<Gamma> T A"
| Derive_MP[intro]:
    "CEV_context_equiv_set_derivable \<Gamma> T A \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> T (Imp A B) \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> T B"
| ContextPropEquivalence[intro]:
    "(\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop) \<Longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> T (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)) \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> T (imp_chain Ps (Eq Prop A B))"

lemma CEV_context_equiv_set_derivable_formula:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A T)
  then show ?case
    by (rule CEV_proves_formula)
next
  case (Derive_MP \<Gamma> T A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have eq_type: "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using ContextPropEquivalence.hyps(2,3) by auto
  show ?case
    using ContextPropEquivalence.hyps(1) eq_type by (rule imp_chain_type)
qed

lemma CEV_context_equiv_set_Theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "CEV_context_equiv_set_derivable \<Gamma> T A"
  using assms by (rule CEV_context_equiv_set_derivable.Theorem)

lemma CEV_context_equiv_set_MP:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
    and "CEV_context_equiv_set_derivable \<Gamma> T (Imp A B)"
  shows "CEV_context_equiv_set_derivable \<Gamma> T B"
  using assms by (rule CEV_context_equiv_set_derivable.Derive_MP)

lemma CEV_context_equiv_set_derivable_of_C_set_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
  shows "CEV_context_equiv_set_derivable \<Gamma> T A"
proof -
  have aux: "\<And>\<Gamma> \<Delta> A. \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> (set \<Delta>) A"
  proof -
    fix \<Gamma> \<Delta> A
    assume d: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    then show "CEV_context_equiv_set_derivable \<Gamma> (set \<Delta>) A"
    proof (induction rule: C_derivable.induct)
      case (Assumption A \<Delta> \<Gamma>)
      then show ?case
        by (intro CEV_context_equiv_set_derivable.Assumption) simp_all
    next
      case (Theorem \<Gamma> A \<Delta>)
      have "\<Gamma> \<turnstile>\<^sub>CEV A"
        using Theorem.hyps
        by (intro CEV_proves.CE CE_proves.C)
      then show ?case
        by (rule CEV_context_equiv_set_derivable.Theorem)
    next
      case (Derive_MP \<Gamma> \<Delta> A B)
      show ?case
        using Derive_MP.IH(1) Derive_MP.IH(2)
        by (rule CEV_context_equiv_set_derivable.Derive_MP)
    qed
  qed
  obtain \<Delta> where sub: "set \<Delta> \<subseteq> T"
    and d_list: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    using assms unfolding C_set_derivable_def by blast
  have d_set: "CEV_context_equiv_set_derivable \<Gamma> (set \<Delta>) A"
    using d_list by (rule aux)
  show ?thesis
  proof -
    have mono: "\<And>\<Gamma> T U A. CEV_context_equiv_set_derivable \<Gamma> T A \<Longrightarrow>
        T \<subseteq> U \<Longrightarrow> CEV_context_equiv_set_derivable \<Gamma> U A"
    proof -
      fix \<Gamma> T U A
      assume d: "CEV_context_equiv_set_derivable \<Gamma> T A"
        and T_sub: "T \<subseteq> U"
      then show "CEV_context_equiv_set_derivable \<Gamma> U A"
      proof (induction rule: CEV_context_equiv_set_derivable.induct)
        case (Assumption A T \<Gamma>)
        then show ?case
          by (intro CEV_context_equiv_set_derivable.Assumption) auto
      next
        case (Theorem \<Gamma> A T)
        show ?case
          using Theorem.hyps
          by (rule CEV_context_equiv_set_derivable.Theorem)
      next
        case (Derive_MP \<Gamma> T A B)
        show ?case
          using Derive_MP.IH(1)[OF Derive_MP.prems]
            Derive_MP.IH(2)[OF Derive_MP.prems]
          by (rule CEV_context_equiv_set_derivable.Derive_MP)
      next
        case (ContextPropEquivalence Ps \<Gamma> A B T)
        have d_iff: "CEV_context_equiv_set_derivable \<Gamma> U
            (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
          using ContextPropEquivalence.IH[OF ContextPropEquivalence.prems] .
        show ?case
          using ContextPropEquivalence.hyps(1,2,3) d_iff
          by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
      qed
    qed
    show ?thesis
      using d_set sub by (rule mono)
  qed
qed

lemma CEV_context_equiv_set_derivable_of_CEV_set_derivable:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "CEV_context_equiv_set_derivable \<Gamma> T A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case
    by (rule CEV_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  show ?case
    using Theorem.hyps by (rule CEV_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  show ?case
    using Derive_MP.IH(1) Derive_MP.IH(2)
    by (rule CEV_context_equiv_set_derivable.Derive_MP)
qed

lemma CEV_context_equiv_set_derivable_mono:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
    and "T \<subseteq> U"
  shows "CEV_context_equiv_set_derivable \<Gamma> U A"
proof -
  have aux: "\<And>U. T \<subseteq> U \<Longrightarrow> CEV_context_equiv_set_derivable \<Gamma> U A"
    using assms(1)
  proof (induction arbitrary: U rule: CEV_context_equiv_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    have A_in_U: "A \<in> U"
      using Assumption.hyps(1) Assumption.prems by auto
    show ?case
      using A_in_U Assumption.hyps(2)
      by (rule CEV_context_equiv_set_derivable.Assumption)
  next
    case (Theorem \<Gamma> A T)
    show ?case
      using Theorem.hyps
      by (rule CEV_context_equiv_set_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> T A B)
    have d_A: "CEV_context_equiv_set_derivable \<Gamma> U A"
      using Derive_MP.prems by (rule Derive_MP.IH(1))
    have d_imp: "CEV_context_equiv_set_derivable \<Gamma> U (Imp A B)"
      using Derive_MP.prems by (rule Derive_MP.IH(2))
    show ?case
      using d_A d_imp by (rule CEV_context_equiv_set_derivable.Derive_MP)
  next
    case (ContextPropEquivalence Ps \<Gamma> A B T)
    have d_iff: "CEV_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
      using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
    show ?case
      using ContextPropEquivalence.hyps(1,2,3) d_iff
      by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
  qed
  show ?thesis
    using assms(2) by (rule aux)
qed

lemma CEV_context_equiv_proves_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "CEV_context_equiv_set_derivable \<Gamma> T B"
  shows "CEV_context_equiv_set_derivable \<Gamma> T (Imp A B)"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_context_equiv_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp A B)"
    using assms(1) B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_imp_of_right)
  have d_taut: "CEV_context_equiv_set_derivable \<Gamma> T (Imp B (Imp A B))"
    using taut by (rule CEV_context_equiv_set_Theorem)
  show ?thesis
    using assms(2) d_taut by (rule CEV_context_equiv_set_MP)
qed

lemma CEV_context_equiv_set_derivable_deduction:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and d: "CEV_context_equiv_set_derivable \<Gamma> (insert X T) B"
  shows "CEV_context_equiv_set_derivable \<Gamma> T (Imp X B)"
proof -
  have aux: "\<And>Y S. \<Gamma> \<turnstile> Y : Prop \<Longrightarrow>
      insert X T \<subseteq> insert Y S \<Longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> S (Imp Y B)"
    using d
  proof (induction rule: CEV_context_equiv_set_derivable.induct)
    case (Assumption B U \<Gamma>)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Assumption.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using Assumption.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps(2) .
    show ?case
    proof (cases "B = Y")
      case True
      have h_self: "\<Gamma> \<turnstile>\<^sub>H Imp Y Y"
        using Y_type by (rule H_imp_self)
      have c_self: "\<Gamma> \<turnstile>\<^sub>C Imp Y Y"
        using h_self by (rule C_proves.H)
      have ce_self: "\<Gamma> \<turnstile>\<^sub>CE Imp Y Y"
        using c_self by (rule CE_proves.C)
      have cev_self: "\<Gamma> \<turnstile>\<^sub>CEV Imp Y Y"
        using ce_self by (rule CEV_proves.CE)
      have d_self: "CEV_context_equiv_set_derivable \<Gamma> S (Imp Y Y)"
        using cev_self by (rule CEV_context_equiv_set_derivable.Theorem)
      show ?thesis
        using d_self True by simp
    next
      case False
      have B_in_S: "B \<in> S"
        using Assumption.hyps(1) U_sub False by blast
      have d_B: "CEV_context_equiv_set_derivable \<Gamma> S B"
        using B_in_S B_type by (rule CEV_context_equiv_set_derivable.Assumption)
      show ?thesis
        using Y_type d_B by (rule CEV_context_equiv_proves_imp_of_right)
    qed
  next
    case (Theorem \<Gamma> B U)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Theorem.prems by blast
    have cev_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp Y B"
      using Y_type Theorem.hyps by (rule CEV_proves_imp_of_right)
    show ?case
      using cev_imp by (rule CEV_context_equiv_set_derivable.Theorem)
  next
    case (Derive_MP \<Gamma> U B C)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Derive_MP.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using Derive_MP.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Derive_MP.hyps(1) by (rule CEV_context_equiv_set_derivable_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using Derive_MP.hyps(2)
      by (auto dest: CEV_context_equiv_set_derivable_formula elim: has_type.cases)
    have taut: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using Y_type B_type C_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
          prop_tautology_deduction_mp)
    have d_taut: "CEV_context_equiv_set_derivable \<Gamma> S
        (Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C)))"
      using taut by (rule CEV_context_equiv_set_derivable.Theorem)
    have IH_B: "CEV_context_equiv_set_derivable \<Gamma> S (Imp Y B)"
      using Y_type U_sub by (rule Derive_MP.IH(1))
    have IH_imp: "CEV_context_equiv_set_derivable \<Gamma> S (Imp Y (Imp B C))"
      using Y_type U_sub by (rule Derive_MP.IH(2))
    have step: "CEV_context_equiv_set_derivable \<Gamma> S
        (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using IH_B d_taut by (rule CEV_context_equiv_set_derivable.Derive_MP)
    show ?case
      using IH_imp step by (rule CEV_context_equiv_set_derivable.Derive_MP)
  next
    case (ContextPropEquivalence Ps \<Gamma> A C U)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using ContextPropEquivalence.prems by blast
    have U_sub: "U \<subseteq> insert Y S"
      using ContextPropEquivalence.prems by blast
    have d_cond_raw: "CEV_context_equiv_set_derivable \<Gamma> S
        (Imp Y (imp_chain Ps (A \<longleftrightarrow>\<^sub>o C)))"
      using Y_type U_sub by (rule ContextPropEquivalence.IH)
    then have d_cond: "CEV_context_equiv_set_derivable \<Gamma> S
        (imp_chain (Y # Ps) (A \<longleftrightarrow>\<^sub>o C))"
      by simp
    have typed_prefix: "\<And>P. P \<in> set (Y # Ps) \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
      using Y_type ContextPropEquivalence.hyps(1) by auto
    have d_eq: "CEV_context_equiv_set_derivable \<Gamma> S
        (imp_chain (Y # Ps) (Eq Prop A C))"
      using typed_prefix ContextPropEquivalence.hyps(2,3) d_cond
      by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
    show ?case
      using d_eq by simp
  qed
  show ?thesis
    using assms(1) by (rule aux) blast
qed

lemma CEV_context_equiv_set_derivable_finite_support:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
  obtains U where "finite U" and "U \<subseteq> T" and
    "CEV_context_equiv_set_derivable \<Gamma> U A"
proof -
  have "\<exists>U. finite U \<and> U \<subseteq> T \<and>
      CEV_context_equiv_set_derivable \<Gamma> U A"
    using assms
  proof (induction rule: CEV_context_equiv_set_derivable.induct)
    case (Assumption A T \<Gamma>)
    then show ?case
      by (intro exI[of _ "{A}"]) auto
  next
    case (Theorem \<Gamma> A T)
    then show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (Derive_MP \<Gamma> T A B)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_A: "CEV_context_equiv_set_derivable \<Gamma> U A"
      using Derive_MP.IH(1) by auto
    obtain V where V_fin: "finite V" and V_sub: "V \<subseteq> T"
      and V_imp: "CEV_context_equiv_set_derivable \<Gamma> V (Imp A B)"
      using Derive_MP.IH(2) by auto
    have A_der: "CEV_context_equiv_set_derivable \<Gamma> (U \<union> V) A"
      using U_A by (rule CEV_context_equiv_set_derivable_mono) auto
    have imp_der: "CEV_context_equiv_set_derivable \<Gamma> (U \<union> V) (Imp A B)"
      using V_imp by (rule CEV_context_equiv_set_derivable_mono) auto
    have B_der: "CEV_context_equiv_set_derivable \<Gamma> (U \<union> V) B"
      using A_der imp_der by (rule CEV_context_equiv_set_derivable.Derive_MP)
    show ?case
      using U_fin U_sub V_fin V_sub B_der
      by (intro exI[of _ "U \<union> V"]) auto
  next
    case (ContextPropEquivalence Ps \<Gamma> A B T)
    obtain U where U_fin: "finite U" and U_sub: "U \<subseteq> T"
      and U_iff: "CEV_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
      using ContextPropEquivalence.IH by auto
    have eq_der: "CEV_context_equiv_set_derivable \<Gamma> U
        (imp_chain Ps (Eq Prop A B))"
      using ContextPropEquivalence.hyps(1,2,3) U_iff
      by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
    show ?case
      using U_fin U_sub eq_der by blast
  qed
  then show ?thesis
    using that by blast
qed

lemma CEV_context_equiv_set_derivable_subst_const:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "CEV_context_equiv_set_derivable \<Gamma>
    (subst_const c \<sigma> N ` T) (subst_const c \<sigma> N A)"
  using assms
proof (induction rule: CEV_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems
    by (rule subst_const_preserves_typing)
  have "subst_const c \<sigma> N A \<in> subst_const c \<sigma> N ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using A_sub_type
    by (rule CEV_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule CEV_proves_subst_const)
  then show ?case
    by (rule CEV_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (subst_const c \<sigma> N A)"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (subst_const c \<sigma> N (Imp A B))"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B))"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp
    by (rule CEV_context_equiv_set_derivable.Derive_MP)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have typed_prefix:
      "\<And>P. P \<in> set (map (subst_const c \<sigma> N) Ps) \<Longrightarrow>
        \<Gamma> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set (map (subst_const c \<sigma> N) Ps)"
    then obtain Q where Q_in: "Q \<in> set Ps"
      and P_def: "P = subst_const c \<sigma> N Q"
      by auto
    have "\<Gamma> \<turnstile> subst_const c \<sigma> N Q : Prop"
      using ContextPropEquivalence.hyps(1)[OF Q_in]
        ContextPropEquivalence.prems
      by (rule subst_const_preserves_typing)
    then show "\<Gamma> \<turnstile> P : Prop"
      using P_def by simp
  qed
  have A_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using ContextPropEquivalence.hyps(2) ContextPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have B_sub_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N B : Prop"
    using ContextPropEquivalence.hyps(3) ContextPropEquivalence.prems
    by (rule subst_const_preserves_typing)
  have d_iff_raw:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (subst_const c \<sigma> N (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)))"
    using ContextPropEquivalence.prems
    by (rule ContextPropEquivalence.IH)
  have d_iff:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (imp_chain (map (subst_const c \<sigma> N) Ps)
          (subst_const c \<sigma> N A \<longleftrightarrow>\<^sub>o
            subst_const c \<sigma> N B))"
    using d_iff_raw by simp
  have d_eq:
      "CEV_context_equiv_set_derivable \<Gamma> (subst_const c \<sigma> N ` T)
        (imp_chain (map (subst_const c \<sigma> N) Ps)
          (Eq Prop (subst_const c \<sigma> N A)
            (subst_const c \<sigma> N B)))"
    using typed_prefix A_sub_type B_sub_type d_iff
    by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
  then show ?case
    by simp
qed

lemma CEV_context_equiv_set_derivable_shift:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
    (shift ` T) (shift A)"
  using assms
proof (induction rule: CEV_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have shifted_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using Assumption.hyps(2) by (rule weakening_front)
  have "shift A \<in> shift ` T"
    using Assumption.hyps(1) by simp
  then show ?case
    using shifted_type
    by (rule CEV_context_equiv_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  have "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV rename Suc A"
    using Theorem.hyps by (rule CEV_proves_rename) auto
  then show ?case
    unfolding shift_def
    by (rule CEV_context_equiv_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (shift A)"
    using Derive_MP.IH(1) .
  have d_imp_raw:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (shift (Imp A B))"
    using Derive_MP.IH(2) .
  have d_imp:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (Imp (shift A) (shift B))"
    using d_imp_raw by (simp add: shift_def)
  show ?case
    using d_A d_imp
    by (rule CEV_context_equiv_set_derivable.Derive_MP)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have typed_prefix:
      "\<And>P. P \<in> set (map shift Ps) \<Longrightarrow>
        \<sigma> # \<Gamma> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set (map shift Ps)"
    then obtain Q where Q_in: "Q \<in> set Ps" and P_def: "P = shift Q"
      by auto
    have "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
      using ContextPropEquivalence.hyps(1)[OF Q_in]
      by (rule weakening_front)
    then show "\<sigma> # \<Gamma> \<turnstile> P : Prop"
      using P_def by simp
  qed
  have A_shift_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using ContextPropEquivalence.hyps(2) by (rule weakening_front)
  have B_shift_type: "\<sigma> # \<Gamma> \<turnstile> shift B : Prop"
    using ContextPropEquivalence.hyps(3) by (rule weakening_front)
  have d_iff_raw:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (shift (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)))"
    using ContextPropEquivalence.IH .
  have d_iff:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (imp_chain (map shift Ps) (shift A \<longleftrightarrow>\<^sub>o shift B))"
    using d_iff_raw
    unfolding shift_def
    by simp
  have d_eq:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (imp_chain (map shift Ps) (Eq Prop (shift A) (shift B)))"
    using typed_prefix A_shift_type B_shift_type d_iff
    by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
  then show ?case
    unfolding shift_def
    by simp
qed

lemma CEV_context_equiv_set_derivable_abstract_const:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
    (abstract_const c \<sigma> ` T) (abstract_const c \<sigma> A)"
proof -
  have shifted:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
        (shift ` T) (shift A)"
    using assms by (rule CEV_context_equiv_set_derivable_shift)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have substituted:
      "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
        (subst_const c \<sigma> (Var 0) ` (shift ` T))
        (subst_const c \<sigma> (Var 0) (shift A))"
    using shifted var_type
    by (rule CEV_context_equiv_set_derivable_subst_const)
  have image_eq:
      "subst_const c \<sigma> (Var 0) ` (shift ` T) =
        abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  show ?thesis
    using substituted image_eq
    unfolding abstract_const_def by simp
qed

definition CEV_context_equiv_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_context_equiv_consistent \<Gamma> T \<longleftrightarrow>
    \<not> CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"

lemma CEV_context_equiv_consistentD:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "\<not> CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
  using assms unfolding CEV_context_equiv_consistent_def by blast

lemma CEV_context_equiv_consistent_mono:
  assumes "CEV_context_equiv_consistent \<Gamma> U"
    and "T \<subseteq> U"
  shows "CEV_context_equiv_consistent \<Gamma> T"
  using assms CEV_context_equiv_set_derivable_mono
  unfolding CEV_context_equiv_consistent_def by blast

lemma CEV_context_equiv_consistent_singleton_neg_of_not_derivable:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_context_equiv_set_derivable \<Gamma> {} A"
  shows "CEV_context_equiv_consistent \<Gamma> {Neg A}"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma> {Neg A} ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(1) by auto
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> {}
      (Imp (Neg A) ObjFalse)"
    using neg_type d_false by (rule CEV_context_equiv_set_derivable_deduction)
  have d_A_thm: "CEV_context_equiv_set_derivable \<Gamma> {}
      (Imp (Imp (Neg A) ObjFalse) A)"
    using CEV_proves_imp_neg_false_to_formula[OF assms(1)]
    by (rule CEV_context_equiv_set_Theorem)
  have "CEV_context_equiv_set_derivable \<Gamma> {} A"
    using d_imp_false d_A_thm by (rule CEV_context_equiv_set_MP)
  then show False
    using assms(2) by blast
qed

lemma CEV_consistent_of_CEV_context_equiv_consistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> T"
proof (unfold CEV_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    by (rule CEV_context_equiv_set_derivable_of_CEV_set_derivable)
  then show False
    using assms unfolding CEV_context_equiv_consistent_def by blast
qed

lemma C_consistent_of_CEV_context_equiv_consistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "C_consistent \<Gamma> T"
proof (unfold C_consistent_def, intro notI)
  assume "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s ObjFalse"
  then have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    by (rule CEV_context_equiv_set_derivable_of_C_set_derivable)
  then show False
    using assms unfolding CEV_context_equiv_consistent_def by blast
qed

lemma CEV_context_equiv_set_derives_ObjFalse_of_formula_and_neg:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
    and "Neg A \<in> T"
  shows "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_context_equiv_set_derivable_formula)
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by auto
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp A (Imp (Neg A) ObjFalse))"
    using taut by (rule CEV_context_equiv_set_Theorem)
  have d_neg: "CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using assms(2) neg_type by (rule CEV_context_equiv_set_derivable.Assumption)
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> T (Imp (Neg A) ObjFalse)"
    using assms(1) d_taut by (rule CEV_context_equiv_set_MP)
  show ?thesis
    using d_neg d_imp_false by (rule CEV_context_equiv_set_MP)
qed

lemma CEV_context_equiv_consistent_not_derives_with_neg:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "Neg A \<in> T"
  shows "\<not> CEV_context_equiv_set_derivable \<Gamma> T A"
proof
  assume d_A: "CEV_context_equiv_set_derivable \<Gamma> T A"
  have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using d_A assms(2) by (rule CEV_context_equiv_set_derives_ObjFalse_of_formula_and_neg)
  then show False
    using assms(1) unfolding CEV_context_equiv_consistent_def by blast
qed

lemma CEV_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable:
  assumes "CEV_context_equiv_set_derivable \<Gamma> T A"
    and "CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
  shows "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_context_equiv_set_derivable_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp A (Imp (Neg A) ObjFalse))"
    using taut by (rule CEV_context_equiv_set_Theorem)
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Neg A) ObjFalse)"
    using assms(1) d_taut by (rule CEV_context_equiv_set_MP)
  show ?thesis
    using assms(2) d_imp_false by (rule CEV_context_equiv_set_MP)
qed

lemma CEV_context_equiv_consistent_not_both_derivable:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "\<not> CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
proof
  assume d_neg: "CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
  have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using assms(2) d_neg
    by (rule CEV_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable)
  then show False
    using assms(1) unfolding CEV_context_equiv_consistent_def by blast
qed

lemma CEV_context_equiv_consistent_insert_formula_if_not_neg_derivable:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
  shows "CEV_context_equiv_consistent \<Gamma> (insert A T)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma> (insert A T) ObjFalse"
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> T (Imp A ObjFalse)"
    using assms(2) d_false by (rule CEV_context_equiv_set_derivable_deduction)
  have d_neg_thm: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp A ObjFalse) (Neg A))"
    using CEV_proves_imp_false_to_neg[OF assms(2)]
    by (rule CEV_context_equiv_set_Theorem)
  have "CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using d_imp_false d_neg_thm by (rule CEV_context_equiv_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CEV_context_equiv_consistent_insert_neg_if_not_derivable:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "CEV_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma>
      (insert (Neg A) T) ObjFalse"
  have neg_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using assms(2) by auto
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Neg A) ObjFalse)"
    using neg_type d_false by (rule CEV_context_equiv_set_derivable_deduction)
  have d_A_thm: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp (Neg A) ObjFalse) A)"
    using CEV_proves_imp_neg_false_to_formula[OF assms(2)]
    by (rule CEV_context_equiv_set_Theorem)
  have "CEV_context_equiv_set_derivable \<Gamma> T A"
    using d_imp_false d_A_thm by (rule CEV_context_equiv_set_MP)
  then show False
    using assms(3) by blast
qed

lemma CEV_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_context_equiv_consistent \<Gamma> (insert A T)"
  shows "CEV_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof -
  have d_false: "CEV_context_equiv_set_derivable \<Gamma> (insert A T) ObjFalse"
    using assms(3) unfolding CEV_context_equiv_consistent_def by blast
  have d_imp_false: "CEV_context_equiv_set_derivable \<Gamma> T (Imp A ObjFalse)"
    using assms(2) d_false by (rule CEV_context_equiv_set_derivable_deduction)
  have d_neg_thm: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Imp A ObjFalse) (Neg A))"
    using CEV_proves_imp_false_to_neg[OF assms(2)]
    by (rule CEV_context_equiv_set_Theorem)
  have d_neg: "CEV_context_equiv_set_derivable \<Gamma> T (Neg A)"
    using d_imp_false d_neg_thm by (rule CEV_context_equiv_set_MP)
  have not_d_A: "\<not> CEV_context_equiv_set_derivable \<Gamma> T A"
  proof
    assume d_A: "CEV_context_equiv_set_derivable \<Gamma> T A"
    have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
      using d_A d_neg
      by (rule CEV_context_equiv_set_derives_ObjFalse_of_formula_and_neg_derivable)
    then show False
      using assms(1) unfolding CEV_context_equiv_consistent_def by blast
  qed
  show ?thesis
    using assms(1,2) not_d_A
    by (rule CEV_context_equiv_consistent_insert_neg_if_not_derivable)
qed

lemma CEV_context_equiv_consistent_decidable_extension:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "CEV_context_equiv_consistent \<Gamma> (insert A T) \<or>
    CEV_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
proof (cases "CEV_context_equiv_consistent \<Gamma> (insert A T)")
  case True
  then show ?thesis
    by blast
next
  case False
  have "CEV_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
    using assms False
    by (rule CEV_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent)
  then show ?thesis
    by blast
qed

definition CEV_context_equiv_locally_maximal_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<longleftrightarrow>
    typed_theory \<Gamma> T \<and> CEV_context_equiv_consistent \<Gamma> T \<and>
    CEV_negation_complete \<Gamma> T"

lemma CEV_locally_maximal_consistent_of_CEV_context_equiv:
  assumes "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_locally_maximal_consistent \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using assms unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have context_consistent: "CEV_context_equiv_consistent \<Gamma> T"
    using assms unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have consistent: "CEV_consistent \<Gamma> T"
    using context_consistent by (rule CEV_consistent_of_CEV_context_equiv_consistent)
  have complete: "CEV_negation_complete \<Gamma> T"
    using assms unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  show ?thesis
    using typed consistent complete
    unfolding CEV_locally_maximal_consistent_def by blast
qed

lemma CEV_context_equiv_locally_maximal_consistent_deductively_closed:
  assumes "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "A \<in> T"
proof (cases "A \<in> T")
  case True
  then show ?thesis .
next
  case False
  have consistent: "CEV_context_equiv_consistent \<Gamma> T"
    using assms(1) unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have complete: "CEV_negation_complete \<Gamma> T"
    using assms(1) unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule CEV_context_equiv_set_derivable_formula)
  have neg_in: "Neg A \<in> T"
    using complete A_type False unfolding CEV_negation_complete_def by blast
  have "\<not> CEV_context_equiv_set_derivable \<Gamma> T A"
    using consistent neg_in by (rule CEV_context_equiv_consistent_not_derives_with_neg)
  then show ?thesis
    using assms(2) by blast
qed

lemma CEV_context_equiv_locally_maximal_contains_theorems:
  assumes "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "A \<in> T"
proof -
  have d: "CEV_context_equiv_set_derivable \<Gamma> T A"
    using assms(2) by (rule CEV_context_equiv_set_Theorem)
  show ?thesis
    using assms(1) d
    by (rule CEV_context_equiv_locally_maximal_consistent_deductively_closed)
qed

definition CEV_context_equiv_lindenbaum_step ::
    "ctx \<Rightarrow> oterm \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_context_equiv_lindenbaum_step \<Gamma> A T =
    (if \<Gamma> \<turnstile> A : Prop then
      (if CEV_context_equiv_consistent \<Gamma> (insert A T) then insert A T
       else insert (Neg A) T)
     else T)"

primrec CEV_context_equiv_lindenbaum_chain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum 0 = T"
| "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) =
    CEV_context_equiv_lindenbaum_step \<Gamma> (enum n)
      (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"

definition CEV_context_equiv_lindenbaum_extension ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "CEV_context_equiv_lindenbaum_extension \<Gamma> T enum =
    (\<Union>n. CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"

lemma CEV_context_equiv_lindenbaum_step_extends:
  "T \<subseteq> CEV_context_equiv_lindenbaum_step \<Gamma> A T"
  unfolding CEV_context_equiv_lindenbaum_step_def by auto

lemma CEV_context_equiv_lindenbaum_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_context_equiv_lindenbaum_step \<Gamma> A T)"
  using assms unfolding CEV_context_equiv_lindenbaum_step_def typed_theory_def
  by auto

lemma CEV_context_equiv_lindenbaum_step_consistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma>
    (CEV_context_equiv_lindenbaum_step \<Gamma> A T)"
proof (cases "\<Gamma> \<turnstile> A : Prop")
  case False
  then show ?thesis
    using assms unfolding CEV_context_equiv_lindenbaum_step_def by simp
next
  case True
  show ?thesis
  proof (cases "CEV_context_equiv_consistent \<Gamma> (insert A T)")
    case True
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close>
      unfolding CEV_context_equiv_lindenbaum_step_def by simp
  next
    case False
    have "CEV_context_equiv_consistent \<Gamma> (insert (Neg A) T)"
      using assms \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      by (rule CEV_context_equiv_consistent_insert_neg_if_insert_formula_inconsistent)
    then show ?thesis
      using \<open>\<Gamma> \<turnstile> A : Prop\<close> False
      unfolding CEV_context_equiv_lindenbaum_step_def by simp
  qed
qed

lemma CEV_context_equiv_lindenbaum_chain_step:
  "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n \<subseteq>
    CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
  using CEV_context_equiv_lindenbaum_step_extends[of
      "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n" \<Gamma> "enum n"]
  by simp

lemma CEV_context_equiv_lindenbaum_chain_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_context_equiv_lindenbaum_step_typed)
qed

lemma CEV_context_equiv_lindenbaum_chain_consistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma>
    (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: CEV_context_equiv_lindenbaum_step_consistent)
qed

lemma CEV_context_equiv_lindenbaum_extension_extends:
  "T \<subseteq> CEV_context_equiv_lindenbaum_extension \<Gamma> T enum"
proof
  fix A
  assume "A \<in> T"
  then have "A \<in> CEV_context_equiv_lindenbaum_chain \<Gamma> T enum 0"
    by simp
  then show "A \<in> CEV_context_equiv_lindenbaum_extension \<Gamma> T enum"
    unfolding CEV_context_equiv_lindenbaum_extension_def by blast
qed

lemma CEV_context_equiv_lindenbaum_extension_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof -
  have "\<And>n. typed_theory \<Gamma> (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CEV_context_equiv_lindenbaum_chain_typed)
  then show ?thesis
    unfolding CEV_context_equiv_lindenbaum_extension_def
    by (rule typed_theory_nat_union)
qed

lemma CEV_context_equiv_lindenbaum_extension_consistent:
  assumes "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma>
    (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma>
      (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CEV_context_equiv_lindenbaum_extension \<Gamma> T enum"
    and d_U: "CEV_context_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CEV_context_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using U_sub unfolding CEV_context_equiv_lindenbaum_extension_def .
  have step: "\<And>n. CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n \<subseteq>
      CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
    by (rule CEV_context_equiv_lindenbaum_chain_step)
  have "\<exists>n. U \<subseteq> CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain:
      "U \<subseteq> CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n"
    by blast
  have "CEV_context_equiv_set_derivable \<Gamma>
      (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CEV_context_equiv_set_derivable_mono)
  moreover have "CEV_context_equiv_consistent \<Gamma>
      (CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n)"
    using assms by (rule CEV_context_equiv_lindenbaum_chain_consistent)
  ultimately show False
    unfolding CEV_context_equiv_consistent_def by blast
qed

lemma CEV_context_equiv_lindenbaum_extension_negation_complete:
  assumes "enumerates_formulas \<Gamma> enum"
  shows "CEV_negation_complete \<Gamma>
    (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof (unfold CEV_negation_complete_def, intro allI impI)
  fix A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = A"
    using assms A_type unfolding enumerates_formulas_def by blast
  let ?S = "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum n"
  have step_eq: "CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) =
      CEV_context_equiv_lindenbaum_step \<Gamma> A ?S"
    using enum_n by simp
  have "A \<in> CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n) \<or>
      Neg A \<in> CEV_context_equiv_lindenbaum_chain \<Gamma> T enum (Suc n)"
  proof (cases "CEV_context_equiv_consistent \<Gamma> (insert A ?S)")
    case True
    have "A \<in> CEV_context_equiv_lindenbaum_step \<Gamma> A ?S"
      using A_type True unfolding CEV_context_equiv_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  next
    case False
    have "Neg A \<in> CEV_context_equiv_lindenbaum_step \<Gamma> A ?S"
      using A_type False unfolding CEV_context_equiv_lindenbaum_step_def by simp
    then show ?thesis
      using step_eq by simp
  qed
  then show "A \<in> CEV_context_equiv_lindenbaum_extension \<Gamma> T enum \<or>
      Neg A \<in> CEV_context_equiv_lindenbaum_extension \<Gamma> T enum"
    unfolding CEV_context_equiv_lindenbaum_extension_def by blast
qed

theorem CEV_context_equiv_lindenbaum_extension_locally_maximal_consistent:
  assumes "typed_theory \<Gamma> T"
    and "CEV_context_equiv_consistent \<Gamma> T"
    and "enumerates_formulas \<Gamma> enum"
  shows "CEV_context_equiv_locally_maximal_consistent \<Gamma>
    (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
proof -
  have typed: "typed_theory \<Gamma> (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(1) by (rule CEV_context_equiv_lindenbaum_extension_typed)
  have consistent: "CEV_context_equiv_consistent \<Gamma>
      (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(2) by (rule CEV_context_equiv_lindenbaum_extension_consistent)
  have complete: "CEV_negation_complete \<Gamma>
      (CEV_context_equiv_lindenbaum_extension \<Gamma> T enum)"
    using assms(3) by (rule CEV_context_equiv_lindenbaum_extension_negation_complete)
  show ?thesis
    using typed consistent complete
    unfolding CEV_context_equiv_locally_maximal_consistent_def by simp
qed

theorem CEV_context_equiv_locally_maximal_extension_exists:
  assumes "typed_theory \<Gamma> T"
    and "CEV_context_equiv_consistent \<Gamma> T"
  shows "\<exists>U. T \<subseteq> U \<and> CEV_context_equiv_locally_maximal_consistent \<Gamma> U"
proof -
  obtain enum where enum: "enumerates_formulas \<Gamma> enum"
    using enumerates_formulas_exists by blast
  let ?U = "CEV_context_equiv_lindenbaum_extension \<Gamma> T enum"
  have sub: "T \<subseteq> ?U"
    by (rule CEV_context_equiv_lindenbaum_extension_extends)
  have local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> ?U"
    using assms enum
    by (rule CEV_context_equiv_lindenbaum_extension_locally_maximal_consistent)
  show ?thesis
    using sub local by blast
qed

theorem CEV_context_equiv_locally_maximal_countermodel_extension:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<not> CEV_context_equiv_set_derivable \<Gamma> {} A"
  shows "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Neg A \<in> T"
proof -
  have typed: "typed_theory \<Gamma> {Neg A}"
    using assms(1) unfolding typed_theory_def by auto
  have consistent: "CEV_context_equiv_consistent \<Gamma> {Neg A}"
    using assms by (rule CEV_context_equiv_consistent_singleton_neg_of_not_derivable)
  obtain T where sub: "{Neg A} \<subseteq> T"
    and local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    using CEV_context_equiv_locally_maximal_extension_exists[OF typed consistent]
    by blast
  have neg_in: "Neg A \<in> T"
    using sub by blast
  show ?thesis
    using local neg_in by blast
qed

definition CEV_context_equiv_conservative :: bool where
  "CEV_context_equiv_conservative \<longleftrightarrow>
    (\<forall>\<Gamma> A. CEV_context_equiv_set_derivable \<Gamma> {} A \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV A)"

definition CEV_prefix_equivalence_internalized :: bool where
  "CEV_prefix_equivalence_internalized \<longleftrightarrow>
    (\<forall>\<Gamma> Ps A B.
      (\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop) \<longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (A \<longleftrightarrow>\<^sub>o B) \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (Eq Prop A B))"

definition CEV_nonempty_prefix_equivalence_internalized :: bool where
  "CEV_nonempty_prefix_equivalence_internalized \<longleftrightarrow>
    (\<forall>\<Gamma> P Ps A B.
      (\<forall>R \<in> set (P # Ps). \<Gamma> \<turnstile> R : Prop) \<longrightarrow>
      \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<Gamma> \<turnstile> B : Prop \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV imp_chain (P # Ps) (A \<longleftrightarrow>\<^sub>o B) \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV imp_chain (P # Ps) (Eq Prop A B))"

theorem CEV_nonempty_prefix_equivalence_internalized_holds:
  "CEV_nonempty_prefix_equivalence_internalized"
proof (unfold CEV_nonempty_prefix_equivalence_internalized_def,
    intro allI impI)
  fix \<Gamma> P Ps A B
  assume typed_prefix:
      "\<forall>R \<in> set (P # Ps). \<Gamma> \<turnstile> R : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_chain:
      "\<Gamma> \<turnstile>\<^sub>CEV imp_chain (P # Ps) (A \<longleftrightarrow>\<^sub>o B)"
  let ?C = "conj_prefix P Ps"
  have prefix_types:
      "\<And>R. R \<in> set (P # Ps) \<Longrightarrow> \<Gamma> \<turnstile> R : Prop"
    using typed_prefix by blast
  have bicond_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
  proof -
    have P_type: "\<Gamma> \<turnstile> P : Prop"
      using prefix_types by simp
    have tail_types: "\<And>R. R \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> R : Prop"
      using prefix_types by simp
    show ?thesis
      using P_type tail_types by (rule conj_prefix_type)
  qed
  have chain_to_conj:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (imp_chain (P # Ps) (A \<longleftrightarrow>\<^sub>o B))
          (Imp ?C (A \<longleftrightarrow>\<^sub>o B))"
    using prop_tautology_imp_chain_to_conj_prefix[
      OF prefix_types bicond_type]
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
  have d_conj_bicond: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C (A \<longleftrightarrow>\<^sub>o B)"
    using d_chain chain_to_conj by (rule CEV_proves.MP)
  have d_conj_eq: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?C (Eq Prop A B)"
  proof -
      have zeta:
        "\<Gamma> \<turnstile>\<^sub>CEV
          Imp (shift_by (length ([] :: otype list)) ?C)
            (zeta_body ([] :: otype list) A B)"
      using d_conj_bicond
      by (simp add: zeta_body_def fresh_vars_def)
    have raw:
        "\<Gamma> \<turnstile>\<^sub>CEV
          Imp ?C (Eq (arrow_type ([] :: otype list) Prop) A B)"
    proof (rule CEV_proves.ContextVectorEquivalence[
        where \<sigma>s = "[]"])
      show "\<Gamma> \<turnstile> ?C : Prop"
        by (rule C_type)
      show "\<Gamma> \<turnstile> A : arrow_type [] Prop"
        using A_type by simp
      show "\<Gamma> \<turnstile> B : arrow_type [] Prop"
        using B_type by simp
      show "[] @ \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift_by (length []) ?C) (zeta_body [] A B)"
        using zeta by simp
    qed
    then show ?thesis
      by simp
  qed
  have eq_type: "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using A_type B_type by auto
  have conj_to_chain:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp ?C (Eq Prop A B))
          (imp_chain (P # Ps) (Eq Prop A B))"
    using prop_tautology_conj_prefix_to_imp_chain[
      OF prefix_types eq_type]
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
  show "\<Gamma> \<turnstile>\<^sub>CEV imp_chain (P # Ps) (Eq Prop A B)"
    using d_conj_eq conj_to_chain by (rule CEV_proves.MP)
qed

lemma CEV_prefix_equivalence_internalized_if_nonempty_prefix:
  assumes nonempty: "CEV_nonempty_prefix_equivalence_internalized"
  shows "CEV_prefix_equivalence_internalized"
proof (unfold CEV_prefix_equivalence_internalized_def, intro allI impI)
  fix \<Gamma> Ps A B
  assume typed_prefix: "\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_iff: "\<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
  show "\<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (Eq Prop A B)"
  proof (cases Ps)
    case Nil
    have d_iff': "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
      using d_iff Nil by simp
    have "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
      using A_type B_type d_iff' by (rule CEV_zeroary_equivalence)
    then show ?thesis
      using Nil by simp
  next
    case (Cons P Ps')
    have typed_nonempty: "\<forall>R \<in> set (P # Ps'). \<Gamma> \<turnstile> R : Prop"
      using typed_prefix Cons by simp
    show ?thesis
      using nonempty typed_nonempty A_type B_type d_iff Cons
      unfolding CEV_nonempty_prefix_equivalence_internalized_def by blast
  qed
qed

lemma CEV_nonempty_prefix_equivalence_internalized_if_prefix:
  assumes prefix: "CEV_prefix_equivalence_internalized"
  shows "CEV_nonempty_prefix_equivalence_internalized"
  using prefix unfolding CEV_prefix_equivalence_internalized_def
    CEV_nonempty_prefix_equivalence_internalized_def by blast

theorem CEV_prefix_equivalence_internalized_iff_nonempty_prefix:
  "CEV_prefix_equivalence_internalized \<longleftrightarrow>
    CEV_nonempty_prefix_equivalence_internalized"
  using CEV_prefix_equivalence_internalized_if_nonempty_prefix
    CEV_nonempty_prefix_equivalence_internalized_if_prefix by blast

lemma CEV_prefix_equivalence_internalized_if_context_conservative:
  assumes conservative: "CEV_context_equiv_conservative"
  shows "CEV_prefix_equivalence_internalized"
proof (unfold CEV_prefix_equivalence_internalized_def, intro allI impI)
  fix \<Gamma> Ps A B
  assume typed_prefix: "\<forall>P \<in> set Ps. \<Gamma> \<turnstile> P : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_iff: "\<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
  have d_context_iff: "CEV_context_equiv_set_derivable \<Gamma> {}
      (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
    using d_iff by (rule CEV_context_equiv_set_derivable.Theorem)
  have typed_prefix': "\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    using typed_prefix by blast
  have d_context_eq: "CEV_context_equiv_set_derivable \<Gamma> {}
      (imp_chain Ps (Eq Prop A B))"
    using typed_prefix' A_type B_type d_context_iff
    by (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
  show "\<Gamma> \<turnstile>\<^sub>CEV imp_chain Ps (Eq Prop A B)"
    using conservative d_context_eq
    unfolding CEV_context_equiv_conservative_def by blast
qed

lemma CEV_context_equiv_conservative_if_prefix_equivalence_internalized:
  assumes prefix: "CEV_prefix_equivalence_internalized"
  shows "CEV_context_equiv_conservative"
proof (unfold CEV_context_equiv_conservative_def, intro allI impI)
  fix \<Gamma> A
  assume d: "CEV_context_equiv_set_derivable \<Gamma> {} A"
  have aux: "\<And>\<Delta> T B. CEV_context_equiv_set_derivable \<Delta> T B \<Longrightarrow>
      T = {} \<Longrightarrow> \<Delta> \<turnstile>\<^sub>CEV B"
  proof -
    fix \<Delta> T B
    assume dB: "CEV_context_equiv_set_derivable \<Delta> T B"
    then show "T = {} \<Longrightarrow> \<Delta> \<turnstile>\<^sub>CEV B"
    proof (induction rule: CEV_context_equiv_set_derivable.induct)
      case (Assumption B T \<Delta>)
      then show ?case
        by simp
    next
      case (Theorem \<Delta> B T)
      then show ?case
        by simp
    next
      case (Derive_MP \<Delta> T B C)
      have d_B: "\<Delta> \<turnstile>\<^sub>CEV B"
        using Derive_MP.prems by (rule Derive_MP.IH(1))
      have d_imp: "\<Delta> \<turnstile>\<^sub>CEV Imp B C"
        using Derive_MP.prems by (rule Derive_MP.IH(2))
      show ?case
        using d_B d_imp by (rule CEV_proves.MP)
    next
      case (ContextPropEquivalence Ps \<Delta> B C T)
      have d_iff: "\<Delta> \<turnstile>\<^sub>CEV imp_chain Ps (B \<longleftrightarrow>\<^sub>o C)"
        using ContextPropEquivalence.prems by (rule ContextPropEquivalence.IH)
      show ?case
        using prefix ContextPropEquivalence.hyps(1,2,3) d_iff
        unfolding CEV_prefix_equivalence_internalized_def by blast
    qed
  qed
  show "\<Gamma> \<turnstile>\<^sub>CEV A"
    using d by (rule aux) simp
qed

theorem CEV_context_equiv_conservative_iff_prefix_equivalence_internalized:
  "CEV_context_equiv_conservative \<longleftrightarrow>
    CEV_prefix_equivalence_internalized"
  using CEV_context_equiv_conservative_if_prefix_equivalence_internalized
    CEV_prefix_equivalence_internalized_if_context_conservative by blast

theorem CEV_context_equiv_locally_maximal_countermodel_extension_if_conservative:
  assumes conservative: "CEV_context_equiv_conservative"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Neg A \<in> T"
proof -
  have not_derivable: "\<not> CEV_context_equiv_set_derivable \<Gamma> {} A"
  proof
    assume "CEV_context_equiv_set_derivable \<Gamma> {} A"
    then have "\<Gamma> \<turnstile>\<^sub>CEV A"
      using conservative unfolding CEV_context_equiv_conservative_def by blast
    then show False
      using not_provable by blast
  qed
  show ?thesis
    using A_type not_derivable
    by (rule CEV_context_equiv_locally_maximal_countermodel_extension)
qed

theorem CEV_context_equiv_locally_maximal_countermodel_extension_if_prefix:
  assumes prefix: "CEV_prefix_equivalence_internalized"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Neg A \<in> T"
  using CEV_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
    A_type not_provable
  by (rule CEV_context_equiv_locally_maximal_countermodel_extension_if_conservative)

theorem CEV_context_equiv_locally_maximal_countermodel_extension_if_nonempty_prefix:
  assumes nonempty: "CEV_nonempty_prefix_equivalence_internalized"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Neg A \<in> T"
  using CEV_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
    A_type not_provable
  by (rule CEV_context_equiv_locally_maximal_countermodel_extension_if_prefix)

definition CEV_context_equiv_abstract_const_admissible :: bool where
  "CEV_context_equiv_abstract_const_admissible \<longleftrightarrow>
    (\<forall>\<Gamma> T A c \<sigma>. CEV_context_equiv_set_derivable \<Gamma> T A \<longrightarrow>
      CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (abstract_const c \<sigma> ` T)
        (abstract_const c \<sigma> A))"

theorem CEV_context_equiv_abstract_const_admissible_holds:
  "CEV_context_equiv_abstract_const_admissible"
  unfolding CEV_context_equiv_abstract_const_admissible_def
  using CEV_context_equiv_set_derivable_abstract_const
  by blast

definition CEV_context_equiv_shifted_inst_admissible :: bool where
  "CEV_context_equiv_shifted_inst_admissible \<longleftrightarrow>
    (\<forall>\<Gamma> T \<sigma> P Q. typed_theory \<Gamma> T \<longrightarrow>
      CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
        (Imp P (shift Q)) \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile> P : Prop \<longrightarrow> \<Gamma> \<turnstile> Q : Prop \<longrightarrow>
      CEV_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q))"

lemma CEV_context_equiv_set_derivable_abstract_fresh_witness_false:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and d: "CEV_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
    (insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)) ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (abstract_const c \<sigma> ` insert ?W T) (abstract_const c \<sigma> ObjFalse)"
    using abstraction d unfolding CEV_context_equiv_abstract_const_admissible_def
    by blast
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(3) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(4) by (rule abstract_const_henkin_witness_axiom_fresh)
  have image_eq: "abstract_const c \<sigma> ` insert ?W T =
      insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)"
    using abs_T abs_W by simp
  show ?thesis
    using abs_d image_eq by simp
qed

lemma CEV_context_equiv_set_derivable_fresh_witness_eigen_imp_false:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and d: "CEV_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
    (Imp (Imp (shift (Exists \<sigma> A)) A) ObjFalse)"
proof -
  let ?E = "Imp (shift (Exists \<sigma> A)) A"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(5) by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have E_type: "\<sigma> # \<Gamma> \<turnstile> ?E : Prop"
    using shifted_exists_type assms(5) by auto
  have d_false: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (insert ?E (shift ` T)) ObjFalse"
    using abstraction d assms(3,4)
    by (rule CEV_context_equiv_set_derivable_abstract_fresh_witness_false)
  show ?thesis
    using E_type d_false by (rule CEV_context_equiv_set_derivable_deduction)
qed

lemma CEV_context_equiv_set_derivable_fresh_witness_false:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and typed: "typed_theory \<Gamma> T"
    and d: "CEV_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_imp_false: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp ?P ObjFalse)"
    using abstraction d fresh_T fresh_A A_type
    by (rule CEV_context_equiv_set_derivable_fresh_witness_eigen_imp_false)
  have d_imp_shift_false: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp ?P (shift ObjFalse))"
    using d_imp_false by simp
  have lower: "CEV_context_equiv_set_derivable \<Gamma> T (Imp ?Q ObjFalse)"
    using inst typed d_imp_shift_false P_type typed_ObjFalse
    unfolding CEV_context_equiv_shifted_inst_admissible_def by blast
  have c_Q: "\<Gamma> \<turnstile>\<^sub>C ?Q"
    using A_type by (rule C_proves_exists_imp_shift_exists)
  have cev_Q: "\<Gamma> \<turnstile>\<^sub>CEV ?Q"
    using c_Q by (intro CEV_proves.CE CE_proves.C)
  have d_Q: "CEV_context_equiv_set_derivable \<Gamma> T ?Q"
    using cev_Q by (rule CEV_context_equiv_set_Theorem)
  show ?thesis
    using d_Q lower by (rule CEV_context_equiv_set_MP)
qed

lemma CEV_context_equiv_consistent_insert_fresh_witness_axiom:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CEV_context_equiv_consistent \<Gamma>
    (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d: "CEV_context_equiv_set_derivable \<Gamma>
      (insert (henkin_witness_axiom c \<sigma> A) T) ObjFalse"
  have "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    using abstraction inst typed d fresh_T fresh_A A_type
    by (rule CEV_context_equiv_set_derivable_fresh_witness_false)
  then show False
    using consistent unfolding CEV_context_equiv_consistent_def by blast
qed

lemma CEV_context_equiv_staged_henkin_step_consistent:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CEV_context_equiv_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using abstraction inst typed consistent fresh_T fresh_A True
      by (rule CEV_context_equiv_consistent_insert_fresh_witness_axiom)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma CEV_context_equiv_staged_henkin_chain_consistent:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(3) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(4) by (rule staged_henkin_chain_typed)
  have consistent_n: "CEV_context_equiv_consistent \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1,2) finite_n typed_n consistent_n
    by (simp add: CEV_context_equiv_staged_henkin_step_consistent)
qed

lemma CEV_context_equiv_staged_henkin_extension_consistent:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma>
      (staged_henkin_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "CEV_context_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CEV_context_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  have "\<exists>n. U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain: "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    by blast
  have "CEV_context_equiv_set_derivable \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CEV_context_equiv_set_derivable_mono)
  moreover have "CEV_context_equiv_consistent \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule CEV_context_equiv_staged_henkin_chain_consistent)
  ultimately show False
    unfolding CEV_context_equiv_consistent_def by blast
qed

theorem CEV_context_equiv_available_countermodel_for_context_nonderivable:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> CEV_context_equiv_set_derivable \<Gamma> {} A"
  shows "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
    Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T"
proof -
  let ?T0 = "{Neg A}"
  have finite0: "finite ?T0"
    by simp
  have typed0: "typed_theory \<Gamma> ?T0"
    using A_type unfolding typed_theory_def by auto
  have consistent0: "CEV_context_equiv_consistent \<Gamma> ?T0"
    using A_type not_derivable
    by (rule CEV_context_equiv_consistent_singleton_neg_of_not_derivable)
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?B = "staged_henkin_extension \<Gamma> ?T0 body_enum"
  have T0_sub_B: "?T0 \<subseteq> ?B"
    by (rule staged_henkin_extension_extends)
  have typed_B: "typed_theory \<Gamma> ?B"
    using typed0 by (rule staged_henkin_extension_typed)
  have consistent_B: "CEV_context_equiv_consistent \<Gamma> ?B"
    using abstraction inst finite0 typed0 consistent0
    by (rule CEV_context_equiv_staged_henkin_extension_consistent)
  have available_B: "Henkin_witness_axioms_available \<Gamma> ?B"
    using body_enum by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?U = "CEV_context_equiv_lindenbaum_extension \<Gamma> ?B formula_enum"
  have B_sub_U: "?B \<subseteq> ?U"
    by (rule CEV_context_equiv_lindenbaum_extension_extends)
  have local_U: "CEV_context_equiv_locally_maximal_consistent \<Gamma> ?U"
    using typed_B consistent_B formula_enum
    by (rule CEV_context_equiv_lindenbaum_extension_locally_maximal_consistent)
  have available_U: "Henkin_witness_axioms_available \<Gamma> ?U"
    using available_B B_sub_U by (rule Henkin_witness_axioms_available_mono)
  have neg_in: "Neg A \<in> ?U"
    using T0_sub_B B_sub_U by blast
  show ?thesis
    using local_U available_U neg_in by blast
qed

lemma CEV_context_equiv_set_derivable_shifted_inst_finite:
  assumes conservative: "CEV_context_equiv_conservative"
    and finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and d: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift Q))"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "CEV_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q)"
  using finite_T typed d Q_type
proof (induction T arbitrary: Q rule: finite_induct)
  case empty
  have d_empty: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) {}
      (Imp P (shift Q))"
    using empty.prems(2) by simp
  have cev_imp: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
    using conservative d_empty
    unfolding CEV_context_equiv_conservative_def by blast
  have inst: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using P_type empty.prems(3) cev_imp by (rule CEV_proves.Inst)
  then show ?case
    by (rule CEV_context_equiv_set_Theorem)
next
  case (insert A T)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using insert.prems(1) unfolding typed_theory_def by auto
  have typed_T: "typed_theory \<Gamma> T"
    using insert.prems(1) unfolding typed_theory_def by auto
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using insert.prems(3) by (rule weakening_front)
  have d_insert: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>)
      (insert (shift A) (shift ` T)) (Imp P (shift Q))"
    using insert.prems(2) by simp
  have d_deduct: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp (shift A) (Imp P (shift Q)))"
    using shift_A_type d_insert by (rule CEV_context_equiv_set_derivable_deduction)
  have taut: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_taut: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp (Imp (shift A) (Imp P (shift Q)))
        (Imp P (Imp (shift A) (shift Q))))"
    using taut by (rule CEV_context_equiv_set_Theorem)
  have d_swapped_raw: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (Imp (shift A) (shift Q)))"
    using d_deduct d_taut by (rule CEV_context_equiv_set_MP)
  have shift_imp: "shift (Imp A Q) = Imp (shift A) (shift Q)"
    by (simp add: shift_def)
  have d_swapped: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift (Imp A Q)))"
    using d_swapped_raw by (simp add: shift_imp)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type insert.prems(3) by auto
  have IH: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Exists \<sigma> P) (Imp A Q))"
    using typed_T d_swapped AQ_type by (rule insert.IH)
  let ?E = "Exists \<sigma> P"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using P_type by auto
  have IH_lift: "CEV_context_equiv_set_derivable \<Gamma> (insert A T)
      (Imp ?E (Imp A Q))"
    using IH by (rule CEV_context_equiv_set_derivable_mono) auto
  have IH_lift': "CEV_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T))
      (Imp ?E (Imp A Q))"
    using IH_lift by (rule CEV_context_equiv_set_derivable_mono) auto
  have d_E: "CEV_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) ?E"
    by (intro CEV_context_equiv_set_derivable.Assumption E_type) simp
  have d_A: "CEV_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) A"
    by (intro CEV_context_equiv_set_derivable.Assumption A_type) simp
  have d_imp_AQ: "CEV_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T))
      (Imp A Q)"
    using d_E IH_lift' by (rule CEV_context_equiv_set_MP)
  have d_Q: "CEV_context_equiv_set_derivable \<Gamma> (insert ?E (insert A T)) Q"
    using d_A d_imp_AQ by (rule CEV_context_equiv_set_MP)
  show ?case
    using E_type d_Q by (rule CEV_context_equiv_set_derivable_deduction)
qed

lemma CEV_context_equiv_set_derivable_shifted_inst:
  assumes conservative: "CEV_context_equiv_conservative"
    and typed: "typed_theory \<Gamma> T"
    and d: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` T)
      (Imp P (shift Q))"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "CEV_context_equiv_set_derivable \<Gamma> T (Imp (Exists \<sigma> P) Q)"
proof -
  obtain U where finite_U: "finite U" and U_sub: "U \<subseteq> shift ` T"
    and d_U: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) U
      (Imp P (shift Q))"
    using d by (rule CEV_context_equiv_set_derivable_finite_support)
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> U \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> U"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using U_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  define S where "S = pre ` U"
  have finite_S: "finite S"
    using finite_U unfolding S_def by simp
  have S_sub: "S \<subseteq> T"
    using pre_prop unfolding S_def by auto
  have shift_S: "shift ` S = U"
  proof
    show "shift ` S \<subseteq> U"
    proof
      fix B
      assume "B \<in> shift ` S"
      then obtain C where C_in: "C \<in> U" and B_def: "B = shift (pre C)"
        unfolding S_def by auto
      have "C = shift (pre C)"
        using pre_prop[OF C_in] by simp
      then show "B \<in> U"
        using C_in B_def by simp
    qed
  next
    show "U \<subseteq> shift ` S"
    proof
      fix B
      assume B_in: "B \<in> U"
      have "pre B \<in> S"
        using B_in unfolding S_def by blast
      moreover have "B = shift (pre B)"
        using pre_prop[OF B_in] by simp
      ultimately show "B \<in> shift ` S"
        by blast
    qed
  qed
  have typed_S: "typed_theory \<Gamma> S"
    using typed S_sub unfolding typed_theory_def by blast
  have d_S: "CEV_context_equiv_set_derivable (\<sigma> # \<Gamma>) (shift ` S)
      (Imp P (shift Q))"
    using d_U shift_S by simp
  have lower_S: "CEV_context_equiv_set_derivable \<Gamma> S
      (Imp (Exists \<sigma> P) Q)"
    using conservative finite_S typed_S d_S P_type Q_type
    by (rule CEV_context_equiv_set_derivable_shifted_inst_finite)
  show ?thesis
    using lower_S S_sub by (rule CEV_context_equiv_set_derivable_mono)
qed

theorem CEV_context_equiv_shifted_inst_admissible_if_context_conservative:
  assumes conservative: "CEV_context_equiv_conservative"
  shows "CEV_context_equiv_shifted_inst_admissible"
  using conservative CEV_context_equiv_set_derivable_shifted_inst
  unfolding CEV_context_equiv_shifted_inst_admissible_def by blast

theorem CEV_context_equiv_shifted_inst_admissible_if_prefix_equivalence_internalized:
  assumes prefix: "CEV_prefix_equivalence_internalized"
  shows "CEV_context_equiv_shifted_inst_admissible"
  using CEV_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
  by (rule CEV_context_equiv_shifted_inst_admissible_if_context_conservative)

theorem CEV_context_equiv_shifted_inst_admissible_if_nonempty_prefix:
  assumes nonempty: "CEV_nonempty_prefix_equivalence_internalized"
  shows "CEV_context_equiv_shifted_inst_admissible"
  using CEV_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
  by (rule CEV_context_equiv_shifted_inst_admissible_if_prefix_equivalence_internalized)

lemma CEV_context_equiv_locally_maximal_equivalence_closed:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_equivalence_closed \<Gamma> T"
proof (unfold CE_equivalence_closed_def, intro allI impI)
  fix A B
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and iff_in: "(A \<longleftrightarrow>\<^sub>o B) \<in> T"
  have iff_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have d_iff: "CEV_context_equiv_set_derivable \<Gamma> T (imp_chain [] (A \<longleftrightarrow>\<^sub>o B))"
    using iff_in iff_type by (intro CEV_context_equiv_set_derivable.Assumption) simp_all
  have d_eq: "CEV_context_equiv_set_derivable \<Gamma> T (imp_chain [] (Eq Prop A B))"
  proof (rule CEV_context_equiv_set_derivable.ContextPropEquivalence)
    show "\<And>P. P \<in> set [] \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
      by simp
    show "\<Gamma> \<turnstile> A : Prop"
      using A_type .
    show "\<Gamma> \<turnstile> B : Prop"
      using B_type .
    show "CEV_context_equiv_set_derivable \<Gamma> T (imp_chain [] (A \<longleftrightarrow>\<^sub>o B))"
      using d_iff .
  qed
  have d_eq': "CEV_context_equiv_set_derivable \<Gamma> T (Eq Prop A B)"
    using d_eq by simp
  show "Eq Prop A B \<in> T"
    using local d_eq'
    by (rule CEV_context_equiv_locally_maximal_consistent_deductively_closed)
qed

lemma CE_generalization_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_generalization_closed \<Gamma> T"
proof (unfold CE_generalization_closed_def, intro allI impI)
  fix P \<sigma> Q
  assume P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp (shift P) Q"
  have d_cev: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q"
    using d by (rule CEV_proves.CE)
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Forall \<sigma> Q)"
    using P_type Q_type d_cev by (rule CEV_proves.Gen)
  show "Imp P (Forall \<sigma> Q) \<in> T"
    using local gen by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CE_instantiation_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_instantiation_closed \<Gamma> T"
proof (unfold CE_instantiation_closed_def, intro allI impI)
  fix \<sigma> P Q
  assume P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q)"
  have d_cev: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
    using d by (rule CEV_proves.CE)
  have inst: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using P_type Q_type d_cev by (rule CEV_proves.Inst)
  show "Imp (Exists \<sigma> P) Q \<in> T"
    using local inst by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CE_rule_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CE_rule_closed \<Gamma> T"
proof -
  have equiv: "CE_equivalence_closed \<Gamma> T"
    using local by (rule CEV_context_equiv_locally_maximal_equivalence_closed)
  have gen: "CE_generalization_closed \<Gamma> T"
    using local by (rule CE_generalization_closed_of_CEV_context_equiv_local_maximal)
  have inst: "CE_instantiation_closed \<Gamma> T"
    using local by (rule CE_instantiation_closed_of_CEV_context_equiv_local_maximal)
  show ?thesis
    using equiv gen inst unfolding CE_rule_closed_def by blast
qed

lemma CEV_vector_equivalence_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_vector_equivalence_closed \<Gamma> T"
proof (unfold CEV_vector_equivalence_closed_def, intro allI impI)
  fix \<sigma>s F G
  assume F_type: "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type: "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and d: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body \<sigma>s F G"
  have eq_thm: "\<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type \<sigma>s Prop) F G"
    using F_type G_type d by (rule CEV_proves.VectorEquivalence)
  show "Eq (arrow_type \<sigma>s Prop) F G \<in> T"
    using local eq_thm by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CEV_context_vector_equivalence_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_context_vector_equivalence_closed \<Gamma> T"
proof (unfold CEV_context_vector_equivalence_closed_def, intro allI impI)
  fix \<sigma>s A F G
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and F_type: "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type: "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and d: "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift_by (length \<sigma>s) A) (zeta_body \<sigma>s F G)"
  have eq_thm: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (arrow_type \<sigma>s Prop) F G)"
    using A_type F_type G_type d by (rule CEV_proves.ContextVectorEquivalence)
  show "Imp A (Eq (arrow_type \<sigma>s Prop) F G) \<in> T"
    using local eq_thm by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CEV_generalization_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_generalization_closed \<Gamma> T"
proof (unfold CEV_generalization_closed_def, intro allI impI)
  fix P \<sigma> Q
  assume P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q"
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Forall \<sigma> Q)"
    using P_type Q_type d by (rule CEV_proves.Gen)
  show "Imp P (Forall \<sigma> Q) \<in> T"
    using local gen by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CEV_instantiation_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_instantiation_closed \<Gamma> T"
proof (unfold CEV_instantiation_closed_def, intro allI impI)
  fix \<sigma> P Q
  assume P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
  have inst: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using P_type Q_type d by (rule CEV_proves.Inst)
  show "Imp (Exists \<sigma> P) Q \<in> T"
    using local inst by (rule CEV_context_equiv_locally_maximal_contains_theorems)
qed

lemma CEV_rule_closed_of_CEV_context_equiv_local_maximal:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
  shows "CEV_rule_closed \<Gamma> T"
proof -
  have vector: "CEV_vector_equivalence_closed \<Gamma> T"
    using local by (rule CEV_vector_equivalence_closed_of_CEV_context_equiv_local_maximal)
  have context_vector: "CEV_context_vector_equivalence_closed \<Gamma> T"
    using local by (rule CEV_context_vector_equivalence_closed_of_CEV_context_equiv_local_maximal)
  have gen: "CEV_generalization_closed \<Gamma> T"
    using local by (rule CEV_generalization_closed_of_CEV_context_equiv_local_maximal)
  have inst: "CEV_instantiation_closed \<Gamma> T"
    using local by (rule CEV_instantiation_closed_of_CEV_context_equiv_local_maximal)
  show ?thesis
    using vector context_vector gen inst unfolding CEV_rule_closed_def by blast
qed

lemma Henkin_witnessed_of_CEV_context_equiv_local_maximal_available:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where ax_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using available A_type unfolding Henkin_witness_axioms_available_def by blast
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have ax_type: "\<Gamma> \<turnstile> henkin_witness_axiom c \<sigma> A : Prop"
    using A_type by (rule henkin_witness_axiom_typed)
  have d_exists: "CEV_context_equiv_set_derivable \<Gamma> T (Exists \<sigma> A)"
    using exists_in exists_type by (rule CEV_context_equiv_set_derivable.Assumption)
  have d_ax_raw: "CEV_context_equiv_set_derivable \<Gamma> T (henkin_witness_axiom c \<sigma> A)"
    using ax_in ax_type by (rule CEV_context_equiv_set_derivable.Assumption)
  have d_ax: "CEV_context_equiv_set_derivable \<Gamma> T
      (Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A))"
    using d_ax_raw unfolding henkin_witness_axiom_def by simp
  have d_inst: "CEV_context_equiv_set_derivable \<Gamma> T (subst0 (Const c \<sigma>) A)"
    using d_exists d_ax by (rule CEV_context_equiv_set_MP)
  have inst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using local d_inst by (rule CEV_context_equiv_locally_maximal_consistent_deductively_closed)
  have witness_type: "\<Gamma> \<turnstile> Const c \<sigma> : \<sigma>"
    by auto
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using witness_type inst_in by blast
qed

lemma C_Henkin_theory_of_CEV_context_equiv_local_maximal_available:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "C_Henkin_theory \<Gamma> T"
proof -
  have typed: "typed_theory \<Gamma> T"
    using local unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have context_consistent: "CEV_context_equiv_consistent \<Gamma> T"
    using local unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have c_consistent: "C_consistent \<Gamma> T"
    using context_consistent by (rule C_consistent_of_CEV_context_equiv_consistent)
  have cev_complete: "CEV_negation_complete \<Gamma> T"
    using local unfolding CEV_context_equiv_locally_maximal_consistent_def by blast
  have c_complete: "C_negation_complete \<Gamma> T"
    using cev_complete unfolding CEV_negation_complete_def C_negation_complete_def by blast
  have maximal: "C_maximal_consistent \<Gamma> T"
    using typed c_consistent c_complete
    unfolding C_maximal_consistent_def by blast
  have witnessed: "Henkin_witnessed \<Gamma> T"
    using local available by (rule Henkin_witnessed_of_CEV_context_equiv_local_maximal_available)
  show ?thesis
    using maximal witnessed unfolding C_Henkin_theory_def by blast
qed

lemma CE_Henkin_theory_of_CEV_context_equiv_local_maximal_available:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "CE_Henkin_theory \<Gamma> T"
proof -
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using local available by (rule C_Henkin_theory_of_CEV_context_equiv_local_maximal_available)
  have closed: "CE_rule_closed \<Gamma> T"
    using local by (rule CE_rule_closed_of_CEV_context_equiv_local_maximal)
  show ?thesis
    using c_henkin closed unfolding CE_Henkin_theory_def by blast
qed

lemma CEV_Henkin_theory_of_CEV_context_equiv_local_maximal_available:
  assumes local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "CEV_Henkin_theory \<Gamma> T"
proof -
  have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    using local available by (rule CE_Henkin_theory_of_CEV_context_equiv_local_maximal_available)
  have closed: "CEV_rule_closed \<Gamma> T"
    using local by (rule CEV_rule_closed_of_CEV_context_equiv_local_maximal)
  show ?thesis
    using ce_henkin closed unfolding CEV_Henkin_theory_def by blast
qed

section \<open>Henkin-theory validity and completeness\<close>

text \<open>
  The canonical construction first yields completeness for validity over
  maximal Henkin theories.  This is the exact syntactic form of Henkin
  completeness; the later semantic-realization layer connects it to a concrete
  model interpretation.
\<close>

definition H_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

definition C_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

definition CE_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CE_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

definition CEV_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CEV_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

definition H_Henkin_entails :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_Henkin_entails \<Gamma> \<Delta> A \<longleftrightarrow>
    (\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop) \<and> \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> set \<Delta> \<subseteq> T \<longrightarrow> A \<in> T)"

definition C_Henkin_entails :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_Henkin_entails \<Gamma> \<Delta> A \<longleftrightarrow>
    (\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop) \<and> \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> set \<Delta> \<subseteq> T \<longrightarrow> A \<in> T)"

lemma H_Henkin_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "H_Henkin_valid_in_context \<Gamma> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule H_proves_formula)
  have "\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T"
    using assms by (blast intro: H_Henkin_contains_theorems)
  show ?thesis
    using A_type \<open>\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T\<close>
    unfolding H_Henkin_valid_in_context_def by blast
qed

lemma C_Henkin_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
  shows "C_Henkin_valid_in_context \<Gamma> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule C_proves_formula)
  have "\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T"
    using assms by (blast intro: C_Henkin_contains_theorems)
  show ?thesis
    using A_type \<open>\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T\<close>
    unfolding C_Henkin_valid_in_context_def by blast
qed

lemma CE_Henkin_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "CE_Henkin_valid_in_context \<Gamma> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule CE_proves_formula)
  have "\<forall>T. CE_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T"
    using CE_Henkin_contains_theorems[OF assms] by blast
  show ?thesis
    using A_type \<open>\<forall>T. CE_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T\<close>
    unfolding CE_Henkin_valid_in_context_def by blast
qed

lemma CEV_Henkin_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "CEV_Henkin_valid_in_context \<Gamma> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule CEV_proves_formula)
  have "\<forall>T. CEV_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T"
    using CEV_Henkin_contains_theorems[OF assms] by blast
  show ?thesis
    using A_type \<open>\<forall>T. CEV_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T\<close>
    unfolding CEV_Henkin_valid_in_context_def by blast
qed

definition CE_Henkin_countermodel_property :: bool where
  "CE_Henkin_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      (\<exists>T. CE_Henkin_theory \<Gamma> T \<and> Neg A \<in> T))"

definition CEV_Henkin_countermodel_property :: bool where
  "CEV_Henkin_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow>
      (\<exists>T. CEV_Henkin_theory \<Gamma> T \<and> Neg A \<in> T))"

definition CE_equivalence_saturated_countermodel_property :: bool where
  "CE_equivalence_saturated_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      (\<exists>T. C_Henkin_theory \<Gamma> T \<and>
        CE_locally_maximal_consistent \<Gamma> T \<and>
        CE_equivalence_closed \<Gamma> T \<and> Neg A \<in> T))"

definition CE_equiv_saturated_countermodel_property :: bool where
  "CE_equiv_saturated_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      (\<exists>T. C_Henkin_theory \<Gamma> T \<and>
        CE_equiv_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T))"

definition CE_equiv_available_countermodel_property :: bool where
  "CE_equiv_available_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      (\<exists>T. CE_equiv_locally_maximal_consistent \<Gamma> T \<and>
        Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T))"

definition CE_context_equiv_available_countermodel_property :: bool where
  "CE_context_equiv_available_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      (\<exists>T. CE_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
        Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T))"

definition CEV_locally_saturated_countermodel_property :: bool where
  "CEV_locally_saturated_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow>
      (\<exists>T. CE_Henkin_theory \<Gamma> T \<and>
        CEV_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T))"

definition CEV_context_equiv_available_countermodel_property :: bool where
  "CEV_context_equiv_available_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow>
      (\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
        Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T))"

definition CEV_over_CE_Henkin_extension_property :: bool where
  "CEV_over_CE_Henkin_extension_property \<longleftrightarrow>
    (\<forall>\<Gamma> A T. \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      CE_Henkin_theory \<Gamma> T \<longrightarrow> Neg A \<in> T \<longrightarrow>
      \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow>
      (\<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
        CEV_locally_maximal_consistent \<Gamma> U \<and> Neg A \<in> U))"

definition CEV_CE_Henkin_countermodel_consistency_property :: bool where
  "CEV_CE_Henkin_countermodel_consistency_property \<longleftrightarrow>
    (\<forall>\<Gamma> A T. \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      CE_Henkin_theory \<Gamma> T \<longrightarrow> Neg A \<in> T \<longrightarrow>
      \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow> CEV_consistent \<Gamma> T)"

definition CEV_CE_Henkin_local_extension_property :: bool where
  "CEV_CE_Henkin_local_extension_property \<longleftrightarrow>
    (\<forall>\<Gamma> T. CE_Henkin_theory \<Gamma> T \<longrightarrow> CEV_consistent \<Gamma> T \<longrightarrow>
      (\<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
        CEV_locally_maximal_consistent \<Gamma> U))"

definition CEV_lindenbaum_preserves_CE_Henkin_property :: bool where
  "CEV_lindenbaum_preserves_CE_Henkin_property \<longleftrightarrow>
    (\<forall>\<Gamma> T enum. enumerates_formulas \<Gamma> enum \<longrightarrow>
      CE_Henkin_theory \<Gamma> T \<longrightarrow> CEV_consistent \<Gamma> T \<longrightarrow>
      CE_Henkin_theory \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum))"

theorem CEV_context_equiv_available_countermodel_property_from_context_assumptions:
  assumes conservative: "CEV_context_equiv_conservative"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
proof (unfold CEV_context_equiv_available_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_CEV: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  have not_context: "\<not> CEV_context_equiv_set_derivable \<Gamma> {} A"
  proof
    assume "CEV_context_equiv_set_derivable \<Gamma> {} A"
    then have "\<Gamma> \<turnstile>\<^sub>CEV A"
      using conservative unfolding CEV_context_equiv_conservative_def by blast
    then show False
      using not_CEV by blast
  qed
  show "\<exists>T. CEV_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
      Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T"
    using abstraction inst A_type not_context
    by (rule CEV_context_equiv_available_countermodel_for_context_nonderivable)
qed

theorem CEV_context_equiv_available_countermodel_property_from_conservative_abstraction:
  assumes conservative: "CEV_context_equiv_conservative"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
  using conservative abstraction
    CEV_context_equiv_shifted_inst_admissible_if_context_conservative[
      OF conservative]
  by (rule CEV_context_equiv_available_countermodel_property_from_context_assumptions)

theorem CEV_context_equiv_available_countermodel_property_from_prefix_assumptions:
  assumes prefix: "CEV_prefix_equivalence_internalized"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
  using CEV_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
    abstraction inst
  by (rule CEV_context_equiv_available_countermodel_property_from_context_assumptions)

theorem CEV_context_equiv_available_countermodel_property_from_nonempty_prefix_assumptions:
  assumes nonempty: "CEV_nonempty_prefix_equivalence_internalized"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
  using CEV_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
    abstraction inst
  by (rule CEV_context_equiv_available_countermodel_property_from_prefix_assumptions)

theorem CEV_context_equiv_available_countermodel_property_from_prefix_abstraction:
  assumes prefix: "CEV_prefix_equivalence_internalized"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
  using CEV_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
    abstraction
  by (rule CEV_context_equiv_available_countermodel_property_from_conservative_abstraction)

theorem CEV_context_equiv_available_countermodel_property_from_nonempty_prefix_abstraction:
  assumes nonempty: "CEV_nonempty_prefix_equivalence_internalized"
    and abstraction: "CEV_context_equiv_abstract_const_admissible"
  shows "CEV_context_equiv_available_countermodel_property"
  using CEV_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
    abstraction
  by (rule CEV_context_equiv_available_countermodel_property_from_prefix_abstraction)

theorem CE_context_equiv_available_countermodel_property_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
  shows "CE_context_equiv_available_countermodel_property"
proof (unfold CE_context_equiv_available_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_CE: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  have not_context: "\<not> CE_context_equiv_set_derivable \<Gamma> {} A"
  proof
    assume "CE_context_equiv_set_derivable \<Gamma> {} A"
    then have "\<Gamma> \<turnstile>\<^sub>CE A"
      using conservative unfolding CE_context_equiv_conservative_def by blast
    then show False
      using not_CE by blast
  qed
  show "\<exists>T. CE_context_equiv_locally_maximal_consistent \<Gamma> T \<and>
      Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T"
    using inst A_type not_context
    by (rule CE_context_equiv_available_countermodel_for_context_nonderivable)
qed

theorem CE_context_equiv_available_countermodel_property_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
  shows "CE_context_equiv_available_countermodel_property"
  using inst CE_context_equiv_conservative_if_prefix_equivalence_internalized[OF prefix]
  by (rule CE_context_equiv_available_countermodel_property_from_context_assumptions)

theorem CE_context_equiv_available_countermodel_property_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_context_equiv_available_countermodel_property"
  using inst CE_prefix_equivalence_internalized_if_nonempty_prefix[OF nonempty]
  by (rule CE_context_equiv_available_countermodel_property_from_prefix_assumptions)

theorem CE_context_equiv_available_countermodel_property_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_context_equiv_available_countermodel_property"
  using CE_context_equiv_shifted_inst_admissible_if_nonempty_prefix[OF nonempty]
    nonempty
  by (rule CE_context_equiv_available_countermodel_property_from_nonempty_prefix_assumptions)

lemma CE_equiv_available_countermodel_property_from_context_available:
  assumes "CE_context_equiv_available_countermodel_property"
  shows "CE_equiv_available_countermodel_property"
proof (unfold CE_equiv_available_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtain T where local: "CE_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CE_context_equiv_available_countermodel_property_def by blast
  have equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    using local by (rule CE_equiv_locally_maximal_consistent_of_CE_context_equiv)
  show "\<exists>T. CE_equiv_locally_maximal_consistent \<Gamma> T \<and>
      Henkin_witness_axioms_available \<Gamma> T \<and> Neg A \<in> T"
    using equiv_local available neg_in by blast
qed

lemma CE_equiv_saturated_countermodel_property_from_available:
  assumes "CE_equiv_available_countermodel_property"
  shows "CE_equiv_saturated_countermodel_property"
proof (unfold CE_equiv_saturated_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtain T where local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CE_equiv_available_countermodel_property_def by blast
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using local available by (rule C_Henkin_theory_of_CE_equiv_local_maximal_available)
  show "\<exists>T. C_Henkin_theory \<Gamma> T \<and>
      CE_equiv_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T"
    using c_henkin local neg_in by blast
qed

lemma CE_equivalence_saturated_countermodel_property_from_equiv_saturated:
  assumes "CE_equiv_saturated_countermodel_property"
  shows "CE_equivalence_saturated_countermodel_property"
proof (unfold CE_equivalence_saturated_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtain T where c_henkin: "C_Henkin_theory \<Gamma> T"
    and equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CE_equiv_saturated_countermodel_property_def by blast
  have local: "CE_locally_maximal_consistent \<Gamma> T"
    using equiv_local by (rule CE_locally_maximal_consistent_of_CE_equiv)
  have equiv_closed: "CE_equivalence_closed \<Gamma> T"
    using equiv_local by (rule CE_equiv_locally_maximal_equivalence_closed)
  show "\<exists>T. C_Henkin_theory \<Gamma> T \<and>
      CE_locally_maximal_consistent \<Gamma> T \<and>
      CE_equivalence_closed \<Gamma> T \<and> Neg A \<in> T"
    using c_henkin local equiv_closed neg_in by blast
qed

lemma CE_Henkin_countermodel_property_from_equiv_saturated:
  assumes "CE_equiv_saturated_countermodel_property"
  shows "CE_Henkin_countermodel_property"
proof (unfold CE_Henkin_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtain T where c_henkin: "C_Henkin_theory \<Gamma> T"
    and equiv_local: "CE_equiv_locally_maximal_consistent \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CE_equiv_saturated_countermodel_property_def by blast
  have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    using c_henkin equiv_local
    by (rule CE_Henkin_theory_of_C_Henkin_equiv_local_maximal)
  show "\<exists>T. CE_Henkin_theory \<Gamma> T \<and> Neg A \<in> T"
    using ce_henkin neg_in by blast
qed

lemma CE_Henkin_countermodel_property_from_available:
  assumes "CE_equiv_available_countermodel_property"
  shows "CE_Henkin_countermodel_property"
  using CE_equiv_saturated_countermodel_property_from_available[OF assms]
  by (rule CE_Henkin_countermodel_property_from_equiv_saturated)

lemma CE_Henkin_countermodel_property_from_context_available:
  assumes "CE_context_equiv_available_countermodel_property"
  shows "CE_Henkin_countermodel_property"
  using CE_equiv_available_countermodel_property_from_context_available[OF assms]
  by (rule CE_Henkin_countermodel_property_from_available)

theorem CE_Henkin_countermodel_property_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
  shows "CE_Henkin_countermodel_property"
  using CE_context_equiv_available_countermodel_property_from_context_assumptions[
      OF inst conservative]
  by (rule CE_Henkin_countermodel_property_from_context_available)

theorem CE_Henkin_countermodel_property_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
  shows "CE_Henkin_countermodel_property"
  using CE_context_equiv_available_countermodel_property_from_prefix_assumptions[
      OF inst prefix]
  by (rule CE_Henkin_countermodel_property_from_context_available)

theorem CE_Henkin_countermodel_property_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_Henkin_countermodel_property"
  using CE_context_equiv_available_countermodel_property_from_nonempty_prefix_assumptions[
      OF inst nonempty]
  by (rule CE_Henkin_countermodel_property_from_context_available)

theorem CE_Henkin_countermodel_property_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_Henkin_countermodel_property"
  using CE_context_equiv_available_countermodel_property_from_nonempty_prefix[
      OF nonempty]
  by (rule CE_Henkin_countermodel_property_from_context_available)

lemma CE_Henkin_countermodel_property_from_equivalence_saturated:
  assumes "CE_equivalence_saturated_countermodel_property"
  shows "CE_Henkin_countermodel_property"
proof (unfold CE_Henkin_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtain T where c_henkin: "C_Henkin_theory \<Gamma> T"
    and local: "CE_locally_maximal_consistent \<Gamma> T"
    and equiv: "CE_equivalence_closed \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CE_equivalence_saturated_countermodel_property_def by blast
  have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    using c_henkin local equiv
    by (rule CE_Henkin_theory_of_C_Henkin_local_maximal_equivalence_closed)
  show "\<exists>T. CE_Henkin_theory \<Gamma> T \<and> Neg A \<in> T"
    using ce_henkin neg_in by blast
qed

lemma CEV_Henkin_countermodel_property_from_locally_saturated:
  assumes "CEV_locally_saturated_countermodel_property"
  shows "CEV_Henkin_countermodel_property"
proof (unfold CEV_Henkin_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  obtain T where ce_henkin: "CE_Henkin_theory \<Gamma> T"
    and local: "CEV_locally_maximal_consistent \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CEV_locally_saturated_countermodel_property_def by blast
  have cev_henkin: "CEV_Henkin_theory \<Gamma> T"
    using ce_henkin local by (rule CEV_Henkin_theory_of_CE_Henkin_local_maximal)
  show "\<exists>T. CEV_Henkin_theory \<Gamma> T \<and> Neg A \<in> T"
    using cev_henkin neg_in by blast
qed

lemma CEV_locally_saturated_countermodel_property_from_context_equiv_available:
  assumes "CEV_context_equiv_available_countermodel_property"
  shows "CEV_locally_saturated_countermodel_property"
proof (unfold CEV_locally_saturated_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  obtain T where local: "CEV_context_equiv_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using assms A_type not_provable
    unfolding CEV_context_equiv_available_countermodel_property_def by blast
  have ce_henkin: "CE_Henkin_theory \<Gamma> T"
    using local available by (rule CE_Henkin_theory_of_CEV_context_equiv_local_maximal_available)
  have cev_local: "CEV_locally_maximal_consistent \<Gamma> T"
    using local by (rule CEV_locally_maximal_consistent_of_CEV_context_equiv)
  show "\<exists>T. CE_Henkin_theory \<Gamma> T \<and>
      CEV_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T"
    using ce_henkin cev_local neg_in by blast
qed

lemma CEV_Henkin_countermodel_property_from_context_equiv_available:
  assumes "CEV_context_equiv_available_countermodel_property"
  shows "CEV_Henkin_countermodel_property"
  using CEV_locally_saturated_countermodel_property_from_context_equiv_available[OF assms]
  by (rule CEV_Henkin_countermodel_property_from_locally_saturated)

theorem CEV_CE_Henkin_local_extension_property_from_lindenbaum_preservation:
  assumes preservation: "CEV_lindenbaum_preserves_CE_Henkin_property"
  shows "CEV_CE_Henkin_local_extension_property"
proof (unfold CEV_CE_Henkin_local_extension_property_def, intro allI impI)
  fix \<Gamma> T
  assume ce_henkin: "CE_Henkin_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  have preserve:
    "\<And>\<Gamma> T enum. enumerates_formulas \<Gamma> enum \<Longrightarrow>
      CE_Henkin_theory \<Gamma> T \<Longrightarrow> CEV_consistent \<Gamma> T \<Longrightarrow>
      CE_Henkin_theory \<Gamma> (CEV_lindenbaum_extension \<Gamma> T enum)"
    using preservation
    unfolding CEV_lindenbaum_preserves_CE_Henkin_property_def by simp
  obtain enum where enum: "enumerates_formulas \<Gamma> enum"
    using enumerates_formulas_exists by blast
  let ?U = "CEV_lindenbaum_extension \<Gamma> T enum"
  have sub: "T \<subseteq> ?U"
    by (rule CEV_lindenbaum_extension_extends)
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using ce_henkin by (rule CE_Henkin_C_Henkin)
  have typed: "typed_theory \<Gamma> T"
    using c_henkin unfolding C_Henkin_theory_def C_maximal_consistent_def by blast
  have ce_henkin_U: "CE_Henkin_theory \<Gamma> ?U"
    using enum ce_henkin consistent by (rule preserve)
  have local_U: "CEV_locally_maximal_consistent \<Gamma> ?U"
    using typed consistent enum by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  show "\<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
      CEV_locally_maximal_consistent \<Gamma> U"
  proof (intro exI[where x="?U"] conjI)
    show "T \<subseteq> ?U"
      using sub .
    show "CE_Henkin_theory \<Gamma> ?U"
      using ce_henkin_U .
    show "CEV_locally_maximal_consistent \<Gamma> ?U"
      using local_U .
  qed
qed

theorem CEV_over_CE_Henkin_extension_property_from_consistency_and_local_extension:
  assumes consistency: "CEV_CE_Henkin_countermodel_consistency_property"
    and local_extension: "CEV_CE_Henkin_local_extension_property"
  shows "CEV_over_CE_Henkin_extension_property"
proof (unfold CEV_over_CE_Henkin_extension_property_def, intro allI impI)
  fix \<Gamma> A T
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and ce_henkin: "CE_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    and not_CEV: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  have consistency_rule:
    "\<And>\<Gamma> A T. \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      CE_Henkin_theory \<Gamma> T \<Longrightarrow> Neg A \<in> T \<Longrightarrow>
      \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> CEV_consistent \<Gamma> T"
    using consistency
    unfolding CEV_CE_Henkin_countermodel_consistency_property_def by simp
  have extension_rule:
    "\<And>\<Gamma> T. CE_Henkin_theory \<Gamma> T \<Longrightarrow> CEV_consistent \<Gamma> T \<Longrightarrow>
      \<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
        CEV_locally_maximal_consistent \<Gamma> U"
    using local_extension
    unfolding CEV_CE_Henkin_local_extension_property_def by simp
  have consistent_T: "CEV_consistent \<Gamma> T"
    using A_type ce_henkin neg_in not_CEV by (rule consistency_rule)
  obtain U where sub: "T \<subseteq> U"
    and ce_henkin_U: "CE_Henkin_theory \<Gamma> U"
    and local_U: "CEV_locally_maximal_consistent \<Gamma> U"
    using extension_rule[OF ce_henkin consistent_T] by blast
  show "\<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
      CEV_locally_maximal_consistent \<Gamma> U \<and> Neg A \<in> U"
  proof (intro exI[where x=U] conjI)
    show "T \<subseteq> U"
      using sub .
    show "CE_Henkin_theory \<Gamma> U"
      using ce_henkin_U .
    show "CEV_locally_maximal_consistent \<Gamma> U"
      using local_U .
    show "Neg A \<in> U"
      using neg_in sub by blast
  qed
qed

theorem CEV_over_CE_Henkin_extension_property_from_consistency_and_lindenbaum_preservation:
  assumes consistency: "CEV_CE_Henkin_countermodel_consistency_property"
    and preservation: "CEV_lindenbaum_preserves_CE_Henkin_property"
  shows "CEV_over_CE_Henkin_extension_property"
  using consistency
    CEV_CE_Henkin_local_extension_property_from_lindenbaum_preservation[
      OF preservation]
  by (rule CEV_over_CE_Henkin_extension_property_from_consistency_and_local_extension)

theorem CEV_locally_saturated_countermodel_property_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
  shows "CEV_locally_saturated_countermodel_property"
proof (unfold CEV_locally_saturated_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_CEV: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  have CE_countermodels: "CE_Henkin_countermodel_property"
    using nonempty by (rule CE_Henkin_countermodel_property_from_nonempty_prefix)
  have CE_countermodel:
    "\<And>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow>
      \<exists>T. CE_Henkin_theory \<Gamma> T \<and> Neg A \<in> T"
    using CE_countermodels
    unfolding CE_Henkin_countermodel_property_def by simp
  have extend:
    "\<And>\<Gamma> A T. \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      CE_Henkin_theory \<Gamma> T \<Longrightarrow> Neg A \<in> T \<Longrightarrow>
      \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow>
      \<exists>U. T \<subseteq> U \<and> CE_Henkin_theory \<Gamma> U \<and>
        CEV_locally_maximal_consistent \<Gamma> U \<and> Neg A \<in> U"
    using extension
    unfolding CEV_over_CE_Henkin_extension_property_def by simp
  have not_CE: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  proof
    assume "\<Gamma> \<turnstile>\<^sub>CE A"
    then have "\<Gamma> \<turnstile>\<^sub>CEV A"
      by (rule CEV_proves.CE)
    then show False
      using not_CEV by blast
  qed
  obtain T where ce_henkin: "CE_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using CE_countermodel[OF A_type not_CE] by blast
  obtain U where "T \<subseteq> U"
    and ce_henkin_U: "CE_Henkin_theory \<Gamma> U"
    and local_U: "CEV_locally_maximal_consistent \<Gamma> U"
    and neg_in_U: "Neg A \<in> U"
    using extend[OF A_type ce_henkin neg_in not_CEV] by blast
  show "\<exists>T. CE_Henkin_theory \<Gamma> T \<and>
      CEV_locally_maximal_consistent \<Gamma> T \<and> Neg A \<in> T"
  proof (intro exI conjI)
    show "CE_Henkin_theory \<Gamma> U"
      using ce_henkin_U .
    show "CEV_locally_maximal_consistent \<Gamma> U"
      using local_U .
    show "Neg A \<in> U"
      using neg_in_U .
  qed
qed

theorem CEV_Henkin_countermodel_property_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
  shows "CEV_Henkin_countermodel_property"
  using CEV_locally_saturated_countermodel_property_from_nonempty_prefix_and_extension[
      OF nonempty extension]
  by (rule CEV_Henkin_countermodel_property_from_locally_saturated)

theorem CEV_locally_saturated_countermodel_property_from_nonempty_prefix_consistency_and_local_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and consistency: "CEV_CE_Henkin_countermodel_consistency_property"
    and local_extension: "CEV_CE_Henkin_local_extension_property"
  shows "CEV_locally_saturated_countermodel_property"
  using nonempty
    CEV_over_CE_Henkin_extension_property_from_consistency_and_local_extension[
      OF consistency local_extension]
  by (rule CEV_locally_saturated_countermodel_property_from_nonempty_prefix_and_extension)

theorem CEV_locally_saturated_countermodel_property_from_nonempty_prefix_consistency_and_lindenbaum:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and consistency: "CEV_CE_Henkin_countermodel_consistency_property"
    and preservation: "CEV_lindenbaum_preserves_CE_Henkin_property"
  shows "CEV_locally_saturated_countermodel_property"
  using nonempty
    CEV_over_CE_Henkin_extension_property_from_consistency_and_lindenbaum_preservation[
      OF consistency preservation]
  by (rule CEV_locally_saturated_countermodel_property_from_nonempty_prefix_and_extension)

theorem CE_completeness_from_Henkin_countermodels:
  assumes countermodels: "CE_Henkin_countermodel_property"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CE_Henkin_valid_in_context_def by blast
  obtain T where ce_henkin: "CE_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using countermodels A_type not_provable
    unfolding CE_Henkin_countermodel_property_def by blast
  have A_in: "A \<in> T"
    using valid ce_henkin unfolding CE_Henkin_valid_in_context_def by blast
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using ce_henkin by (rule CE_Henkin_C_Henkin)
  have "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF c_henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem CEV_completeness_from_Henkin_countermodels:
  assumes countermodels: "CEV_Henkin_countermodel_property"
    and valid: "CEV_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CEV_Henkin_valid_in_context_def by blast
  obtain T where cev_henkin: "CEV_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using countermodels A_type not_provable
    unfolding CEV_Henkin_countermodel_property_def by blast
  have A_in: "A \<in> T"
    using valid cev_henkin unfolding CEV_Henkin_valid_in_context_def by blast
  have c_henkin: "C_Henkin_theory \<Gamma> T"
    using cev_henkin by (rule CEV_Henkin_C_Henkin)
  have "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF c_henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem CE_Henkin_valid_in_context_iff_proves_from_countermodels:
  assumes "CE_Henkin_countermodel_property"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
proof
  assume "CE_Henkin_valid_in_context \<Gamma> A"
  with assms show "\<Gamma> \<turnstile>\<^sub>CE A"
    by (rule CE_completeness_from_Henkin_countermodels)
next
  assume "\<Gamma> \<turnstile>\<^sub>CE A"
  then show "CE_Henkin_valid_in_context \<Gamma> A"
    by (rule CE_Henkin_valid_of_proves)
qed

theorem CE_completeness_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_context_assumptions[OF inst conservative] valid
  by (rule CE_completeness_from_Henkin_countermodels)

theorem CE_Henkin_valid_in_context_iff_proves_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_context_assumptions[OF inst conservative]
  by (rule CE_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CE_completeness_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_prefix_assumptions[OF inst prefix] valid
  by (rule CE_completeness_from_Henkin_countermodels)

theorem CE_Henkin_valid_in_context_iff_proves_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_prefix_assumptions[OF inst prefix]
  by (rule CE_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CE_completeness_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix_assumptions[
      OF inst nonempty] valid
  by (rule CE_completeness_from_Henkin_countermodels)

theorem CE_Henkin_valid_in_context_iff_proves_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix_assumptions[
      OF inst nonempty]
  by (rule CE_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CE_completeness_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix[OF nonempty] valid
  by (rule CE_completeness_from_Henkin_countermodels)

theorem CE_Henkin_valid_in_context_iff_proves_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix[OF nonempty]
  by (rule CE_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CE_completeness_from_equiv_saturated_countermodels:
  assumes countermodels: "CE_equiv_saturated_countermodel_property"
    and valid: "CE_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_equiv_saturated[OF countermodels] valid
  by (rule CE_completeness_from_Henkin_countermodels)

theorem CE_Henkin_valid_in_context_iff_proves_from_equiv_saturated_countermodels:
  assumes "CE_equiv_saturated_countermodel_property"
  shows "CE_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_equiv_saturated[OF assms]
  by (rule CE_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CEV_Henkin_valid_in_context_iff_proves_from_countermodels:
  assumes "CEV_Henkin_countermodel_property"
  shows "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
proof
  assume "CEV_Henkin_valid_in_context \<Gamma> A"
  with assms show "\<Gamma> \<turnstile>\<^sub>CEV A"
    by (rule CEV_completeness_from_Henkin_countermodels)
next
  assume "\<Gamma> \<turnstile>\<^sub>CEV A"
  then show "CEV_Henkin_valid_in_context \<Gamma> A"
    by (rule CEV_Henkin_valid_of_proves)
qed

theorem CEV_completeness_from_locally_saturated_countermodels:
  assumes countermodels: "CEV_locally_saturated_countermodel_property"
    and valid: "CEV_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_locally_saturated[OF countermodels] valid
  by (rule CEV_completeness_from_Henkin_countermodels)

theorem CEV_Henkin_valid_in_context_iff_proves_from_locally_saturated_countermodels:
  assumes "CEV_locally_saturated_countermodel_property"
  shows "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_locally_saturated[OF assms]
  by (rule CEV_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CEV_completeness_from_context_equiv_available_countermodels:
  assumes countermodels: "CEV_context_equiv_available_countermodel_property"
    and valid: "CEV_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_context_equiv_available[
      OF countermodels] valid
  by (rule CEV_completeness_from_Henkin_countermodels)

theorem CEV_Henkin_valid_in_context_iff_proves_from_context_equiv_available_countermodels:
  assumes "CEV_context_equiv_available_countermodel_property"
  shows "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_context_equiv_available[OF assms]
  by (rule CEV_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CEV_completeness_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
    and valid: "CEV_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_nonempty_prefix_and_extension[
      OF nonempty extension] valid
  by (rule CEV_completeness_from_Henkin_countermodels)

theorem CEV_Henkin_valid_in_context_iff_proves_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
  shows "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_nonempty_prefix_and_extension[
      OF nonempty extension]
  by (rule CEV_Henkin_valid_in_context_iff_proves_from_countermodels)

lemma H_Henkin_entails_of_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and derivable: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "H_Henkin_entails \<Gamma> \<Delta> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using derivable by (rule H_derivable_formula)
  have contains: "\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> set \<Delta> \<subseteq> T \<longrightarrow> A \<in> T"
  proof (intro allI impI)
    fix T
    assume henkin: "H_Henkin_theory \<Gamma> T"
      and assms_sub: "set \<Delta> \<subseteq> T"
    have set_derivable: "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>H\<^sub>s A"
      using derivable by (rule H_set_derivable_of_list)
    have derivable_T: "\<Gamma> ; T \<turnstile>\<^sub>H\<^sub>s A"
      using set_derivable assms_sub by (rule H_set_derivable_mono)
    show "A \<in> T"
      using henkin derivable_T by (rule H_Henkin_contains_derivable)
  qed
  show ?thesis
    using typed_assms A_type contains
    unfolding H_Henkin_entails_def by blast
qed

lemma C_Henkin_entails_of_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and derivable: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "C_Henkin_entails \<Gamma> \<Delta> A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using derivable by (rule C_derivable_formula)
  have contains: "\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> set \<Delta> \<subseteq> T \<longrightarrow> A \<in> T"
  proof (intro allI impI)
    fix T
    assume henkin: "C_Henkin_theory \<Gamma> T"
      and assms_sub: "set \<Delta> \<subseteq> T"
    have set_derivable: "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>C\<^sub>s A"
      using derivable by (rule C_set_derivable_of_list)
    have derivable_T: "\<Gamma> ; T \<turnstile>\<^sub>C\<^sub>s A"
      using set_derivable assms_sub by (rule C_set_derivable_mono)
    show "A \<in> T"
      using henkin derivable_T by (rule C_Henkin_contains_derivable)
  qed
  show ?thesis
    using typed_assms A_type contains
    unfolding C_Henkin_entails_def by blast
qed

theorem H_completeness_from_Henkin_valid:
  assumes valid: "H_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding H_Henkin_valid_in_context_def by blast
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_unprovable_staged)
  have A_in: "A \<in> T"
    using valid henkin unfolding H_Henkin_valid_in_context_def by blast
  have "A \<notin> T"
    using H_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem C_completeness_from_Henkin_valid:
  assumes valid: "C_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding C_Henkin_valid_in_context_def by blast
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_unprovable_staged)
  have A_in: "A \<in> T"
    using valid henkin unfolding C_Henkin_valid_in_context_def by blast
  have "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem H_strong_completeness_from_Henkin_entails:
  assumes entails: "H_Henkin_entails \<Gamma> \<Delta> A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  have typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using entails unfolding H_Henkin_entails_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails unfolding H_Henkin_entails_def by blast
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_underivable_list_staged)
  have A_in: "A \<in> T"
    using entails henkin assms_sub unfolding H_Henkin_entails_def by blast
  have "A \<notin> T"
    using H_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem C_strong_completeness_from_Henkin_entails:
  assumes entails: "C_Henkin_entails \<Gamma> \<Delta> A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  have typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using entails unfolding C_Henkin_entails_def by blast
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails unfolding C_Henkin_entails_def by blast
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_underivable_list_staged)
  have A_in: "A \<in> T"
    using entails henkin assms_sub unfolding C_Henkin_entails_def by blast
  have "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  then show False
    using A_in by blast
qed

theorem H_Henkin_valid_in_context_iff_proves:
  "H_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>H A"
proof
  assume "H_Henkin_valid_in_context \<Gamma> A"
  then show "\<Gamma> \<turnstile>\<^sub>H A"
    by (rule H_completeness_from_Henkin_valid)
next
  assume "\<Gamma> \<turnstile>\<^sub>H A"
  then show "H_Henkin_valid_in_context \<Gamma> A"
    by (rule H_Henkin_valid_of_proves)
qed

theorem C_Henkin_valid_in_context_iff_proves:
  "C_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume "C_Henkin_valid_in_context \<Gamma> A"
  then show "\<Gamma> \<turnstile>\<^sub>C A"
    by (rule C_completeness_from_Henkin_valid)
next
  assume "\<Gamma> \<turnstile>\<^sub>C A"
  then show "C_Henkin_valid_in_context \<Gamma> A"
    by (rule C_Henkin_valid_of_proves)
qed

theorem H_Henkin_entails_iff_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  shows "H_Henkin_entails \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof
  assume "H_Henkin_entails \<Gamma> \<Delta> A"
  then show "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
    by (rule H_strong_completeness_from_Henkin_entails)
next
  assume derivable: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  show "H_Henkin_entails \<Gamma> \<Delta> A"
    using typed_assms derivable by (rule H_Henkin_entails_of_derivable)
qed

theorem C_Henkin_entails_iff_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  shows "C_Henkin_entails \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof
  assume "C_Henkin_entails \<Gamma> \<Delta> A"
  then show "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
    by (rule C_strong_completeness_from_Henkin_entails)
next
  assume derivable: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  show "C_Henkin_entails \<Gamma> \<Delta> A"
    using typed_assms derivable by (rule C_Henkin_entails_of_derivable)
qed

section \<open>Canonical term-model semantics\<close>

text \<open>
  A canonical Henkin theory determines a concrete general model whose values
  are typed object-language terms in the base context.  An environment is a
  typed term-substitution into that context, evaluation is capture-avoiding
  substitution, and propositional truth is membership in the Henkin theory.
\<close>

definition term_model_domain :: "ctx \<Rightarrow> otype \<Rightarrow> oterm set" where
  "term_model_domain \<Gamma> \<sigma> = {M. \<Gamma> \<turnstile> M : \<sigma>}"

definition term_model_eval :: "oterm env \<Rightarrow> oterm \<Rightarrow> oterm" where
  "term_model_eval s M = subst s M"

definition term_model_holds :: "oterm set \<Rightarrow> oterm \<Rightarrow> bool" where
  "term_model_holds T A \<longleftrightarrow> A \<in> T"

lemma term_model_holds_Var_iff:
  "term_model_holds T (term_model_eval Var A) \<longleftrightarrow> A \<in> T"
  unfolding term_model_holds_def term_model_eval_def
  by (simp add: subst_Var)

lemma term_model_eval_type:
  assumes "\<Delta> \<turnstile> M : \<sigma>"
    and "term_subst_typed \<Delta> \<Gamma> s"
  shows "term_model_eval s M \<in> term_model_domain \<Gamma> \<sigma>"
  using term_subst_preserves_typing[OF assms]
  unfolding term_model_eval_def term_model_domain_def by blast

lemma H_term_model_truth_lemma:
  assumes henkin: "H_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
  shows "term_model_holds T (term_model_eval s A) \<longleftrightarrow>
    H_subst_truth \<Delta> \<Gamma> T s A"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type subst_type
    unfolding term_model_holds_def term_model_eval_def
      H_subst_truth_def H_canonical_truth_def
    by blast
qed

lemma C_term_model_truth_lemma:
  assumes henkin: "C_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and A_type: "\<Delta> \<turnstile> A : Prop"
  shows "term_model_holds T (term_model_eval s A) \<longleftrightarrow>
    C_subst_truth \<Delta> \<Gamma> T s A"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst s A : Prop"
    using A_type s_typed by (rule term_subst_preserves_typing)
  show ?thesis
    using henkin s_typed A_type subst_type
    unfolding term_model_holds_def term_model_eval_def
      C_subst_truth_def C_canonical_truth_def
    by blast
qed

definition H_term_model_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

definition C_term_model_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

definition CE_term_model_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CE_Henkin_theory \<Gamma> T \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

definition CEV_term_model_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CEV_Henkin_theory \<Gamma> T \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

definition H_term_model_entails :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow>
    (\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop) \<and> \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow>
      (\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)) \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

definition C_term_model_entails :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow>
    (\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop) \<and> \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow>
      (\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)) \<longrightarrow>
      term_model_holds T (term_model_eval Var A))"

lemma H_term_model_valid_iff_Henkin_valid:
  "H_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    H_Henkin_valid_in_context \<Gamma> A"
  unfolding H_term_model_valid_in_context_def H_Henkin_valid_in_context_def
    term_model_holds_def term_model_eval_def
  by simp

lemma C_term_model_valid_iff_Henkin_valid:
  "C_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    C_Henkin_valid_in_context \<Gamma> A"
  unfolding C_term_model_valid_in_context_def C_Henkin_valid_in_context_def
    term_model_holds_def term_model_eval_def
  by simp

lemma CE_term_model_valid_iff_Henkin_valid:
  "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    CE_Henkin_valid_in_context \<Gamma> A"
  unfolding CE_term_model_valid_in_context_def CE_Henkin_valid_in_context_def
    term_model_holds_def term_model_eval_def
  by simp

lemma CEV_term_model_valid_iff_Henkin_valid:
  "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow>
    CEV_Henkin_valid_in_context \<Gamma> A"
  unfolding CEV_term_model_valid_in_context_def CEV_Henkin_valid_in_context_def
    term_model_holds_def term_model_eval_def
  by simp

lemma H_term_model_entails_iff_Henkin_entails:
  "H_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow> H_Henkin_entails \<Gamma> \<Delta> A"
  unfolding H_term_model_entails_def H_Henkin_entails_def
    term_model_holds_def term_model_eval_def
  by (auto simp: subst_Var)

lemma C_term_model_entails_iff_Henkin_entails:
  "C_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow> C_Henkin_entails \<Gamma> \<Delta> A"
  unfolding C_term_model_entails_def C_Henkin_entails_def
    term_model_holds_def term_model_eval_def
  by (auto simp: subst_Var)

theorem H_term_model_completeness:
  assumes "H_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
  using assms H_term_model_valid_iff_Henkin_valid
    H_completeness_from_Henkin_valid by blast

theorem C_term_model_completeness:
  assumes "C_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using assms C_term_model_valid_iff_Henkin_valid
    C_completeness_from_Henkin_valid by blast

theorem H_term_model_strong_completeness:
  assumes "H_term_model_entails \<Gamma> \<Delta> A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  using assms H_term_model_entails_iff_Henkin_entails
    H_strong_completeness_from_Henkin_entails by blast

theorem C_term_model_strong_completeness:
  assumes "C_term_model_entails \<Gamma> \<Delta> A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  using assms C_term_model_entails_iff_Henkin_entails
    C_strong_completeness_from_Henkin_entails by blast

theorem H_term_model_valid_iff_proves:
  "H_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>H A"
  using H_term_model_valid_iff_Henkin_valid
    H_Henkin_valid_in_context_iff_proves by blast

theorem C_term_model_valid_iff_proves:
  "C_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
  using C_term_model_valid_iff_Henkin_valid
    C_Henkin_valid_in_context_iff_proves by blast

theorem CE_term_model_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "CE_term_model_valid_in_context \<Gamma> A"
  using CE_Henkin_valid_of_proves[OF assms]
    CE_term_model_valid_iff_Henkin_valid by blast

theorem CEV_term_model_valid_of_proves:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "CEV_term_model_valid_in_context \<Gamma> A"
  using CEV_Henkin_valid_of_proves[OF assms]
    CEV_term_model_valid_iff_Henkin_valid by blast

theorem CE_term_model_completeness_from_Henkin_countermodels:
  assumes countermodels: "CE_Henkin_countermodel_property"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using valid CE_term_model_valid_iff_Henkin_valid
    CE_completeness_from_Henkin_countermodels[OF countermodels] by blast

theorem CE_term_model_completeness_from_equiv_saturated_countermodels:
  assumes countermodels: "CE_equiv_saturated_countermodel_property"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_equiv_saturated[OF countermodels] valid
  by (rule CE_term_model_completeness_from_Henkin_countermodels)

theorem CE_term_model_completeness_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_context_assumptions[OF inst conservative] valid
  by (rule CE_term_model_completeness_from_Henkin_countermodels)

theorem CE_term_model_completeness_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_prefix_assumptions[OF inst prefix] valid
  by (rule CE_term_model_completeness_from_Henkin_countermodels)

theorem CE_term_model_completeness_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix_assumptions[
      OF inst nonempty] valid
  by (rule CE_term_model_completeness_from_Henkin_countermodels)

theorem CE_term_model_completeness_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and valid: "CE_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix[OF nonempty] valid
  by (rule CE_term_model_completeness_from_Henkin_countermodels)

theorem CEV_term_model_completeness_from_Henkin_countermodels:
  assumes countermodels: "CEV_Henkin_countermodel_property"
    and valid: "CEV_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using valid CEV_term_model_valid_iff_Henkin_valid
    CEV_completeness_from_Henkin_countermodels[OF countermodels] by blast

theorem CEV_term_model_completeness_from_locally_saturated_countermodels:
  assumes countermodels: "CEV_locally_saturated_countermodel_property"
    and valid: "CEV_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_locally_saturated[OF countermodels] valid
  by (rule CEV_term_model_completeness_from_Henkin_countermodels)

theorem CEV_term_model_completeness_from_context_equiv_available_countermodels:
  assumes countermodels: "CEV_context_equiv_available_countermodel_property"
    and valid: "CEV_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_context_equiv_available[
      OF countermodels] valid
  by (rule CEV_term_model_completeness_from_Henkin_countermodels)

theorem CEV_term_model_completeness_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
    and valid: "CEV_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_nonempty_prefix_and_extension[
      OF nonempty extension] valid
  by (rule CEV_term_model_completeness_from_Henkin_countermodels)

theorem CE_term_model_valid_iff_proves_from_countermodels:
  assumes "CE_Henkin_countermodel_property"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_term_model_valid_iff_Henkin_valid
    CE_Henkin_valid_in_context_iff_proves_from_countermodels[OF assms] by blast

theorem CE_term_model_valid_iff_proves_from_equiv_saturated_countermodels:
  assumes "CE_equiv_saturated_countermodel_property"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_equiv_saturated[OF assms]
  by (rule CE_term_model_valid_iff_proves_from_countermodels)

theorem CE_term_model_valid_iff_proves_from_context_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and conservative: "CE_context_equiv_conservative"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_context_assumptions[OF inst conservative]
  by (rule CE_term_model_valid_iff_proves_from_countermodels)

theorem CE_term_model_valid_iff_proves_from_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and prefix: "CE_prefix_equivalence_internalized"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_prefix_assumptions[OF inst prefix]
  by (rule CE_term_model_valid_iff_proves_from_countermodels)

theorem CE_term_model_valid_iff_proves_from_nonempty_prefix_assumptions:
  assumes inst: "CE_context_equiv_shifted_inst_admissible"
    and nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix_assumptions[
      OF inst nonempty]
  by (rule CE_term_model_valid_iff_proves_from_countermodels)

theorem CE_term_model_valid_iff_proves_from_nonempty_prefix:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
  shows "CE_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CE A"
  using CE_Henkin_countermodel_property_from_nonempty_prefix[OF nonempty]
  by (rule CE_term_model_valid_iff_proves_from_countermodels)

theorem CEV_term_model_valid_iff_proves_from_countermodels:
  assumes "CEV_Henkin_countermodel_property"
  shows "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_term_model_valid_iff_Henkin_valid
    CEV_Henkin_valid_in_context_iff_proves_from_countermodels[OF assms] by blast

theorem CEV_term_model_valid_iff_proves_from_locally_saturated_countermodels:
  assumes "CEV_locally_saturated_countermodel_property"
  shows "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_locally_saturated[OF assms]
  by (rule CEV_term_model_valid_iff_proves_from_countermodels)

theorem CEV_term_model_valid_iff_proves_from_context_equiv_available_countermodels:
  assumes "CEV_context_equiv_available_countermodel_property"
  shows "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_context_equiv_available[OF assms]
  by (rule CEV_term_model_valid_iff_proves_from_countermodels)

theorem CEV_term_model_valid_iff_proves_from_nonempty_prefix_and_extension:
  assumes nonempty: "CE_nonempty_prefix_equivalence_internalized"
    and extension: "CEV_over_CE_Henkin_extension_property"
  shows "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_from_nonempty_prefix_and_extension[
      OF nonempty extension]
  by (rule CEV_term_model_valid_iff_proves_from_countermodels)

subsection \<open>Unconditional completeness for vector equivalence\<close>

theorem CEV_prefix_equivalence_internalized_holds:
  "CEV_prefix_equivalence_internalized"
  using CEV_nonempty_prefix_equivalence_internalized_holds
  by (rule CEV_prefix_equivalence_internalized_if_nonempty_prefix)

lemma imp_chain_append[simp]:
  "imp_chain (Ps @ Qs) A = imp_chain Ps (imp_chain Qs A)"
  by (induction Ps) simp_all

lemma CEV_set_derivable_imp_chain_discharge:
  assumes typed: "\<And>P. P \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    and d: "\<Gamma> ; set Ps \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV imp_chain (rev Ps) A"
  using typed d
proof (induction Ps arbitrary: A)
  case Nil
  then show ?case
    using CEV_set_empty_imp_proves by simp
next
  case (Cons P Ps)
  have P_type: "\<Gamma> \<turnstile> P : Prop"
    using Cons.prems(1) by simp
  have tail_types: "\<And>Q. Q \<in> set Ps \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop"
    using Cons.prems(1) by simp
  have d_insert: "\<Gamma> ; insert P (set Ps) \<turnstile>\<^sub>CEV\<^sub>s A"
    using Cons.prems(2) by simp
  have d_imp: "\<Gamma> ; set Ps \<turnstile>\<^sub>CEV\<^sub>s Imp P A"
    using P_type d_insert
    by (rule CEV_set_derivable_deduction)
  have "\<Gamma> \<turnstile>\<^sub>CEV imp_chain (rev Ps) (Imp P A)"
    using tail_types d_imp by (rule Cons.IH)
  then show ?case
    by simp
qed

lemma CEV_set_derivable_imp_chain_elim:
  assumes d_chain: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s imp_chain Ps A"
    and d_prefix: "\<And>P. P \<in> set Ps \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s P"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  using assms
proof (induction Ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons P Ps)
  have d_P: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s P"
    using Cons.prems(2) by simp
  have d_imp:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp P (imp_chain Ps A)"
    using Cons.prems(1) by simp
  have d_tail: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s imp_chain Ps A"
    using d_P d_imp
    by (rule CEV_set_derivable.Derive_MP)
  show ?case
    using d_tail Cons.prems(2) by (rule Cons.IH) simp
qed

theorem CEV_context_equiv_set_derivable_conservative:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "CEV_context_equiv_set_derivable \<Gamma> T A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  using d typed
proof (induction rule: CEV_context_equiv_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  show ?case
    using Assumption.hyps(1,2)
    by (rule CEV_set_derivable.Assumption)
next
  case (Theorem \<Gamma> A T)
  show ?case
    using Theorem.hyps
    by (rule CEV_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  show ?case
    using d_A d_imp by (rule CEV_set_derivable.Derive_MP)
next
  case (ContextPropEquivalence Ps \<Gamma> A B T)
  have d_iff: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
      imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
    using ContextPropEquivalence.prems
    by (rule ContextPropEquivalence.IH)
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> T"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s
      imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
    using d_iff by (rule CEV_set_derivable_finite_support)
  obtain Us where set_Us: "set Us = U"
    using finite_U finite_list by metis
  have typed_Us: "\<And>P. P \<in> set Us \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    using ContextPropEquivalence.prems U_sub set_Us
    unfolding typed_theory_def by blast
  have d_Us: "\<Gamma> ; set Us \<turnstile>\<^sub>CEV\<^sub>s
      imp_chain Ps (A \<longleftrightarrow>\<^sub>o B)"
    using d_U set_Us by simp
  have theorem_nested:
      "\<Gamma> \<turnstile>\<^sub>CEV
        imp_chain (rev Us) (imp_chain Ps (A \<longleftrightarrow>\<^sub>o B))"
    using typed_Us d_Us
    by (rule CEV_set_derivable_imp_chain_discharge)
  have theorem_iff:
      "\<Gamma> \<turnstile>\<^sub>CEV
        imp_chain (rev Us @ Ps) (A \<longleftrightarrow>\<^sub>o B)"
    using theorem_nested by simp
  have typed_combined:
      "\<And>P. P \<in> set (rev Us @ Ps) \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
    using typed_Us ContextPropEquivalence.hyps(1) by auto
  have theorem_eq:
      "\<Gamma> \<turnstile>\<^sub>CEV imp_chain (rev Us @ Ps) (Eq Prop A B)"
  proof -
    have prefix_rule:
        "\<And>\<Delta> Qs C D.
          (\<And>Q. Q \<in> set Qs \<Longrightarrow> \<Delta> \<turnstile> Q : Prop) \<Longrightarrow>
          \<Delta> \<turnstile> C : Prop \<Longrightarrow>
          \<Delta> \<turnstile> D : Prop \<Longrightarrow>
          \<Delta> \<turnstile>\<^sub>CEV imp_chain Qs (C \<longleftrightarrow>\<^sub>o D) \<Longrightarrow>
          \<Delta> \<turnstile>\<^sub>CEV imp_chain Qs (Eq Prop C D)"
      using CEV_prefix_equivalence_internalized_holds
      unfolding CEV_prefix_equivalence_internalized_def by blast
    show ?thesis
      using typed_combined ContextPropEquivalence.hyps(2,3) theorem_iff
      by (rule prefix_rule)
  qed
  have local_eq_raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        imp_chain (rev Us @ Ps) (Eq Prop A B)"
    using theorem_eq by (rule CEV_set_derivable.Theorem)
  have local_eq:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        imp_chain (rev Us) (imp_chain Ps (Eq Prop A B))"
    using local_eq_raw by simp
  have local_assms:
      "\<And>P. P \<in> set (rev Us) \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s P"
  proof -
    fix P
    assume P_in: "P \<in> set (rev Us)"
    have P_type: "\<Gamma> \<turnstile> P : Prop"
      using typed_Us P_in by simp
    have "P \<in> T"
      using P_in set_Us U_sub by auto
    then show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s P"
      using P_type by (rule CEV_set_derivable.Assumption)
  qed
  show ?case
    using local_eq local_assms by (rule CEV_set_derivable_imp_chain_elim)
qed

theorem CEV_context_equiv_conservative_holds:
  "CEV_context_equiv_conservative"
  using CEV_prefix_equivalence_internalized_holds
  by (rule CEV_context_equiv_conservative_if_prefix_equivalence_internalized)

theorem CEV_context_equiv_shifted_inst_admissible_holds:
  "CEV_context_equiv_shifted_inst_admissible"
  using CEV_context_equiv_conservative_holds
  by (rule CEV_context_equiv_shifted_inst_admissible_if_context_conservative)

theorem CEV_context_equiv_consistent_iff_CEV_consistent:
  assumes "typed_theory \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> T \<longleftrightarrow> CEV_consistent \<Gamma> T"
proof
  assume "CEV_context_equiv_consistent \<Gamma> T"
  then show "CEV_consistent \<Gamma> T"
    by (rule CEV_consistent_of_CEV_context_equiv_consistent)
next
  assume consistent: "CEV_consistent \<Gamma> T"
  show "CEV_context_equiv_consistent \<Gamma> T"
  proof (unfold CEV_context_equiv_consistent_def, intro notI)
    assume d_context: "CEV_context_equiv_set_derivable \<Gamma> T ObjFalse"
    have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
      using assms d_context
      by (rule CEV_context_equiv_set_derivable_conservative)
    then show False
      using consistent unfolding CEV_consistent_def by blast
  qed
qed

lemma consts_of_set_insert[simp]:
  "consts_of_set (insert A T) = consts_of A \<union> consts_of_set T"
  unfolding consts_of_set_def by auto

lemma fresh_const_for_finite_consts:
  assumes "finite (consts_of_set T)"
  obtains c where "fresh_const_for c T A"
proof -
  have finite_support: "finite (consts_of_set T \<union> consts_of A)"
    using assms by simp
  obtain c where "c \<notin> consts_of_set T \<union> consts_of A"
    using fresh_string_finite[OF finite_support] by blast
  then have "fresh_const_for c T A"
    unfolding fresh_const_for_def by blast
  then show ?thesis
    using that by blast
qed

lemma fresh_const_for_stage_fresh_finite_consts:
  assumes "finite (consts_of_set T)"
  shows "fresh_const_for (fresh_const_for_stage T A) T A"
  unfolding fresh_const_for_stage_def
  using fresh_const_for_finite_consts[OF assms, of A]
  by (metis someI_ex)

lemma staged_henkin_step_finite_consts:
  assumes "finite (consts_of_set T)"
  shows "finite (consts_of_set (staged_henkin_step \<Gamma> spec T))"
  using assms
  unfolding staged_henkin_step_def
  by (cases spec) auto

lemma staged_henkin_chain_finite_consts:
  assumes "finite (consts_of_set T)"
  shows "finite (consts_of_set (staged_henkin_chain \<Gamma> T enum n))"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (simp add: staged_henkin_step_finite_consts)
qed

lemma CEV_context_equiv_staged_henkin_step_consistent_finite_consts:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_consts: "finite (consts_of_set T)"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_consts by (rule fresh_const_for_stage_fresh_finite_consts)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CEV_context_equiv_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using abstraction inst typed consistent fresh_T fresh_A True
      by (rule CEV_context_equiv_consistent_insert_fresh_witness_axiom)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma CEV_context_equiv_staged_henkin_chain_consistent_finite_consts:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_consts: "finite (consts_of_set T)"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have finite_consts_n:
      "finite (consts_of_set (staged_henkin_chain \<Gamma> T enum n))"
    using Suc.prems(3) by (rule staged_henkin_chain_finite_consts)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(4) by (rule staged_henkin_chain_typed)
  have consistent_n: "CEV_context_equiv_consistent \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1,2) finite_consts_n typed_n consistent_n
    by (simp add:
        CEV_context_equiv_staged_henkin_step_consistent_finite_consts)
qed

lemma CEV_context_equiv_staged_henkin_extension_consistent_finite_consts:
  assumes abstraction: "CEV_context_equiv_abstract_const_admissible"
    and inst: "CEV_context_equiv_shifted_inst_admissible"
    and finite_consts: "finite (consts_of_set T)"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_context_equiv_consistent \<Gamma> T"
  shows "CEV_context_equiv_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold CEV_context_equiv_consistent_def, intro notI)
  assume d_false: "CEV_context_equiv_set_derivable \<Gamma>
      (staged_henkin_extension \<Gamma> T enum) ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "CEV_context_equiv_set_derivable \<Gamma> U ObjFalse"
    using d_false by (rule CEV_context_equiv_set_derivable_finite_support)
  have U_sub_union: "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  have "\<exists>n. U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step by (rule finite_subset_nat_chain)
  then obtain n where U_sub_chain:
      "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    by blast
  have d_chain: "CEV_context_equiv_set_derivable \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n) ObjFalse"
    using d_U U_sub_chain by (rule CEV_context_equiv_set_derivable_mono)
  have consistent_chain: "CEV_context_equiv_consistent \<Gamma>
      (staged_henkin_chain \<Gamma> T enum n)"
    using assms
    by (rule CEV_context_equiv_staged_henkin_chain_consistent_finite_consts)
  show False
    using d_chain consistent_chain
    unfolding CEV_context_equiv_consistent_def by blast
qed

theorem CEV_Henkin_extension_exists:
  assumes typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
    and finite_consts: "finite (consts_of_set T)"
  shows "\<exists>U. T \<subseteq> U \<and> CEV_Henkin_theory \<Gamma> U"
proof -
  have context_consistent: "CEV_context_equiv_consistent \<Gamma> T"
    using typed consistent
    by (simp add: CEV_context_equiv_consistent_iff_CEV_consistent)
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?B = "staged_henkin_extension \<Gamma> T body_enum"
  have T_sub_B: "T \<subseteq> ?B"
    by (rule staged_henkin_extension_extends)
  have typed_B: "typed_theory \<Gamma> ?B"
    using typed by (rule staged_henkin_extension_typed)
  have consistent_B: "CEV_context_equiv_consistent \<Gamma> ?B"
    using CEV_context_equiv_abstract_const_admissible_holds
      CEV_context_equiv_shifted_inst_admissible_holds
      finite_consts typed context_consistent
    by (rule
        CEV_context_equiv_staged_henkin_extension_consistent_finite_consts)
  have available_B: "Henkin_witness_axioms_available \<Gamma> ?B"
    using body_enum by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?U = "CEV_context_equiv_lindenbaum_extension \<Gamma> ?B formula_enum"
  have B_sub_U: "?B \<subseteq> ?U"
    by (rule CEV_context_equiv_lindenbaum_extension_extends)
  have local_U: "CEV_context_equiv_locally_maximal_consistent \<Gamma> ?U"
    using typed_B consistent_B formula_enum
    by (rule CEV_context_equiv_lindenbaum_extension_locally_maximal_consistent)
  have available_U: "Henkin_witness_axioms_available \<Gamma> ?U"
    using available_B B_sub_U by (rule Henkin_witness_axioms_available_mono)
  have henkin_U: "CEV_Henkin_theory \<Gamma> ?U"
    using local_U available_U
    by (rule CEV_Henkin_theory_of_CEV_context_equiv_local_maximal_available)
  show ?thesis
    using T_sub_B B_sub_U henkin_U by blast
qed

theorem CEV_context_equiv_available_countermodel_property_holds:
  "CEV_context_equiv_available_countermodel_property"
  using CEV_context_equiv_conservative_holds
    CEV_context_equiv_abstract_const_admissible_holds
  by (rule
      CEV_context_equiv_available_countermodel_property_from_conservative_abstraction)

theorem CEV_Henkin_countermodel_property_holds:
  "CEV_Henkin_countermodel_property"
  using CEV_context_equiv_available_countermodel_property_holds
  by (rule CEV_Henkin_countermodel_property_from_context_equiv_available)

theorem CEV_Henkin_completeness:
  assumes "CEV_Henkin_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_holds assms
  by (rule CEV_completeness_from_Henkin_countermodels)

theorem CEV_Henkin_valid_in_context_iff_proves:
  "CEV_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_holds
  by (rule CEV_Henkin_valid_in_context_iff_proves_from_countermodels)

theorem CEV_term_model_completeness:
  assumes "CEV_term_model_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_holds assms
  by (rule CEV_term_model_completeness_from_Henkin_countermodels)

theorem CEV_term_model_valid_iff_proves:
  "CEV_term_model_valid_in_context \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
  using CEV_Henkin_countermodel_property_holds
  by (rule CEV_term_model_valid_iff_proves_from_countermodels)

theorem H_term_model_entails_iff_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  shows "H_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  using H_term_model_entails_iff_Henkin_entails
    H_Henkin_entails_iff_derivable[OF typed_assms] by blast

theorem C_term_model_entails_iff_derivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  shows "C_term_model_entails \<Gamma> \<Delta> A \<longleftrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  using C_term_model_entails_iff_Henkin_entails
    C_Henkin_entails_iff_derivable[OF typed_assms] by blast

theorem H_term_model_countermodel_for_unprovable:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>H A"
  obtains T where "H_Henkin_theory \<Gamma> T"
    and "term_model_holds T (term_model_eval Var (Neg A))"
    and "\<not> term_model_holds T (term_model_eval Var A)"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_unprovable_staged)
  have not_A: "A \<notin> T"
    using H_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  have neg_holds: "term_model_holds T (term_model_eval Var (Neg A))"
    using neg_in by (simp add: term_model_holds_Var_iff)
  have not_holds: "\<not> term_model_holds T (term_model_eval Var A)"
    using not_A by (simp add: term_model_holds_Var_iff)
  show ?thesis
    using that henkin neg_holds not_holds by blast
qed

theorem C_term_model_countermodel_for_unprovable:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>C A"
  obtains T where "C_Henkin_theory \<Gamma> T"
    and "term_model_holds T (term_model_eval Var (Neg A))"
    and "\<not> term_model_holds T (term_model_eval Var A)"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_unprovable_staged)
  have not_A: "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  have neg_holds: "term_model_holds T (term_model_eval Var (Neg A))"
    using neg_in by (simp add: term_model_holds_Var_iff)
  have not_holds: "\<not> term_model_holds T (term_model_eval Var A)"
    using not_A by (simp add: term_model_holds_Var_iff)
  show ?thesis
    using that henkin neg_holds not_holds by blast
qed

theorem H_term_model_countermodel_for_underivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  obtains T where "H_Henkin_theory \<Gamma> T"
    and "\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)"
    and "term_model_holds T (term_model_eval Var (Neg A))"
    and "\<not> term_model_holds T (term_model_eval Var A)"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_underivable_list_staged)
  have assumptions_hold: "\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)"
    using assms_sub by (auto simp: term_model_holds_Var_iff)
  have not_A: "A \<notin> T"
    using H_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  have neg_holds: "term_model_holds T (term_model_eval Var (Neg A))"
    using neg_in by (simp add: term_model_holds_Var_iff)
  have not_holds: "\<not> term_model_holds T (term_model_eval Var A)"
    using not_A by (simp add: term_model_holds_Var_iff)
  show ?thesis
    using that henkin assumptions_hold neg_holds not_holds by blast
qed

theorem C_term_model_countermodel_for_underivable:
  assumes typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  obtains T where "C_Henkin_theory \<Gamma> T"
    and "\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)"
    and "term_model_holds T (term_model_eval Var (Neg A))"
    and "\<not> term_model_holds T (term_model_eval Var A)"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_underivable_list_staged)
  have assumptions_hold: "\<forall>B \<in> set \<Delta>. term_model_holds T (term_model_eval Var B)"
    using assms_sub by (auto simp: term_model_holds_Var_iff)
  have not_A: "A \<notin> T"
    using C_Henkin_neg_mem_iff[OF henkin A_type] neg_in by blast
  have neg_holds: "term_model_holds T (term_model_eval Var (Neg A))"
    using neg_in by (simp add: term_model_holds_Var_iff)
  have not_holds: "\<not> term_model_holds T (term_model_eval Var A)"
    using not_A by (simp add: term_model_holds_Var_iff)
  show ?thesis
    using that henkin assumptions_hold neg_holds not_holds by blast
qed

section \<open>Truth-lemma bridge to countermodels\<close>

context applicative_structure
begin

definition H_truth_lemma_at :: "ctx \<Rightarrow> oterm set \<Rightarrow> 'v env \<Rightarrow> bool" where
  "H_truth_lemma_at \<Gamma> T \<rho> \<longleftrightarrow>
    H_Henkin_theory \<Gamma> T \<and> env_typed \<Gamma> \<rho> \<and>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> (holds (eval \<rho> A) \<longleftrightarrow> A \<in> T))"

definition C_truth_lemma_at :: "ctx \<Rightarrow> oterm set \<Rightarrow> 'v env \<Rightarrow> bool" where
  "C_truth_lemma_at \<Gamma> T \<rho> \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> env_typed \<Gamma> \<rho> \<and>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> (holds (eval \<rho> A) \<longleftrightarrow> A \<in> T))"

definition H_truth_lemma_model_existence :: bool where
  "H_truth_lemma_model_existence \<longleftrightarrow>
    (\<forall>\<Gamma> T. H_Henkin_theory \<Gamma> T \<longrightarrow> (\<exists>\<rho>. H_truth_lemma_at \<Gamma> T \<rho>))"

definition C_truth_lemma_model_existence :: bool where
  "C_truth_lemma_model_existence \<longleftrightarrow>
    (\<forall>\<Gamma> T. C_Henkin_theory \<Gamma> T \<longrightarrow> (\<exists>\<rho>. C_truth_lemma_at \<Gamma> T \<rho>))"

definition H_subst_truth_realized_at :: "ctx \<Rightarrow> oterm set \<Rightarrow> 'v env \<Rightarrow> bool" where
  "H_subst_truth_realized_at \<Gamma> T \<rho> \<longleftrightarrow>
    H_Henkin_theory \<Gamma> T \<and> env_typed \<Gamma> \<rho> \<and>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      (holds (eval \<rho> A) \<longleftrightarrow> H_subst_truth \<Gamma> \<Gamma> T Var A))"

definition C_subst_truth_realized_at :: "ctx \<Rightarrow> oterm set \<Rightarrow> 'v env \<Rightarrow> bool" where
  "C_subst_truth_realized_at \<Gamma> T \<rho> \<longleftrightarrow>
    C_Henkin_theory \<Gamma> T \<and> env_typed \<Gamma> \<rho> \<and>
    (\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      (holds (eval \<rho> A) \<longleftrightarrow> C_subst_truth \<Gamma> \<Gamma> T Var A))"

definition H_subst_truth_realization_existence :: bool where
  "H_subst_truth_realization_existence \<longleftrightarrow>
    (\<forall>\<Gamma> T. H_Henkin_theory \<Gamma> T \<longrightarrow>
      (\<exists>\<rho>. H_subst_truth_realized_at \<Gamma> T \<rho>))"

definition C_subst_truth_realization_existence :: bool where
  "C_subst_truth_realization_existence \<longleftrightarrow>
    (\<forall>\<Gamma> T. C_Henkin_theory \<Gamma> T \<longrightarrow>
      (\<exists>\<rho>. C_subst_truth_realized_at \<Gamma> T \<rho>))"

lemma H_truth_lemma_at_from_subst_truth_realized:
  assumes realized: "H_subst_truth_realized_at \<Gamma> T \<rho>"
  shows "H_truth_lemma_at \<Gamma> T \<rho>"
proof -
  have henkin: "H_Henkin_theory \<Gamma> T"
    using realized unfolding H_subst_truth_realized_at_def by blast
  have env: "env_typed \<Gamma> \<rho>"
    using realized unfolding H_subst_truth_realized_at_def by blast
  have truth: "\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> (holds (eval \<rho> A) \<longleftrightarrow> A \<in> T)"
  proof (intro allI impI)
    fix A
    assume A_type: "\<Gamma> \<turnstile> A : Prop"
    have holds_subst: "holds (eval \<rho> A) \<longleftrightarrow>
        H_subst_truth \<Gamma> \<Gamma> T Var A"
      using realized A_type unfolding H_subst_truth_realized_at_def by blast
    have subst_mem: "H_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow> A \<in> T"
      using henkin A_type by (rule H_subst_truth_identity_mem_iff)
    show "holds (eval \<rho> A) \<longleftrightarrow> A \<in> T"
      using holds_subst subst_mem by blast
  qed
  show ?thesis
    using henkin env truth unfolding H_truth_lemma_at_def by blast
qed

lemma C_truth_lemma_at_from_subst_truth_realized:
  assumes realized: "C_subst_truth_realized_at \<Gamma> T \<rho>"
  shows "C_truth_lemma_at \<Gamma> T \<rho>"
proof -
  have henkin: "C_Henkin_theory \<Gamma> T"
    using realized unfolding C_subst_truth_realized_at_def by blast
  have env: "env_typed \<Gamma> \<rho>"
    using realized unfolding C_subst_truth_realized_at_def by blast
  have truth: "\<forall>A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> (holds (eval \<rho> A) \<longleftrightarrow> A \<in> T)"
  proof (intro allI impI)
    fix A
    assume A_type: "\<Gamma> \<turnstile> A : Prop"
    have holds_subst: "holds (eval \<rho> A) \<longleftrightarrow>
        C_subst_truth \<Gamma> \<Gamma> T Var A"
      using realized A_type unfolding C_subst_truth_realized_at_def by blast
    have subst_mem: "C_subst_truth \<Gamma> \<Gamma> T Var A \<longleftrightarrow> A \<in> T"
      using henkin A_type by (rule C_subst_truth_identity_mem_iff)
    show "holds (eval \<rho> A) \<longleftrightarrow> A \<in> T"
      using holds_subst subst_mem by blast
  qed
  show ?thesis
    using henkin env truth unfolding C_truth_lemma_at_def by blast
qed

theorem H_truth_lemma_model_existence_from_subst_truth_realization:
  assumes "H_subst_truth_realization_existence"
  shows "H_truth_lemma_model_existence"
proof (unfold H_truth_lemma_model_existence_def, intro allI impI)
  fix \<Gamma> T
  assume henkin: "H_Henkin_theory \<Gamma> T"
  obtain \<rho> where "H_subst_truth_realized_at \<Gamma> T \<rho>"
    using assms henkin
    unfolding H_subst_truth_realization_existence_def by blast
  then have "H_truth_lemma_at \<Gamma> T \<rho>"
    by (rule H_truth_lemma_at_from_subst_truth_realized)
  then show "\<exists>\<rho>. H_truth_lemma_at \<Gamma> T \<rho>"
    by blast
qed

theorem C_truth_lemma_model_existence_from_subst_truth_realization:
  assumes "C_subst_truth_realization_existence"
  shows "C_truth_lemma_model_existence"
proof (unfold C_truth_lemma_model_existence_def, intro allI impI)
  fix \<Gamma> T
  assume henkin: "C_Henkin_theory \<Gamma> T"
  obtain \<rho> where "C_subst_truth_realized_at \<Gamma> T \<rho>"
    using assms henkin
    unfolding C_subst_truth_realization_existence_def by blast
  then have "C_truth_lemma_at \<Gamma> T \<rho>"
    by (rule C_truth_lemma_at_from_subst_truth_realized)
  then show "\<exists>\<rho>. C_truth_lemma_at \<Gamma> T \<rho>"
    by blast
qed

lemma H_truth_lemma_henkin:
  assumes "H_truth_lemma_at \<Gamma> T \<rho>"
  shows "H_Henkin_theory \<Gamma> T"
  using assms unfolding H_truth_lemma_at_def by blast

lemma H_truth_lemma_env_typed:
  assumes "H_truth_lemma_at \<Gamma> T \<rho>"
  shows "env_typed \<Gamma> \<rho>"
  using assms unfolding H_truth_lemma_at_def by blast

lemma H_truth_lemma_holds_iff:
  assumes "H_truth_lemma_at \<Gamma> T \<rho>"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "holds (eval \<rho> A) \<longleftrightarrow> A \<in> T"
  using assms unfolding H_truth_lemma_at_def by blast

lemma H_truth_lemma_not_holds_of_neg:
  assumes truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "\<not> holds (eval \<rho> A)"
proof
  assume "holds (eval \<rho> A)"
  then have "A \<in> T"
    using truth A_type by (simp add: H_truth_lemma_holds_iff)
  moreover have "A \<notin> T"
    using H_truth_lemma_henkin[OF truth] A_type neg_in
      H_Henkin_neg_mem_iff by blast
  ultimately show False
    by blast
qed

lemma H_countermodel_from_truth_lemma:
  assumes truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "countermodel_in_context \<Gamma> A \<rho>"
  using A_type H_truth_lemma_env_typed[OF truth]
    H_truth_lemma_not_holds_of_neg[OF truth A_type neg_in]
  unfolding countermodel_in_context_def by blast

lemma H_has_countermodel_from_truth_lemma:
  assumes "H_truth_lemma_at \<Gamma> T \<rho>"
    and "\<Gamma> \<turnstile> A : Prop"
    and "Neg A \<in> T"
  shows "has_countermodel \<Gamma> A"
  using H_countermodel_from_truth_lemma[OF assms]
  unfolding has_countermodel_def by blast

lemma H_satisfies_assumptions_from_truth_lemma:
  assumes truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and assms_sub: "set \<Delta> \<subseteq> T"
  shows "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
proof -
  have "\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop \<and> holds (eval \<rho> B)"
  proof
    fix B
    assume B_in: "B \<in> set \<Delta>"
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using typed_assms B_in by blast
    have "B \<in> T"
      using assms_sub B_in by blast
    then have "holds (eval \<rho> B)"
      using truth B_type by (simp add: H_truth_lemma_holds_iff)
    then show "\<Gamma> \<turnstile> B : Prop \<and> holds (eval \<rho> B)"
      using B_type by blast
  qed
  then show ?thesis
    using H_truth_lemma_env_typed[OF truth]
    unfolding satisfies_assumptions_def by blast
qed

lemma H_entailment_countermodel_from_truth_lemma:
  assumes truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "countermodel_for_entailment \<Gamma> \<Delta> A \<rho>"
  using A_type
    H_satisfies_assumptions_from_truth_lemma[OF truth typed_assms assms_sub]
    H_truth_lemma_not_holds_of_neg[OF truth A_type neg_in]
  unfolding countermodel_for_entailment_def by blast

lemma H_has_entailment_countermodel_from_truth_lemma:
  assumes "H_truth_lemma_at \<Gamma> T \<rho>"
    and "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and "set \<Delta> \<subseteq> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "Neg A \<in> T"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using H_entailment_countermodel_from_truth_lemma[OF assms]
  unfolding has_entailment_countermodel_def by blast

lemma C_truth_lemma_henkin:
  assumes "C_truth_lemma_at \<Gamma> T \<rho>"
  shows "C_Henkin_theory \<Gamma> T"
  using assms unfolding C_truth_lemma_at_def by blast

lemma C_truth_lemma_env_typed:
  assumes "C_truth_lemma_at \<Gamma> T \<rho>"
  shows "env_typed \<Gamma> \<rho>"
  using assms unfolding C_truth_lemma_at_def by blast

lemma C_truth_lemma_holds_iff:
  assumes "C_truth_lemma_at \<Gamma> T \<rho>"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "holds (eval \<rho> A) \<longleftrightarrow> A \<in> T"
  using assms unfolding C_truth_lemma_at_def by blast

lemma C_truth_lemma_not_holds_of_neg:
  assumes truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "\<not> holds (eval \<rho> A)"
proof
  assume "holds (eval \<rho> A)"
  then have "A \<in> T"
    using truth A_type by (simp add: C_truth_lemma_holds_iff)
  moreover have "A \<notin> T"
    using C_truth_lemma_henkin[OF truth] A_type neg_in
      C_Henkin_neg_mem_iff by blast
  ultimately show False
    by blast
qed

lemma C_countermodel_from_truth_lemma:
  assumes truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "countermodel_in_context \<Gamma> A \<rho>"
  using A_type C_truth_lemma_env_typed[OF truth]
    C_truth_lemma_not_holds_of_neg[OF truth A_type neg_in]
  unfolding countermodel_in_context_def by blast

lemma C_has_countermodel_from_truth_lemma:
  assumes "C_truth_lemma_at \<Gamma> T \<rho>"
    and "\<Gamma> \<turnstile> A : Prop"
    and "Neg A \<in> T"
  shows "has_countermodel \<Gamma> A"
  using C_countermodel_from_truth_lemma[OF assms]
  unfolding has_countermodel_def by blast

lemma C_satisfies_assumptions_from_truth_lemma:
  assumes truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and assms_sub: "set \<Delta> \<subseteq> T"
  shows "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
proof -
  have "\<forall>B \<in> set \<Delta>. \<Gamma> \<turnstile> B : Prop \<and> holds (eval \<rho> B)"
  proof
    fix B
    assume B_in: "B \<in> set \<Delta>"
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using typed_assms B_in by blast
    have "B \<in> T"
      using assms_sub B_in by blast
    then have "holds (eval \<rho> B)"
      using truth B_type by (simp add: C_truth_lemma_holds_iff)
    then show "\<Gamma> \<turnstile> B : Prop \<and> holds (eval \<rho> B)"
      using B_type by blast
  qed
  then show ?thesis
    using C_truth_lemma_env_typed[OF truth]
    unfolding satisfies_assumptions_def by blast
qed

lemma C_entailment_countermodel_from_truth_lemma:
  assumes truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "countermodel_for_entailment \<Gamma> \<Delta> A \<rho>"
  using A_type
    C_satisfies_assumptions_from_truth_lemma[OF truth typed_assms assms_sub]
    C_truth_lemma_not_holds_of_neg[OF truth A_type neg_in]
  unfolding countermodel_for_entailment_def by blast

lemma C_has_entailment_countermodel_from_truth_lemma:
  assumes "C_truth_lemma_at \<Gamma> T \<rho>"
    and "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and "set \<Delta> \<subseteq> T"
    and "\<Gamma> \<turnstile> A : Prop"
    and "Neg A \<in> T"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using C_entailment_countermodel_from_truth_lemma[OF assms]
  unfolding has_entailment_countermodel_def by blast

theorem H_countermodel_property_from_staged_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
  shows "H_countermodel_property"
proof (unfold H_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>H A"
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using body_enums by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using formula_enums by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_unprovable_staged)
  obtain \<rho> where truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    using truth_models henkin
    unfolding H_truth_lemma_model_existence_def by blast
  show "has_countermodel \<Gamma> A"
    using truth A_type neg_in by (rule H_has_countermodel_from_truth_lemma)
qed

theorem H_completeness_from_staged_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof -
  have countermodels: "H_countermodel_property"
    using truth_models body_enums formula_enums
    by (rule H_countermodel_property_from_staged_truth_lemma)
  show ?thesis
    using countermodels valid by (rule H_completeness_from_countermodels)
qed

theorem H_countermodel_property_from_truth_lemma:
  assumes "H_truth_lemma_model_existence"
  shows "H_countermodel_property"
  using assms enumerates_witness_bodies_exists enumerates_formulas_exists
  by (rule H_countermodel_property_from_staged_truth_lemma)

theorem H_completeness_from_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof -
  have countermodels: "H_countermodel_property"
    using truth_models by (rule H_countermodel_property_from_truth_lemma)
  show ?thesis
    using countermodels valid by (rule H_completeness_from_countermodels)
qed

theorem H_entailment_countermodel_from_staged_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using body_enums by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using formula_enums by blast
  obtain T where henkin: "H_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule H_canonical_Henkin_theory_for_underivable_list_staged)
  obtain \<rho> where truth: "H_truth_lemma_at \<Gamma> T \<rho>"
    using truth_models henkin
    unfolding H_truth_lemma_model_existence_def by blast
  show ?thesis
    using truth typed_assms assms_sub A_type neg_in
    by (rule H_has_entailment_countermodel_from_truth_lemma)
qed

theorem H_strong_completeness_from_staged_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using truth_models body_enums formula_enums typed_assms A_type not_derivable
    by (rule H_entailment_countermodel_from_staged_truth_lemma)
  then show False
    using semantically_entails_no_countermodel[OF entails] by blast
qed

theorem H_entailment_countermodel_from_truth_lemma_existence:
  assumes truth_models: "H_truth_lemma_model_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using truth_models enumerates_witness_bodies_exists enumerates_formulas_exists
    typed_assms A_type not_derivable
  by (rule H_entailment_countermodel_from_staged_truth_lemma)

theorem H_strong_completeness_from_truth_lemma:
  assumes truth_models: "H_truth_lemma_model_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using truth_models typed_assms A_type not_derivable
    by (rule H_entailment_countermodel_from_truth_lemma_existence)
  then show False
    using semantically_entails_no_countermodel[OF entails] by blast
qed

end

context classicist_structure
begin

theorem C_countermodel_property_from_staged_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
  shows "C_countermodel_property"
proof (unfold C_countermodel_property_def, intro allI impI)
  fix \<Gamma> A
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>C A"
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using body_enums by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using formula_enums by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and neg_in: "Neg A \<in> T"
    using A_type not_provable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_unprovable_staged)
  obtain \<rho> where truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    using truth_models henkin
    unfolding C_truth_lemma_model_existence_def by blast
  show "has_countermodel \<Gamma> A"
    using truth A_type neg_in by (rule C_has_countermodel_from_truth_lemma)
qed

theorem C_completeness_from_staged_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
proof -
  have countermodels: "C_countermodel_property"
    using truth_models body_enums formula_enums
    by (rule C_countermodel_property_from_staged_truth_lemma)
  show ?thesis
    using countermodels valid by (rule C_completeness_from_countermodels)
qed

theorem C_countermodel_property_from_truth_lemma:
  assumes "C_truth_lemma_model_existence"
  shows "C_countermodel_property"
  using assms enumerates_witness_bodies_exists enumerates_formulas_exists
  by (rule C_countermodel_property_from_staged_truth_lemma)

theorem C_completeness_from_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
proof -
  have countermodels: "C_countermodel_property"
    using truth_models by (rule C_countermodel_property_from_truth_lemma)
  show ?thesis
    using countermodels valid by (rule C_completeness_from_countermodels)
qed

theorem C_entailment_countermodel_from_staged_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
proof -
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using body_enums by blast
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using formula_enums by blast
  obtain T where henkin: "C_Henkin_theory \<Gamma> T"
    and assms_sub: "set \<Delta> \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using typed_assms A_type not_derivable body_enum formula_enum
    by (rule C_canonical_Henkin_theory_for_underivable_list_staged)
  obtain \<rho> where truth: "C_truth_lemma_at \<Gamma> T \<rho>"
    using truth_models henkin
    unfolding C_truth_lemma_model_existence_def by blast
  show ?thesis
    using truth typed_assms assms_sub A_type neg_in
    by (rule C_has_entailment_countermodel_from_truth_lemma)
qed

theorem C_strong_completeness_from_staged_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and body_enums: "\<And>\<Gamma>. \<exists>body_enum. enumerates_witness_bodies \<Gamma> body_enum"
    and formula_enums: "\<And>\<Gamma>. \<exists>formula_enum. enumerates_formulas \<Gamma> formula_enum"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using truth_models body_enums formula_enums typed_assms A_type not_derivable
    by (rule C_entailment_countermodel_from_staged_truth_lemma)
  then show False
    using semantically_entails_no_countermodel[OF entails] by blast
qed

theorem C_entailment_countermodel_from_truth_lemma_existence:
  assumes truth_models: "C_truth_lemma_model_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using truth_models enumerates_witness_bodies_exists enumerates_formulas_exists
    typed_assms A_type not_derivable
  by (rule C_entailment_countermodel_from_staged_truth_lemma)

theorem C_strong_completeness_from_truth_lemma:
  assumes truth_models: "C_truth_lemma_model_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using entails by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using truth_models typed_assms A_type not_derivable
    by (rule C_entailment_countermodel_from_truth_lemma_existence)
  then show False
    using semantically_entails_no_countermodel[OF entails] by blast
qed

theorem H_countermodel_property_from_subst_truth_realization:
  assumes "H_subst_truth_realization_existence"
  shows "H_countermodel_property"
  using H_truth_lemma_model_existence_from_subst_truth_realization[OF assms]
  by (rule H_countermodel_property_from_truth_lemma)

theorem H_completeness_from_subst_truth_realization:
  assumes realization: "H_subst_truth_realization_existence"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
  using H_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    valid
  by (rule H_completeness_from_truth_lemma)

theorem H_entailment_countermodel_from_subst_truth_realization:
  assumes realization: "H_subst_truth_realization_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using H_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    typed_assms A_type not_derivable
  by (rule H_entailment_countermodel_from_truth_lemma_existence)

theorem H_strong_completeness_from_subst_truth_realization:
  assumes realization: "H_subst_truth_realization_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  using H_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    typed_assms entails
  by (rule H_strong_completeness_from_truth_lemma)

theorem C_countermodel_property_from_subst_truth_realization:
  assumes "C_subst_truth_realization_existence"
  shows "C_countermodel_property"
  using C_truth_lemma_model_existence_from_subst_truth_realization[OF assms]
  by (rule C_countermodel_property_from_truth_lemma)

theorem C_completeness_from_subst_truth_realization:
  assumes realization: "C_subst_truth_realization_existence"
    and valid: "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using C_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    valid
  by (rule C_completeness_from_truth_lemma)

theorem C_entailment_countermodel_from_subst_truth_realization:
  assumes realization: "C_subst_truth_realization_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_derivable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "has_entailment_countermodel \<Gamma> \<Delta> A"
  using C_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    typed_assms A_type not_derivable
  by (rule C_entailment_countermodel_from_truth_lemma_existence)

theorem C_strong_completeness_from_subst_truth_realization:
  assumes realization: "C_subst_truth_realization_existence"
    and typed_assms: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and entails: "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  using C_truth_lemma_model_existence_from_subst_truth_realization[OF realization]
    typed_assms entails
  by (rule C_strong_completeness_from_truth_lemma)

end

end
