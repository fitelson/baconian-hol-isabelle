theory Bacon_PP_ZF_Hyper_Frame
  imports Bacon_PP_ZF_Full_Frame "HOL-Library.Sublist"
begin

section \<open>A preconstructed hyperintensional HOL-ZF frame\<close>

text \<open>
  The full-frame negative control shows that metalanguage equality is too
  strong an interpretation of object identity: it makes both identity and
  distinctness rigid.  We retain preconstructed set-theoretic domains and
  terminating structural denotation, but replace equality by a world-indexed
  equivalence relation.

  Worlds are natural numbers ordered by extension.  Two propositions are
  equivalent at world \<open>w\<close> when they agree at every world \<open>v \<ge> w\<close>.
  At arrow types, equivalence is the corresponding logical relation.  The
  arrow domain contains exactly the set-theoretic functions that respect this
  relation at every world.  Both the domain and equivalence clauses recurse
  only on proper subtypes.
\<close>

fun pp_h_domain :: "otype \<Rightarrow> ZF"
and pp_h_eqv :: "otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_h_domain Ind = Nat"
| "pp_h_domain Prop = Power Nat"
| "pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Sep (Fun (pp_h_domain \<sigma>) (pp_h_domain \<tau>))
      (\<lambda>f. \<forall>w x y.
        Elem x (pp_h_domain \<sigma>) \<longrightarrow>
        Elem y (pp_h_domain \<sigma>) \<longrightarrow>
        pp_h_eqv \<sigma> w x y \<longrightarrow>
        pp_h_eqv \<tau> w (f \<acute> x) (f \<acute> y))"
| "pp_h_eqv Ind w x y = (x = y)"
| "pp_h_eqv Prop w P Q =
    (\<forall>v \<ge> w. Elem (nat2Nat v) P \<longleftrightarrow> Elem (nat2Nat v) Q)"
| "pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g =
    (\<forall>v \<ge> w. \<forall>x y.
      Elem x (pp_h_domain \<sigma>) \<longrightarrow>
      Elem y (pp_h_domain \<sigma>) \<longrightarrow>
      pp_h_eqv \<sigma> v x y \<longrightarrow>
      pp_h_eqv \<tau> v (f \<acute> x) (g \<acute> y))"

lemma pp_h_prop_eqv_refl:
  "pp_h_eqv Prop w P P"
  by simp

lemma pp_h_prop_eqv_symmetric:
  "pp_h_eqv Prop w P Q \<Longrightarrow> pp_h_eqv Prop w Q P"
  by auto

lemma pp_h_prop_eqv_transitive:
  "pp_h_eqv Prop w P Q \<Longrightarrow>
    pp_h_eqv Prop w Q R \<Longrightarrow>
    pp_h_eqv Prop w P R"
  by auto

lemma pp_h_prop_eqv_persistent:
  assumes "pp_h_eqv Prop w P Q" and "w \<le> v"
  shows "pp_h_eqv Prop v P Q"
  using assms by auto

lemma pp_h_prop_eqv_truth_iff:
  "pp_h_eqv Prop w P (pp_zf_truth True) \<longleftrightarrow>
    (\<forall>v \<ge> w. pp_zf_holds P v)"
  by (simp add: pp_zf_holds_def pp_zf_truth_def Elem_nat2Nat_Nat)

text \<open>
  The last biconditional is the intended S4 necessity clause: identity with
  truth at \<open>w\<close> means truth throughout the tail above \<open>w\<close>.  Unlike
  metalanguage equality, failure of equivalence at \<open>w\<close> need not persist:
  two propositions may disagree now and agree on a later tail.
\<close>

lemma pp_h_arrow_member_function:
  assumes "Elem f (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Elem f (Fun (pp_h_domain \<sigma>) (pp_h_domain \<tau>))"
  using assms by (simp add: Sep)

lemma pp_h_arrow_member_respects:
  assumes f: "Elem f (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
  shows "pp_h_eqv \<tau> w (f \<acute> x) (f \<acute> y)"
  using f x y xy by (auto simp: Sep)

lemma pp_h_app_closed:
  assumes f: "Elem f (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_h_domain \<sigma>)"
  shows "Elem (f \<acute> x) (pp_h_domain \<tau>)"
proof -
  have f_fun: "Elem f (Fun (pp_h_domain \<sigma>) (pp_h_domain \<tau>))"
    using pp_h_arrow_member_function[OF f] .
  have is_fun: "isFun f"
    using pp_zf_function_isFun[OF f_fun] .
  have domain: "Domain f = pp_h_domain \<sigma>"
    using pp_zf_function_domain[OF f_fun] .
  have in_range: "Elem (f \<acute> x) (Range f)"
    using fun_value_in_range[OF is_fun] x domain by simp
  have range_subset: "subset (Range f) (pp_h_domain \<tau>)"
    using Fun_Range[OF f_fun] .
  show ?thesis
    using in_range range_subset by (auto simp: subset_def)
qed

lemma pp_h_eqv_persistent:
  assumes eqv: "pp_h_eqv \<sigma> w x y" and future: "w \<le> v"
  shows "pp_h_eqv \<sigma> v x y"
  using eqv future
proof (induction \<sigma> arbitrary: w v x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by auto
next
  case (Arr \<sigma> \<tau>)
  then show ?case by auto
qed

subsection \<open>Nonempty domains\<close>

fun pp_h_default :: "otype \<Rightarrow> ZF" where
  "pp_h_default Ind = Empty"
| "pp_h_default Prop = Empty"
| "pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Lambda (pp_h_domain \<sigma>) (\<lambda>_. pp_h_default \<tau>)"

lemma pp_h_default_in_domain_and_reflexive:
  "Elem (pp_h_default \<sigma>) (pp_h_domain \<sigma>) \<and>
    (\<forall>w. pp_h_eqv \<sigma> w (pp_h_default \<sigma>) (pp_h_default \<sigma>))"
proof (induction \<sigma>)
  case Ind
  then show ?case
    by (simp add: Elem_Empty_Nat)
next
  case Prop
  then show ?case
    by (simp add: Power subset_empty)
next
  case (Arr \<sigma> \<tau>)
  have source:
      "Elem (pp_h_default \<sigma>) (pp_h_domain \<sigma>)"
    using Arr.IH(1) by blast
  have target:
      "Elem (pp_h_default \<tau>) (pp_h_domain \<tau>)"
    using Arr.IH(2) by blast
  have target_refl:
      "\<And>w. pp_h_eqv \<tau> w (pp_h_default \<tau>) (pp_h_default \<tau>)"
    using Arr.IH(2) by blast
  have function_member:
      "Elem
        (Lambda (pp_h_domain \<sigma>) (\<lambda>_. pp_h_default \<tau>))
        (Fun (pp_h_domain \<sigma>) (pp_h_domain \<tau>))"
    by (simp add: Elem_Lambda_Fun target)
  have respects:
      "\<forall>w x y.
        Elem x (pp_h_domain \<sigma>) \<longrightarrow>
        Elem y (pp_h_domain \<sigma>) \<longrightarrow>
        pp_h_eqv \<sigma> w x y \<longrightarrow>
        pp_h_eqv \<tau> w
          ((Lambda (pp_h_domain \<sigma>) (\<lambda>_. pp_h_default \<tau>)) \<acute> x)
          ((Lambda (pp_h_domain \<sigma>) (\<lambda>_. pp_h_default \<tau>)) \<acute> y)"
    using target_refl
    by (auto simp: Lambda_app)
  have member:
      "Elem (pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using function_member respects by (simp add: Sep)
  have reflexive:
      "\<And>w. pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
        (pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using target_refl
    by (auto simp: Lambda_app)
  show ?case
    using member reflexive by blast
qed

lemma pp_h_default_in_domain:
  "Elem (pp_h_default \<sigma>) (pp_h_domain \<sigma>)"
  using pp_h_default_in_domain_and_reflexive by blast

theorem pp_h_domain_nonempty:
  "\<exists>x. Elem x (pp_h_domain \<sigma>)"
  using pp_h_default_in_domain by blast

subsection \<open>Equivalence laws\<close>

lemma pp_h_eqv_reflexive:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
  shows "pp_h_eqv \<sigma> w x x"
  using x
proof (induction \<sigma> arbitrary: w x)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by simp
next
  case (Arr \<sigma> \<tau>)
  then show ?case
    by (auto simp: Sep)
qed

lemma pp_h_eqv_symmetric:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
  shows "pp_h_eqv \<sigma> w y x"
  using x y xy
proof (induction \<sigma> arbitrary: w x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by auto
next
  case (Arr \<sigma> \<tau>)
  have x_fun: "Elem x (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have y_fun: "Elem y (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  show ?case
    unfolding pp_h_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "w \<le> v"
      and a: "Elem a (pp_h_domain \<sigma>)"
      and b: "Elem b (pp_h_domain \<sigma>)"
      and ab: "pp_h_eqv \<sigma> v a b"
    have ba: "pp_h_eqv \<sigma> v b a"
      using Arr.IH(1)[OF a b ab] .
    have old:
        "pp_h_eqv \<tau> v (x \<acute> b) (y \<acute> a)"
      using Arr.prems(3) future b a ba by auto
    have xb: "Elem (x \<acute> b) (pp_h_domain \<tau>)"
      using pp_h_app_closed[OF x_fun b] .
    have ya: "Elem (y \<acute> a) (pp_h_domain \<tau>)"
      using pp_h_app_closed[OF y_fun a] .
    show "pp_h_eqv \<tau> v (y \<acute> a) (x \<acute> b)"
      using Arr.IH(2)[OF xb ya old] .
  qed
qed

lemma pp_h_eqv_transitive:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and z: "Elem z (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
    and yz: "pp_h_eqv \<sigma> w y z"
  shows "pp_h_eqv \<sigma> w x z"
  using x y z xy yz
proof (induction \<sigma> arbitrary: w x y z)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by auto
next
  case (Arr \<sigma> \<tau>)
  have x_fun: "Elem x (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have y_fun: "Elem y (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  have z_fun: "Elem z (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(3) .
  show ?case
    unfolding pp_h_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "w \<le> v"
      and a: "Elem a (pp_h_domain \<sigma>)"
      and b: "Elem b (pp_h_domain \<sigma>)"
      and ab: "pp_h_eqv \<sigma> v a b"
    have yy: "pp_h_eqv \<sigma> v b b"
      using pp_h_eqv_reflexive[OF b] .
    have first: "pp_h_eqv \<tau> v (x \<acute> a) (y \<acute> b)"
      using Arr.prems(4) future a b ab by auto
    have second: "pp_h_eqv \<tau> v (y \<acute> b) (z \<acute> b)"
      using Arr.prems(5) future b b yy by auto
    have xa: "Elem (x \<acute> a) (pp_h_domain \<tau>)"
      using pp_h_app_closed[OF x_fun a] .
    have yb: "Elem (y \<acute> b) (pp_h_domain \<tau>)"
      using pp_h_app_closed[OF y_fun b] .
    have zb: "Elem (z \<acute> b) (pp_h_domain \<tau>)"
      using pp_h_app_closed[OF z_fun b] .
    show "pp_h_eqv \<tau> v (x \<acute> a) (z \<acute> b)"
      using Arr.IH(2)[OF xa yb zb first second] .
  qed
qed

section \<open>Structural hyperintensional denotation\<close>

fun pp_h_eval ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> oterm \<Rightarrow> ZF" where
  "pp_h_eval C \<rho> (Var n) = \<rho> n"
| "pp_h_eval C \<rho> (Const c \<sigma>) = C c \<sigma>"
| "pp_h_eval C \<rho> (App M N) =
    (pp_h_eval C \<rho> M) \<acute> (pp_h_eval C \<rho> N)"
| "pp_h_eval C \<rho> (Lam \<sigma> M) =
    Lambda (pp_h_domain \<sigma>)
      (\<lambda>x. pp_h_eval C (extend_env x \<rho>) M)"
| "pp_h_eval C \<rho> (Eq \<sigma> M N) =
    pp_zf_prop (\<lambda>z.
      pp_h_eqv \<sigma> (Nat2nat z) (pp_h_eval C \<rho> M) (pp_h_eval C \<rho> N))"
| "pp_h_eval C \<rho> (Neg A) =
    pp_zf_prop (\<lambda>z. \<not> Elem z (pp_h_eval C \<rho> A))"
| "pp_h_eval C \<rho> (Conj A B) =
    pp_zf_prop (\<lambda>z.
      Elem z (pp_h_eval C \<rho> A) \<and> Elem z (pp_h_eval C \<rho> B))"
| "pp_h_eval C \<rho> (Disj A B) =
    pp_zf_prop (\<lambda>z.
      Elem z (pp_h_eval C \<rho> A) \<or> Elem z (pp_h_eval C \<rho> B))"
| "pp_h_eval C \<rho> (Imp A B) =
    pp_zf_prop (\<lambda>z.
      Elem z (pp_h_eval C \<rho> A) \<longrightarrow> Elem z (pp_h_eval C \<rho> B))"
| "pp_h_eval C \<rho> (Forall \<sigma> A) =
    pp_zf_prop (\<lambda>z.
      \<forall>x. Elem x (pp_h_domain \<sigma>) \<longrightarrow>
        Elem z (pp_h_eval C (extend_env x \<rho>) A))"
| "pp_h_eval C \<rho> (Exists \<sigma> A) =
    pp_zf_prop (\<lambda>z.
      \<exists>x. Elem x (pp_h_domain \<sigma>) \<and>
        Elem z (pp_h_eval C (extend_env x \<rho>) A))"

lemma pp_h_eval_Eq_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Eq \<sigma> M N)) w \<longleftrightarrow>
    pp_h_eqv \<sigma> w (pp_h_eval C \<rho> M) (pp_h_eval C \<rho> N)"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Neg_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Neg A)) w \<longleftrightarrow>
    \<not> pp_zf_holds (pp_h_eval C \<rho> A) w"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Conj_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Conj A B)) w \<longleftrightarrow>
    pp_zf_holds (pp_h_eval C \<rho> A) w \<and>
    pp_zf_holds (pp_h_eval C \<rho> B) w"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Disj_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Disj A B)) w \<longleftrightarrow>
    pp_zf_holds (pp_h_eval C \<rho> A) w \<or>
    pp_zf_holds (pp_h_eval C \<rho> B) w"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Imp_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Imp A B)) w \<longleftrightarrow>
    (pp_zf_holds (pp_h_eval C \<rho> A) w \<longrightarrow>
      pp_zf_holds (pp_h_eval C \<rho> B) w)"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Forall_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Forall \<sigma> A)) w \<longleftrightarrow>
    (\<forall>x. Elem x (pp_h_domain \<sigma>) \<longrightarrow>
      pp_zf_holds (pp_h_eval C (extend_env x \<rho>) A) w)"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_eval_Exists_holds[simp]:
  "pp_zf_holds (pp_h_eval C \<rho> (Exists \<sigma> A)) w \<longleftrightarrow>
    (\<exists>x. Elem x (pp_h_domain \<sigma>) \<and>
      pp_zf_holds (pp_h_eval C (extend_env x \<rho>) A) w)"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

definition pp_h_env_typed ::
    "ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_h_env_typed \<Gamma> \<rho> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      Elem (\<rho> n) (pp_h_domain \<sigma>))"

definition pp_h_env_eqv ::
    "nat \<Rightarrow> ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longleftrightarrow>
    pp_h_env_typed \<Gamma> \<rho> \<and>
    pp_h_env_typed \<Gamma> \<eta> \<and>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      pp_h_eqv \<sigma> w (\<rho> n) (\<eta> n))"

lemma pp_h_env_typed_lookup:
  assumes env: "pp_h_env_typed \<Gamma> \<rho>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "Elem (\<rho> n) (pp_h_domain \<sigma>)"
  using env lookup unfolding pp_h_env_typed_def by blast

lemma pp_h_env_typed_extend:
  assumes env: "pp_h_env_typed \<Gamma> \<rho>"
    and x: "Elem x (pp_h_domain \<sigma>)"
  shows "pp_h_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
proof (unfold pp_h_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "Elem (extend_env x \<rho> n) (pp_h_domain \<tau>)"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 x by simp
  next
    case (Suc m)
    then have "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    then have "Elem (\<rho> m) (pp_h_domain \<tau>)"
      using pp_h_env_typed_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_h_env_eqv_typed_left:
  "pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_h_env_typed \<Gamma> \<rho>"
  unfolding pp_h_env_eqv_def by blast

lemma pp_h_env_eqv_typed_right:
  "pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_h_env_typed \<Gamma> \<eta>"
  unfolding pp_h_env_eqv_def by blast

lemma pp_h_env_eqv_lookup:
  assumes env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_h_eqv \<sigma> w (\<rho> n) (\<eta> n)"
  using env lookup unfolding pp_h_env_eqv_def by blast

lemma pp_h_env_eqv_refl:
  assumes env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_h_env_eqv w \<Gamma> \<rho> \<rho>"
proof (unfold pp_h_env_eqv_def, intro conjI allI impI)
  show "pp_h_env_typed \<Gamma> \<rho>"
    using env .
  show "pp_h_env_typed \<Gamma> \<rho>"
    using env .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "Elem (\<rho> n) (pp_h_domain \<sigma>)"
    using pp_h_env_typed_lookup[OF env lookup] .
  then show "pp_h_eqv \<sigma> w (\<rho> n) (\<rho> n)"
    by (rule pp_h_eqv_reflexive)
qed

lemma pp_h_env_eqv_persistent:
  assumes env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
    and future: "w \<le> v"
  shows "pp_h_env_eqv v \<Gamma> \<rho> \<eta>"
proof (unfold pp_h_env_eqv_def, intro conjI allI impI)
  show "pp_h_env_typed \<Gamma> \<rho>"
    using pp_h_env_eqv_typed_left[OF env] .
  show "pp_h_env_typed \<Gamma> \<eta>"
    using pp_h_env_eqv_typed_right[OF env] .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "pp_h_eqv \<sigma> w (\<rho> n) (\<eta> n)"
    using pp_h_env_eqv_lookup[OF env lookup] .
  then show "pp_h_eqv \<sigma> v (\<rho> n) (\<eta> n)"
    using future by (rule pp_h_eqv_persistent)
qed

lemma pp_h_env_eqv_extend:
  assumes env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
    and x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
  shows "pp_h_env_eqv w (\<sigma> # \<Gamma>)
    (extend_env x \<rho>) (extend_env y \<eta>)"
proof (unfold pp_h_env_eqv_def, intro conjI allI impI)
  show "pp_h_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
    using pp_h_env_typed_extend[OF pp_h_env_eqv_typed_left[OF env] x] .
  show "pp_h_env_typed (\<sigma> # \<Gamma>) (extend_env y \<eta>)"
    using pp_h_env_typed_extend[OF pp_h_env_eqv_typed_right[OF env] y] .
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "pp_h_eqv \<tau> w
      (extend_env x \<rho> n) (extend_env y \<eta> n)"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 xy by simp
  next
    case (Suc m)
    then have "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    then have "pp_h_eqv \<tau> w (\<rho> m) (\<eta> m)"
      using pp_h_env_eqv_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_h_app_respects:
  assumes fg: "pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
    and x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
  shows "pp_h_eqv \<tau> w (f \<acute> x) (g \<acute> y)"
  using fg x y xy by auto

lemma pp_h_lambda_closed:
  assumes typed:
      "\<And>x. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
        Elem (F x) (pp_h_domain \<tau>)"
    and respects:
      "\<And>w x y. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_h_domain \<sigma>) \<Longrightarrow>
        pp_h_eqv \<sigma> w x y \<Longrightarrow>
        pp_h_eqv \<tau> w (F x) (F y)"
  shows "Elem (Lambda (pp_h_domain \<sigma>) F)
    (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
proof -
  have function_member:
      "Elem (Lambda (pp_h_domain \<sigma>) F)
        (Fun (pp_h_domain \<sigma>) (pp_h_domain \<tau>))"
    using typed by (simp add: Elem_Lambda_Fun)
  have relation_respecting:
      "\<forall>w x y.
        Elem x (pp_h_domain \<sigma>) \<longrightarrow>
        Elem y (pp_h_domain \<sigma>) \<longrightarrow>
        pp_h_eqv \<sigma> w x y \<longrightarrow>
        pp_h_eqv \<tau> w
          ((Lambda (pp_h_domain \<sigma>) F) \<acute> x)
          ((Lambda (pp_h_domain \<sigma>) F) \<acute> y)"
    using respects by (auto simp: Lambda_app)
  show ?thesis
    using function_member relation_respecting by (simp add: Sep)
qed

lemma pp_h_eqv_congruence:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
    and x': "Elem x' (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and y': "Elem y' (pp_h_domain \<sigma>)"
    and xx': "pp_h_eqv \<sigma> w x x'"
    and yy': "pp_h_eqv \<sigma> w y y'"
  shows "pp_h_eqv \<sigma> w x y \<longleftrightarrow>
    pp_h_eqv \<sigma> w x' y'"
proof
  assume xy: "pp_h_eqv \<sigma> w x y"
  have x'x: "pp_h_eqv \<sigma> w x' x"
    using pp_h_eqv_symmetric[OF x x' xx'] .
  have x'y: "pp_h_eqv \<sigma> w x' y"
    using pp_h_eqv_transitive[OF x' x y x'x xy] .
  show "pp_h_eqv \<sigma> w x' y'"
    using pp_h_eqv_transitive[OF x' y y' x'y yy'] .
next
  assume x'y': "pp_h_eqv \<sigma> w x' y'"
  have y'y: "pp_h_eqv \<sigma> w y' y"
    using pp_h_eqv_symmetric[OF y y' yy'] .
  have xy': "pp_h_eqv \<sigma> w x y'"
    using pp_h_eqv_transitive[OF x x' y' xx' x'y'] .
  show "pp_h_eqv \<sigma> w x y"
    using pp_h_eqv_transitive[OF x y' y xy' y'y] .
qed

lemma pp_h_prop_eqv_pp_zf_prop_iff:
  "pp_h_eqv Prop w (pp_zf_prop P) (pp_zf_prop Q) \<longleftrightarrow>
    (\<forall>v \<ge> w. P (nat2Nat v) \<longleftrightarrow> Q (nat2Nat v))"
  by (simp add: Elem_nat2Nat_Nat)

lemma pp_h_prop_in_domain:
  "Elem (pp_zf_prop P) (pp_h_domain Prop)"
  using pp_zf_prop_in_domain by simp

lemma pp_h_prop_eqv_at:
  assumes PQ: "pp_h_eqv Prop w P Q"
    and future: "w \<le> v"
  shows "Elem (nat2Nat v) P \<longleftrightarrow> Elem (nat2Nat v) Q"
  using PQ future by simp

definition pp_h_dom :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_h_dom \<sigma> x \<longleftrightarrow> Elem x (pp_h_domain \<sigma>)"

lemma pp_h_eval_rename:
  "pp_h_eval C \<rho> (rename r M) =
    pp_h_eval C (\<lambda>n. \<rho> (r n)) M"
proof (induction M arbitrary: \<rho> r)
  case (Lam \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Lam.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
next
  case (Forall \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Forall.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
next
  case (Exists \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Exists.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
qed (simp_all add: fun_eq_iff)

lemma pp_h_eval_shift:
  "pp_h_eval C (extend_env x \<rho>) (shift M) = pp_h_eval C \<rho> M"
  unfolding shift_def
  using pp_h_eval_rename[of C "extend_env x \<rho>" Suc M]
  by simp

definition pp_h_list_env :: "ZF list \<Rightarrow> nat \<Rightarrow> ZF" where
  "pp_h_list_env env = nth_default Empty env"

lemma pp_h_list_env_Cons:
  "pp_h_list_env (x # env) = extend_env x (pp_h_list_env env)"
  by (rule ext, rename_tac n, case_tac n)
    (simp_all add: pp_h_list_env_def nth_default_def)

lemma env_ok_implies_pp_h_env_typed:
  assumes env: "env_ok (map pp_h_dom \<Gamma>) xs"
  shows "pp_h_env_typed \<Gamma> (pp_h_list_env xs)"
proof (unfold pp_h_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  then have n_lt: "n < length \<Gamma>" and nth: "\<Gamma> ! n = \<sigma>"
    by (auto simp: lookup_def split: if_splits)
  from env have len: "length xs = length \<Gamma>"
    and entries:
      "\<forall>k<length \<Gamma>. pp_h_dom (\<Gamma> ! k) (xs ! k)"
    by (auto simp: env_ok_def)
  have env_n: "pp_h_list_env xs n = xs ! n"
    using n_lt len
    by (simp add: pp_h_list_env_def nth_default_nth)
  have typed_n: "pp_h_dom (\<Gamma> ! n) (xs ! n)"
    using entries n_lt by blast
  show "Elem (pp_h_list_env xs n) (pp_h_domain \<sigma>)"
    using env_n typed_n nth by (simp add: pp_h_dom_def)
qed

locale pp_h_constants =
  fixes C :: "string \<Rightarrow> otype \<Rightarrow> ZF"
  assumes C_typed: "Elem (C c \<sigma>) (pp_h_domain \<sigma>)"
begin

theorem pp_h_eval_fundamental:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
  shows
    "(\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> M) (pp_h_domain \<tau>)) \<and>
     (\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv \<tau> w (pp_h_eval C \<rho> M) (pp_h_eval C \<eta> M))"
  using typed
proof (induction rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Var n)) (pp_h_domain \<tau>)"
      using Var.hyps pp_h_env_typed_lookup by simp
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv \<tau> w
          (pp_h_eval C \<rho> (Var n)) (pp_h_eval C \<eta> (Var n))"
      using Var.hyps pp_h_env_eqv_lookup by simp
  qed
next
  case (Const \<Gamma> c \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Const c \<tau>)) (pp_h_domain \<tau>)"
      using C_typed by simp
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv \<tau> w
          (pp_h_eval C \<rho> (Const c \<tau>))
          (pp_h_eval C \<eta> (Const c \<tau>))"
      using C_typed pp_h_eqv_reflexive by simp
  qed
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (App M N)) (pp_h_domain \<tau>)"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_h_env_typed \<Gamma> \<rho>"
      have function_member:
          "Elem (pp_h_eval C \<rho> M)
            (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using App.IH(1) env by blast
      have argument:
          "Elem (pp_h_eval C \<rho> N) (pp_h_domain \<sigma>)"
        using App.IH(2) env by blast
      show "Elem (pp_h_eval C \<rho> (App M N)) (pp_h_domain \<tau>)"
        using pp_h_app_closed[OF function_member argument] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv \<tau> w
          (pp_h_eval C \<rho> (App M N)) (pp_h_eval C \<eta> (App M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      have functions_related:
          "pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_h_eval C \<rho> M) (pp_h_eval C \<eta> M)"
        using App.IH(1) env by blast
      have left_argument:
          "Elem (pp_h_eval C \<rho> N) (pp_h_domain \<sigma>)"
        using App.IH(2) pp_h_env_eqv_typed_left[OF env] by blast
      have right_argument:
          "Elem (pp_h_eval C \<eta> N) (pp_h_domain \<sigma>)"
        using App.IH(2) pp_h_env_eqv_typed_right[OF env] by blast
      have arguments:
          "pp_h_eqv \<sigma> w
            (pp_h_eval C \<rho> N) (pp_h_eval C \<eta> N)"
        using App.IH(2) env by blast
      show "pp_h_eqv \<tau> w
          (pp_h_eval C \<rho> (App M N)) (pp_h_eval C \<eta> (App M N))"
        using pp_h_app_respects[
          OF functions_related left_argument right_argument arguments]
        by simp
    qed
  qed
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Lam \<sigma> M))
          (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_h_env_typed \<Gamma> \<rho>"
      have body_typed:
          "\<And>x. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
            Elem (pp_h_eval C (extend_env x \<rho>) M)
              (pp_h_domain \<tau>)"
      proof -
        fix x
        assume x: "Elem x (pp_h_domain \<sigma>)"
        have extended:
            "pp_h_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
          using pp_h_env_typed_extend[OF env x] .
        show "Elem (pp_h_eval C (extend_env x \<rho>) M)
            (pp_h_domain \<tau>)"
          using Lam.IH extended by blast
      qed
      have body_respects:
          "\<And>w x y. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
            Elem y (pp_h_domain \<sigma>) \<Longrightarrow>
            pp_h_eqv \<sigma> w x y \<Longrightarrow>
            pp_h_eqv \<tau> w
              (pp_h_eval C (extend_env x \<rho>) M)
              (pp_h_eval C (extend_env y \<rho>) M)"
      proof -
        fix w x y
        assume x: "Elem x (pp_h_domain \<sigma>)"
          and y: "Elem y (pp_h_domain \<sigma>)"
          and xy: "pp_h_eqv \<sigma> w x y"
        have base: "pp_h_env_eqv w \<Gamma> \<rho> \<rho>"
          using pp_h_env_eqv_refl[OF env] .
        have extended:
            "pp_h_env_eqv w (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<rho>)"
          using pp_h_env_eqv_extend[OF base x y xy] .
        show "pp_h_eqv \<tau> w
            (pp_h_eval C (extend_env x \<rho>) M)
            (pp_h_eval C (extend_env y \<rho>) M)"
          using Lam.IH extended by blast
      qed
      show "Elem (pp_h_eval C \<rho> (Lam \<sigma> M))
          (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using pp_h_lambda_closed[OF body_typed body_respects] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_h_eval C \<rho> (Lam \<sigma> M))
          (pp_h_eval C \<eta> (Lam \<sigma> M))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_h_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_h_eval C \<rho> (Lam \<sigma> M))
          (pp_h_eval C \<eta> (Lam \<sigma> M))"
        unfolding pp_h_eval.simps pp_h_eqv.simps
      proof (intro allI impI)
        fix v x y
        assume future: "w \<le> v"
          and x: "Elem x (pp_h_domain \<sigma>)"
          and y: "Elem y (pp_h_domain \<sigma>)"
          and xy: "pp_h_eqv \<sigma> v x y"
        have base: "pp_h_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_h_env_eqv_persistent[OF env future] .
        have extended:
            "pp_h_env_eqv v (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<eta>)"
          using pp_h_env_eqv_extend[OF base x y xy] .
        have body:
            "pp_h_eqv \<tau> v
              (pp_h_eval C (extend_env x \<rho>) M)
              (pp_h_eval C (extend_env y \<eta>) M)"
          using Lam.IH extended by blast
        show "pp_h_eqv \<tau> v
            ((Lambda (pp_h_domain \<sigma>)
              (\<lambda>x. pp_h_eval C (extend_env x \<rho>) M)) \<acute> x)
            ((Lambda (pp_h_domain \<sigma>)
              (\<lambda>x. pp_h_eval C (extend_env x \<eta>) M)) \<acute> y)"
          using body x y by (simp add: Lambda_app)
      qed
    qed
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Eq \<sigma> M N)) (pp_h_domain Prop)"
    proof (intro allI impI)
      fix \<rho>
      assume "pp_h_env_typed \<Gamma> \<rho>"
      show "Elem (pp_h_eval C \<rho> (Eq \<sigma> M N)) (pp_h_domain Prop)"
        unfolding pp_h_eval.simps
        by (rule pp_h_prop_in_domain)
    qed
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Eq \<sigma> M N))
          (pp_h_eval C \<eta> (Eq \<sigma> M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Eq \<sigma> M N))
          (pp_h_eval C \<eta> (Eq \<sigma> M N))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "w \<le> v"
        have env_v: "pp_h_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_h_env_eqv_persistent[OF env future] .
        have M_left:
            "Elem (pp_h_eval C \<rho> M) (pp_h_domain \<sigma>)"
          using Eq.IH(1) pp_h_env_eqv_typed_left[OF env] by blast
        have M_right:
            "Elem (pp_h_eval C \<eta> M) (pp_h_domain \<sigma>)"
          using Eq.IH(1) pp_h_env_eqv_typed_right[OF env] by blast
        have N_left:
            "Elem (pp_h_eval C \<rho> N) (pp_h_domain \<sigma>)"
          using Eq.IH(2) pp_h_env_eqv_typed_left[OF env] by blast
        have N_right:
            "Elem (pp_h_eval C \<eta> N) (pp_h_domain \<sigma>)"
          using Eq.IH(2) pp_h_env_eqv_typed_right[OF env] by blast
        have M_related:
            "pp_h_eqv \<sigma> v
              (pp_h_eval C \<rho> M) (pp_h_eval C \<eta> M)"
          using Eq.IH(1) env_v by blast
        have N_related:
            "pp_h_eqv \<sigma> v
              (pp_h_eval C \<rho> N) (pp_h_eval C \<eta> N)"
          using Eq.IH(2) env_v by blast
        show "pp_h_eqv \<sigma> (Nat2nat (nat2Nat v))
              (pp_h_eval C \<rho> M) (pp_h_eval C \<rho> N) =
            pp_h_eqv \<sigma> (Nat2nat (nat2Nat v))
              (pp_h_eval C \<eta> M) (pp_h_eval C \<eta> N)"
          using pp_h_eqv_congruence[
            OF M_left M_right N_left N_right M_related N_related]
          by simp
      qed
    qed
  qed
next
  case (Neg \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Neg A)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Neg A)) (pp_h_eval C \<eta> (Neg A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      have related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> A) (pp_h_eval C \<eta> A)"
        using Neg.IH env by blast
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Neg A)) (pp_h_eval C \<eta> (Neg A))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
        using pp_h_prop_eqv_at[OF related] by blast
    qed
  qed
next
  case (Conj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Conj A B)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Conj A B))
          (pp_h_eval C \<eta> (Conj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> A) (pp_h_eval C \<eta> A)"
        using Conj.IH(1) env by blast
      have B_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> B) (pp_h_eval C \<eta> B)"
        using Conj.IH(2) env by blast
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Conj A B))
          (pp_h_eval C \<eta> (Conj A B))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
        using pp_h_prop_eqv_at[OF A_related]
          pp_h_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Disj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Disj A B)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Disj A B))
          (pp_h_eval C \<eta> (Disj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> A) (pp_h_eval C \<eta> A)"
        using Disj.IH(1) env by blast
      have B_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> B) (pp_h_eval C \<eta> B)"
        using Disj.IH(2) env by blast
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Disj A B))
          (pp_h_eval C \<eta> (Disj A B))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
        using pp_h_prop_eqv_at[OF A_related]
          pp_h_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Imp \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Imp A B)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Imp A B))
          (pp_h_eval C \<eta> (Imp A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> A) (pp_h_eval C \<eta> A)"
        using Imp.IH(1) env by blast
      have B_related:
          "pp_h_eqv Prop w (pp_h_eval C \<rho> B) (pp_h_eval C \<eta> B)"
        using Imp.IH(2) env by blast
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Imp A B))
          (pp_h_eval C \<eta> (Imp A B))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
        using pp_h_prop_eqv_at[OF A_related]
          pp_h_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Forall \<sigma> A)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Forall \<sigma> A))
          (pp_h_eval C \<eta> (Forall \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Forall \<sigma> A))
          (pp_h_eval C \<eta> (Forall \<sigma> A))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "w \<le> v"
        have base: "pp_h_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_h_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
              (Elem (nat2Nat v)
                  (pp_h_eval C (extend_env x \<rho>) A) \<longleftrightarrow>
               Elem (nat2Nat v)
                  (pp_h_eval C (extend_env x \<eta>) A))"
        proof -
          fix x
          assume x: "Elem x (pp_h_domain \<sigma>)"
          have xx: "pp_h_eqv \<sigma> v x x"
            using pp_h_eqv_reflexive[OF x] .
          have extended:
              "pp_h_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_h_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_h_eqv Prop v
                (pp_h_eval C (extend_env x \<rho>) A)
                (pp_h_eval C (extend_env x \<eta>) A)"
            using Forall.IH extended by blast
          show "Elem (nat2Nat v)
                (pp_h_eval C (extend_env x \<rho>) A) \<longleftrightarrow>
              Elem (nat2Nat v)
                (pp_h_eval C (extend_env x \<eta>) A)"
            using pp_h_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<forall>x. Elem x (pp_h_domain \<sigma>) \<longrightarrow>
              Elem (nat2Nat v) (pp_h_eval C (extend_env x \<rho>) A)) =
            (\<forall>x. Elem x (pp_h_domain \<sigma>) \<longrightarrow>
              Elem (nat2Nat v) (pp_h_eval C (extend_env x \<eta>) A))"
          using body_iff by blast
      qed
    qed
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_h_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_h_eval C \<rho> (Exists \<sigma> A)) (pp_h_domain Prop)"
      by (intro allI impI; simp only: pp_h_eval.simps;
          rule pp_h_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_h_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Exists \<sigma> A))
          (pp_h_eval C \<eta> (Exists \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_h_eqv Prop w
          (pp_h_eval C \<rho> (Exists \<sigma> A))
          (pp_h_eval C \<eta> (Exists \<sigma> A))"
        unfolding pp_h_eval.simps pp_h_prop_eqv_pp_zf_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "w \<le> v"
        have base: "pp_h_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_h_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
              (Elem (nat2Nat v)
                  (pp_h_eval C (extend_env x \<rho>) A) \<longleftrightarrow>
               Elem (nat2Nat v)
                  (pp_h_eval C (extend_env x \<eta>) A))"
        proof -
          fix x
          assume x: "Elem x (pp_h_domain \<sigma>)"
          have xx: "pp_h_eqv \<sigma> v x x"
            using pp_h_eqv_reflexive[OF x] .
          have extended:
              "pp_h_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_h_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_h_eqv Prop v
                (pp_h_eval C (extend_env x \<rho>) A)
                (pp_h_eval C (extend_env x \<eta>) A)"
            using Exists.IH extended by blast
          show "Elem (nat2Nat v)
                (pp_h_eval C (extend_env x \<rho>) A) \<longleftrightarrow>
              Elem (nat2Nat v)
                (pp_h_eval C (extend_env x \<eta>) A)"
            using pp_h_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<exists>x. Elem x (pp_h_domain \<sigma>) \<and>
              Elem (nat2Nat v) (pp_h_eval C (extend_env x \<rho>) A)) =
            (\<exists>x. Elem x (pp_h_domain \<sigma>) \<and>
              Elem (nat2Nat v) (pp_h_eval C (extend_env x \<eta>) A))"
          using body_iff by blast
      qed
    qed
  qed
qed

lemma pp_h_eval_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_h_dom \<tau> (pp_h_eval C \<rho> M)"
  using pp_h_eval_fundamental[OF typed] env
  unfolding pp_h_dom_def by blast

lemma pp_h_eval_respects:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_h_env_eqv w \<Gamma> \<rho> \<eta>"
  shows "pp_h_eqv \<tau> w (pp_h_eval C \<rho> M) (pp_h_eval C \<eta> M)"
  using pp_h_eval_fundamental[OF typed] env by blast

definition pp_h_den :: "oterm \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "pp_h_den A env = pp_h_eval C (pp_h_list_env env) A"

sublocale HHenkin:
  henkin_action_model pp_h_dom pp_zf_holds pp_h_den
proof
  fix \<Gamma> A \<sigma> env
  assume typed: "\<Gamma> \<turnstile> A : \<sigma>"
    and env: "env_ok (map pp_h_dom \<Gamma>) env"
  show "pp_h_dom \<sigma> (pp_h_den A env)"
    unfolding pp_h_den_def
    using pp_h_eval_type[OF typed env_ok_implies_pp_h_env_typed[OF env]] .
next
  show "pp_zf_holds (pp_h_den (Neg A) env) w \<longleftrightarrow>
      \<not> pp_zf_holds (pp_h_den A env) w" for A env w
    by (simp only: pp_h_den_def pp_h_eval_Neg_holds)
next
  show "pp_zf_holds (pp_h_den (Imp A B) env) w \<longleftrightarrow>
      (pp_zf_holds (pp_h_den A env) w \<longrightarrow>
       pp_zf_holds (pp_h_den B env) w)" for A B env w
    by (simp only: pp_h_den_def pp_h_eval_Imp_holds)
next
  show "pp_zf_holds (pp_h_den (Forall \<sigma> Q) env) w \<longleftrightarrow>
      (\<forall>x. pp_h_dom \<sigma> x \<longrightarrow>
        pp_zf_holds (pp_h_den Q (x # env)) w)" for \<sigma> Q env w
    by (simp only: pp_h_den_def pp_h_dom_def pp_h_list_env_Cons
      pp_h_eval_Forall_holds)
next
  show "pp_zf_holds (pp_h_den (Exists \<sigma> P) env) w \<longleftrightarrow>
      (\<exists>x. pp_h_dom \<sigma> x \<and>
        pp_zf_holds (pp_h_den P (x # env)) w)" for \<sigma> P env w
    by (simp only: pp_h_den_def pp_h_dom_def pp_h_list_env_Cons
      pp_h_eval_Exists_holds)
next
  show "pp_h_den (shift A) (x # env) = pp_h_den A env" for A x env
    by (simp add: pp_h_den_def pp_h_list_env_Cons pp_h_eval_shift)
next
  show "\<exists>x. pp_h_dom \<sigma> x" for \<sigma>
    using pp_h_domain_nonempty by (simp add: pp_h_dom_def)
qed

end

definition pp_h_default_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_h_default_constants c \<sigma> = pp_h_default \<sigma>"

interpretation DefaultHConstants:
  pp_h_constants pp_h_default_constants
  by standard
    (simp add: pp_h_default_constants_def pp_h_default_in_domain)

section \<open>Internal Pure and Fun classifiers\<close>

definition pp_h_predicate_admissible ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_h_predicate_admissible \<sigma> Q \<longleftrightarrow>
    (\<forall>w x y.
      Elem x (pp_h_domain \<sigma>) \<longrightarrow>
      Elem y (pp_h_domain \<sigma>) \<longrightarrow>
      pp_h_eqv \<sigma> w x y \<longrightarrow>
      (\<forall>v \<ge> w. Q v x \<longleftrightarrow> Q v y))"

definition pp_h_classifier ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_h_classifier \<sigma> Q =
    Lambda (pp_h_domain \<sigma>)
      (\<lambda>x. pp_zf_prop (\<lambda>z. Q (Nat2nat z) x))"

lemma pp_h_classifier_in_domain:
  assumes admissible: "pp_h_predicate_admissible \<sigma> Q"
  shows "Elem (pp_h_classifier \<sigma> Q)
    (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
proof (unfold pp_h_classifier_def, rule pp_h_lambda_closed)
  show "\<And>x. Elem x (pp_h_domain \<sigma>) \<Longrightarrow>
      Elem (pp_zf_prop (\<lambda>z. Q (Nat2nat z) x))
        (pp_h_domain Prop)"
    by (rule pp_h_prop_in_domain)
  fix w x y
  assume x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
  show "pp_h_eqv Prop w
      (pp_zf_prop (\<lambda>z. Q (Nat2nat z) x))
      (pp_zf_prop (\<lambda>z. Q (Nat2nat z) y))"
    unfolding pp_h_prop_eqv_pp_zf_prop_iff
    using admissible x y xy
    by (simp add: pp_h_predicate_admissible_def)
qed

lemma pp_h_classifier_apply:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
  shows "(pp_h_classifier \<sigma> Q) \<acute> x =
    pp_zf_prop (\<lambda>z. Q (Nat2nat z) x)"
  using x by (simp add: pp_h_classifier_def Lambda_app)

lemma pp_h_classifier_holds:
  assumes x: "Elem x (pp_h_domain \<sigma>)"
  shows "pp_zf_holds ((pp_h_classifier \<sigma> Q) \<acute> x) w
    \<longleftrightarrow> Q w x"
  using pp_h_classifier_apply[OF x, of Q]
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

lemma pp_h_truth_in_domain:
  "Elem (pp_zf_truth b) (pp_h_domain Prop)"
  unfolding pp_zf_truth_def
  by (rule pp_h_prop_in_domain)

lemma pp_h_identity_predicate_admissible:
  assumes a: "Elem a (pp_h_domain \<sigma>)"
  shows "pp_h_predicate_admissible \<sigma>
    (\<lambda>w x. pp_h_eqv \<sigma> w x a)"
  unfolding pp_h_predicate_admissible_def
proof (intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
    and future: "w \<le> v"
  have xy_v: "pp_h_eqv \<sigma> v x y"
    using pp_h_eqv_persistent[OF xy future] .
  have aa: "pp_h_eqv \<sigma> v a a"
    using pp_h_eqv_reflexive[OF a] .
  show "pp_h_eqv \<sigma> v x a = pp_h_eqv \<sigma> v y a"
    using pp_h_eqv_congruence[OF x y a a xy_v aa] .
qed

fun pp_h_fundamental_at ::
    "otype \<Rightarrow> ZF \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_h_fundamental_at Ind r w x = False"
| "pp_h_fundamental_at Prop r w x = pp_h_eqv Prop w x r"
| "pp_h_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) r w x = False"

lemma pp_h_fundamental_admissible:
  assumes r: "Elem r (pp_h_domain Prop)"
  shows "pp_h_predicate_admissible \<sigma> (pp_h_fundamental_at \<sigma> r)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_h_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_h_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_h_domain Prop)"
      and y: "Elem y (pp_h_domain Prop)"
      and xy: "pp_h_eqv Prop w x y"
      and future: "w \<le> v"
    have xy_v: "pp_h_eqv Prop v x y"
      using pp_h_eqv_persistent[OF xy future] .
    have rr: "pp_h_eqv Prop v r r"
      using pp_h_eqv_reflexive[OF r] .
    show "pp_h_fundamental_at Prop r v x =
        pp_h_fundamental_at Prop r v y"
      using pp_h_eqv_congruence[OF x y r r xy_v rr] by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_h_predicate_admissible_def)
qed

fun pp_h_internal_constants ::
    "(otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      ZF \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_h_internal_constants Pure r c Ind = pp_h_default Ind"
| "pp_h_internal_constants Pure r c Prop = pp_h_default Prop"
| "pp_h_internal_constants Pure r c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_h_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_h_classifier \<sigma> (pp_h_fundamental_at \<sigma> r)
     else pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

locale pp_h_internal_parameters =
  fixes Pure :: "otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool"
    and r :: ZF
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_h_predicate_admissible \<sigma> (Pure \<sigma>)"
    and r_typed: "Elem r (pp_h_domain Prop)"
begin

lemma pp_h_internal_constants_typed:
  "Elem (pp_h_internal_constants Pure r c \<sigma>) (pp_h_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_h_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_h_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem (pp_h_classifier \<sigma> (Pure \<sigma>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_h_classifier_in_domain[OF Pure_admissible] .
  have fun_classifier:
      "Elem
        (pp_h_classifier \<sigma> (pp_h_fundamental_at \<sigma> r))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_h_classifier_in_domain[
      OF pp_h_fundamental_admissible[OF r_typed]] .
  have default:
      "Elem (pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_h_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

sublocale Constants:
  pp_h_constants "pp_h_internal_constants Pure r"
  by standard (rule pp_h_internal_constants_typed)

lemma pp_h_eval_Pure[simp]:
  "pp_h_eval (pp_h_internal_constants Pure r) \<rho> (pp_Pure \<sigma>) =
    pp_h_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_h_eval_Fun[simp]:
  "pp_h_eval (pp_h_internal_constants Pure r) \<rho> (pp_Fun \<sigma>) =
    pp_h_classifier \<sigma> (pp_h_fundamental_at \<sigma> r)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_h_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_zf_holds
      (pp_h_eval (pp_h_internal_constants Pure r) \<rho> (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      Pure \<sigma> w
        (pp_h_eval (pp_h_internal_constants Pure r) \<rho> M)"
proof -
  have argument:
      "Elem (pp_h_eval (pp_h_internal_constants Pure r) \<rho> M)
        (pp_h_domain \<sigma>)"
    using Constants.pp_h_eval_type[OF typed env]
    by (simp add: pp_h_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_h_classifier_holds[OF argument, of "Pure \<sigma>" w]
    by simp
qed

lemma pp_h_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_zf_holds
      (pp_h_eval (pp_h_internal_constants Pure r) \<rho> (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_h_fundamental_at \<sigma> r w
        (pp_h_eval (pp_h_internal_constants Pure r) \<rho> M)"
proof -
  have argument:
      "Elem (pp_h_eval (pp_h_internal_constants Pure r) \<rho> M)
        (pp_h_domain \<sigma>)"
    using Constants.pp_h_eval_type[OF typed env]
    by (simp add: pp_h_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_h_classifier_holds[
      OF argument, of "pp_h_fundamental_at \<sigma> r" w]
    by simp
qed

lemma pp_h_unique_fundamental_holds:
  "pp_zf_holds
    (pp_h_eval (pp_h_internal_constants Pure r) \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  have base: "pp_h_env_typed [] \<rho>"
    by (simp add: pp_h_env_typed_def lookup_def)
  have r_env:
      "pp_h_env_typed [Prop] (extend_env r \<rho>)"
    using pp_h_env_typed_extend[OF base r_typed] .
  have r_is_fundamental:
      "pp_zf_holds
        (pp_h_eval (pp_h_internal_constants Pure r) (extend_env r \<rho>)
          (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_h_eqv Prop w r r"
      using pp_h_eqv_reflexive[OF r_typed] .
    show ?thesis
      using pp_h_eval_fun_holds[OF var_type r_env, of w] rr by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_h_domain Prop) \<longrightarrow>
        pp_zf_holds
          (pp_h_eval (pp_h_internal_constants Pure r)
            (extend_env y (extend_env r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_h_domain Prop)"
    have yr_env:
        "pp_h_env_typed [Prop, Prop]
          (extend_env y (extend_env r \<rho>))"
      using pp_h_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have r_type: "[Prop, Prop] \<turnstile> Var 1 : Prop"
      by simp
    have fun_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_internal_constants Pure r)
            (extend_env y (extend_env r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_h_eqv Prop w y r"
      using pp_h_eval_fun_holds[OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_internal_constants Pure r)
            (extend_env y (extend_env r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_h_eqv Prop w y r"
      by simp
    show "pp_zf_holds
        (pp_h_eval (pp_h_internal_constants Pure r)
          (extend_env y (extend_env r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_h_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_h_eval_Exists_holds)
    apply (rule exI[of _ r])
    using r_typed r_is_fundamental uniqueness
    by (simp only: pp_h_eval_Conj_holds pp_h_eval_Forall_holds)
qed

lemma pp_h_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_zf_holds
    (pp_h_eval (pp_h_internal_constants Pure r) \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_h_env_typed [] \<rho>"
    by (simp add: pp_h_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_h_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_h_domain \<sigma>)"
    have extended:
        "pp_h_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_h_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_h_fundamental_at \<sigma> r w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_internal_constants Pure r) (extend_env x \<rho>)
            (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_h_fundamental_at \<sigma> r w x"
      using pp_h_eval_fun_holds[OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_zf_holds
          (pp_h_eval (pp_h_internal_constants Pure r) (extend_env x \<rho>)
            (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_zf_holds
        (pp_h_eval (pp_h_internal_constants Pure r) (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_h_eval_Neg_holds[
        of "pp_h_internal_constants Pure r" "extend_env x \<rho>"
          "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_h_unique_fundamental_gvalid:
  "Constants.HHenkin.gvalid [] (pp_unique_fundamental Prop)"
  unfolding Constants.HHenkin.gvalid_def Constants.pp_h_den_def
  using pp_h_unique_fundamental_holds by blast

theorem pp_h_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "Constants.HHenkin.gvalid [] (pp_no_fundamentals \<sigma>)"
  unfolding Constants.HHenkin.gvalid_def Constants.pp_h_den_def
  using pp_h_no_fundamentals_holds[OF assms] by blast

end

section \<open>The box/complement obstruction\<close>

definition pp_frame_box ::
    "('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool"
  where
  "pp_frame_box R p w \<longleftrightarrow> (\<forall>v. R w v \<longrightarrow> p v)"

definition pp_frame_diamond ::
    "('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool"
  where
  "pp_frame_diamond R p w \<longleftrightarrow> (\<exists>v. R w v \<and> p v)"

definition pp_frame_unary_recombines_at ::
    "('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow>
      ((('w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow>
      ('w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool"
  where
  "pp_frame_unary_recombines_at R Pure p w \<longleftrightarrow>
    (\<forall>X. Pure X \<longrightarrow>
      pp_frame_box R (X p) w \<longrightarrow>
      (\<forall>q. X q w))"

theorem pp_directed_frame_not_box_diamond_box_obstruction:
  fixes R :: "'w \<Rightarrow> 'w \<Rightarrow> bool"
    and Pure ::
      "(('w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> bool"
  assumes reflexive: "\<And>w. R w w"
    and transitive:
      "\<And>w u v. R w u \<Longrightarrow> R u v \<Longrightarrow> R w v"
    and directed:
      "\<And>w u v. R w u \<Longrightarrow> R w v \<Longrightarrow>
        \<exists>z. R u z \<and> R v z"
    and recombination:
      "pp_frame_unary_recombines_at R Pure p w"
    and not_box_pure:
      "Pure (\<lambda>q u. \<not> pp_frame_box R q u)"
    and diamond_box_pure:
      "Pure
        (\<lambda>q u. pp_frame_diamond R (pp_frame_box R q) u)"
  shows False
proof -
  have eventually_box:
      "pp_frame_diamond R (pp_frame_box R p) w"
  proof (rule ccontr)
    assume no_eventually_box:
      "\<not> pp_frame_diamond R (pp_frame_box R p) w"
    have necessary_not_box:
        "pp_frame_box R
          ((\<lambda>q u. \<not> pp_frame_box R q u) p) w"
      using no_eventually_box
      unfolding pp_frame_box_def pp_frame_diamond_def by blast
    have universal_not_box:
        "\<forall>q. \<not> pp_frame_box R q w"
      using recombination not_box_pure necessary_not_box
      unfolding pp_frame_unary_recombines_at_def by blast
    have "pp_frame_box R (\<lambda>_. True) w"
      unfolding pp_frame_box_def by simp
    then show False
      using universal_not_box[rule_format, of "\<lambda>_. True"] by blast
  qed
  then obtain v where wv: "R w v"
    and box_p_v: "pp_frame_box R p v"
    unfolding pp_frame_diamond_def by blast
  have necessary_diamond_box:
      "pp_frame_box R
        (\<lambda>u. pp_frame_diamond R (pp_frame_box R p) u) w"
    using wv box_p_v directed transitive
    unfolding pp_frame_box_def pp_frame_diamond_def
    by blast
  have universal_diamond_box:
      "\<forall>q. pp_frame_diamond R (pp_frame_box R q) w"
    using recombination diamond_box_pure necessary_diamond_box
    unfolding pp_frame_unary_recombines_at_def by blast
  obtain u where wu: "R w u"
    and box_false_u: "pp_frame_box R (\<lambda>_. False) u"
    using universal_diamond_box[rule_format, of "\<lambda>_. False"]
    unfolding pp_frame_diamond_def by blast
  have "False"
    using box_false_u reflexive[of u]
    unfolding pp_frame_box_def by blast
  then show False .
qed

section \<open>A nonconvergent branching replacement\<close>

definition pp_tree_access :: "bool list \<Rightarrow> bool list \<Rightarrow> bool"
  where
  "pp_tree_access u v \<longleftrightarrow> prefix u v"

definition pp_tree_seed :: "bool list \<Rightarrow> bool list \<Rightarrow> bool"
  where
  "pp_tree_seed w u \<longleftrightarrow> prefix (w @ [True]) u"

lemma pp_tree_access_reflexive:
  "pp_tree_access w w"
  unfolding pp_tree_access_def by simp

lemma pp_tree_access_transitive:
  assumes "pp_tree_access w u" and "pp_tree_access u v"
  shows "pp_tree_access w v"
  using assms unfolding pp_tree_access_def
  by (rule prefix_order.trans)

lemma pp_tree_split_incomparable:
  "\<not> pp_tree_access (w @ [False]) (w @ [True])"
  "\<not> pp_tree_access (w @ [True]) (w @ [False])"
  unfolding pp_tree_access_def by simp_all

lemma pp_tree_split_no_common_successor:
  "\<not> (\<exists>z.
    pp_tree_access (w @ [False]) z \<and>
    pp_tree_access (w @ [True]) z)"
proof
  assume "\<exists>z.
      pp_tree_access (w @ [False]) z \<and>
      pp_tree_access (w @ [True]) z"
  then obtain z where false_z:
      "prefix (w @ [False]) z"
    and true_z: "prefix (w @ [True]) z"
    unfolding pp_tree_access_def by blast
  have "prefix (w @ [False]) (w @ [True]) \<or>
      prefix (w @ [True]) (w @ [False])"
    using prefix_same_cases[OF false_z true_z] .
  then show False by simp
qed

lemma pp_tree_seed_box_on_left:
  "pp_frame_box pp_tree_access (pp_tree_seed w) (w @ [True])"
  unfolding pp_frame_box_def pp_tree_access_def pp_tree_seed_def
  by simp

lemma pp_tree_seed_no_eventual_box_on_right:
  "\<not> pp_frame_diamond pp_tree_access
    (pp_frame_box pp_tree_access (pp_tree_seed w))
    (w @ [False])"
proof
  assume eventual:
      "pp_frame_diamond pp_tree_access
        (pp_frame_box pp_tree_access (pp_tree_seed w))
        (w @ [False])"
  then obtain v where false_v:
      "pp_tree_access (w @ [False]) v"
    and box_seed_v:
      "pp_frame_box pp_tree_access (pp_tree_seed w) v"
    unfolding pp_frame_diamond_def by blast
  have seed_v: "pp_tree_seed w v"
    using box_seed_v pp_tree_access_reflexive[of v]
    unfolding pp_frame_box_def by blast
  have true_v: "pp_tree_access (w @ [True]) v"
    using seed_v unfolding pp_tree_seed_def pp_tree_access_def .
  show False
    using pp_tree_split_no_common_successor[of w]
      false_v true_v by blast
qed

theorem pp_tree_local_seed_escapes_directed_obstruction:
  "\<not> pp_frame_box pp_tree_access
      ((\<lambda>q u. \<not> pp_frame_box pp_tree_access q u)
        (pp_tree_seed w)) w"
  "\<not> pp_frame_box pp_tree_access
      ((\<lambda>q u.
          pp_frame_diamond pp_tree_access
            (pp_frame_box pp_tree_access q) u)
        (pp_tree_seed w)) w"
proof -
  have root_left:
      "pp_tree_access w (w @ [True])"
    unfolding pp_tree_access_def by simp
  show "\<not> pp_frame_box pp_tree_access
      ((\<lambda>q u. \<not> pp_frame_box pp_tree_access q u)
        (pp_tree_seed w)) w"
    using root_left pp_tree_seed_box_on_left[of w]
    unfolding pp_frame_box_def by blast
  have root_right:
      "pp_tree_access w (w @ [False])"
    unfolding pp_tree_access_def by simp
  show "\<not> pp_frame_box pp_tree_access
      ((\<lambda>q u.
          pp_frame_diamond pp_tree_access
            (pp_frame_box pp_tree_access q) u)
        (pp_tree_seed w)) w"
    using root_right pp_tree_seed_no_eventual_box_on_right[of w]
    unfolding pp_frame_box_def by blast
qed

definition pp_h_box_classifier :: ZF where
  "pp_h_box_classifier =
    pp_h_classifier Prop
      (\<lambda>w q. pp_h_eqv Prop w q (pp_zf_truth True))"

definition pp_h_not_box_classifier :: ZF where
  "pp_h_not_box_classifier =
    pp_h_classifier Prop
      (\<lambda>w q. \<not> pp_h_eqv Prop w q (pp_zf_truth True))"

definition pp_h_diamond_box_classifier :: ZF where
  "pp_h_diamond_box_classifier =
    pp_h_classifier Prop
      (\<lambda>w q. \<exists>v \<ge> w.
        pp_h_eqv Prop v q (pp_zf_truth True))"

definition pp_h_diamond_box_logical_operator :: oterm where
  "pp_h_diamond_box_logical_operator =
    Lam Prop (\<diamond>\<^sub>o (\<box>\<^sub>o (Var 0)))"

lemma pp_h_diamond_box_logical_operator_typed:
  "[] \<turnstile> pp_h_diamond_box_logical_operator :
    Prop \<rightarrow>\<^sub>o Prop"
  unfolding pp_h_diamond_box_logical_operator_def
  by (intro has_type.Lam typed_ObjDiamond typed_ObjBox has_type.Var)
    simp_all

lemma pp_h_diamond_box_logical_operator_logical:
  "pp_logical_vocabulary pp_h_diamond_box_logical_operator"
  by (simp add: pp_logical_vocabulary_def
      pp_h_diamond_box_logical_operator_def ObjDiamond_def
      ObjBox_def ObjTrue_def)

lemma pp_h_diamond_box_logical_operator_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop)
      pp_h_diamond_box_logical_operator
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_h_diamond_box_logical_operator :
      Prop \<rightarrow>\<^sub>o Prop"
    by (rule pp_h_diamond_box_logical_operator_typed)
  show "pp_logical_vocabulary pp_h_diamond_box_logical_operator"
    by (rule pp_h_diamond_box_logical_operator_logical)
qed simp

lemma pp_h_eval_ObjTrue:
  "pp_h_eval C \<rho> ObjTrue = pp_zf_truth True"
  unfolding ObjTrue_def
  apply simp
  unfolding pp_zf_truth_def pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep)

lemma pp_h_prop_neg_prop:
  "pp_zf_prop (\<lambda>z. \<not> Elem z (pp_zf_prop Q)) =
    pp_zf_prop (\<lambda>z. \<not> Q z)"
  unfolding pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep)

lemma pp_h_eval_box_logical_operator:
  "pp_h_eval C \<rho> pp_zf_eq_truth_operator = pp_h_box_classifier"
  unfolding pp_zf_eq_truth_operator_def pp_h_box_classifier_def
    pp_h_classifier_def
  by (simp add: pp_h_eval_ObjTrue extend_env.simps)

lemma pp_h_eval_not_box_logical_operator:
  "pp_h_eval C \<rho> pp_zf_neq_truth_operator =
    pp_h_not_box_classifier"
  unfolding pp_zf_neq_truth_operator_def pp_h_not_box_classifier_def
    pp_h_classifier_def
  apply (simp only: pp_h_eval.simps pp_h_eval_ObjTrue)
  apply (simp only: Lambda_ext)
  apply (intro conjI allI impI)
   apply simp
  apply (simp only: extend_env.simps pp_h_eval.simps pp_h_eval_ObjTrue)
  by (rule pp_h_prop_neg_prop)

lemma pp_h_eval_ObjBox_holds:
  "pp_zf_holds (pp_h_eval C \<rho> (\<box>\<^sub>o A)) w
    \<longleftrightarrow>
    pp_h_eqv Prop w (pp_h_eval C \<rho> A) (pp_zf_truth True)"
  by (simp add: ObjBox_def pp_h_eval_ObjTrue)

lemma pp_h_eval_ObjDiamond_holds:
  "pp_zf_holds (pp_h_eval C \<rho> (\<diamond>\<^sub>o A)) w
    \<longleftrightarrow>
      (\<exists>v \<ge> w. pp_zf_holds (pp_h_eval C \<rho> A) v)"
  unfolding ObjDiamond_def
  by (simp only: pp_h_eval_Neg_holds
      pp_h_eval_ObjBox_holds pp_h_prop_eqv_truth_iff;
      blast)

lemma pp_h_eval_diamond_box_holds:
  "pp_zf_holds
      (pp_h_eval C \<rho> (\<diamond>\<^sub>o (\<box>\<^sub>o A))) w
    \<longleftrightarrow>
    (\<exists>v \<ge> w.
      pp_h_eqv Prop v (pp_h_eval C \<rho> A) (pp_zf_truth True))"
  by (simp add: pp_h_eval_ObjDiamond_holds
      pp_h_eval_ObjBox_holds)

lemma pp_h_prop_ext:
  assumes P: "Elem P (pp_h_domain Prop)"
    and Q: "Elem Q (pp_h_domain Prop)"
    and holds:
      "\<And>w. pp_zf_holds P w \<longleftrightarrow> pp_zf_holds Q w"
  shows "P = Q"
  apply (subst Ext)
proof
  fix z
  have P_sub: "subset P Nat"
    using P by (simp add: Power)
  have Q_sub: "subset Q Nat"
    using Q by (simp add: Power)
  show "Elem z P = Elem z Q"
  proof (cases "Elem z Nat")
    case True
    have code: "nat2Nat (Nat2nat z) = z"
      using True by simp
    show ?thesis
      using holds[of "Nat2nat z"]
      unfolding pp_zf_holds_def code .
  next
    case False
    have "\<not> Elem z P" and "\<not> Elem z Q"
      using P_sub Q_sub False
      by (auto simp: subset_def)
    then show ?thesis by simp
  qed
qed

lemma pp_h_eval_diamond_box_logical_operator:
  "pp_h_eval C \<rho> pp_h_diamond_box_logical_operator =
    pp_h_diamond_box_classifier"
  unfolding pp_h_diamond_box_logical_operator_def
    pp_h_diamond_box_classifier_def pp_h_classifier_def
  apply (simp only: pp_h_eval.simps Lambda_ext)
  apply (intro conjI allI impI)
   apply simp
  apply (rule pp_h_prop_ext)
  subgoal
    unfolding ObjDiamond_def ObjBox_def
    by (simp only: pp_h_eval.simps; rule pp_h_prop_in_domain)
  subgoal
    by (rule pp_h_prop_in_domain)
  subgoal for q w
    using pp_h_eval_diamond_box_holds[
      of C "extend_env q \<rho>" "Var 0" w]
    by (simp add: pp_h_classifier_holds)
  done

lemma pp_h_box_logical_operator_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_zf_eq_truth_operator
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_zf_eq_truth_operator : Prop \<rightarrow>\<^sub>o Prop"
    by (rule pp_zf_eq_truth_operator_typed)
  show "pp_logical_vocabulary pp_zf_eq_truth_operator"
    by (rule pp_zf_eq_truth_operator_logical)
qed simp

lemma pp_h_not_box_logical_operator_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_zf_neq_truth_operator
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_zf_neq_truth_operator : Prop \<rightarrow>\<^sub>o Prop"
    by (rule pp_zf_neq_truth_operator_typed)
  show "pp_logical_vocabulary pp_zf_neq_truth_operator"
    by (rule pp_zf_neq_truth_operator_logical)
qed simp

lemma pp_h_box_predicate_admissible:
  "pp_h_predicate_admissible Prop
    (\<lambda>w q. pp_h_eqv Prop w q (pp_zf_truth True))"
  using pp_h_identity_predicate_admissible[OF pp_h_truth_in_domain] .

lemma pp_h_not_box_predicate_admissible:
  "pp_h_predicate_admissible Prop
    (\<lambda>w q. \<not> pp_h_eqv Prop w q (pp_zf_truth True))"
  using pp_h_box_predicate_admissible
  unfolding pp_h_predicate_admissible_def by blast

lemma pp_h_diamond_box_predicate_admissible:
  "pp_h_predicate_admissible Prop
    (\<lambda>w q. \<exists>v \<ge> w.
      pp_h_eqv Prop v q (pp_zf_truth True))"
  unfolding pp_h_predicate_admissible_def
proof (intro allI impI)
  fix w x y u
  assume x: "Elem x (pp_h_domain Prop)"
    and y: "Elem y (pp_h_domain Prop)"
    and xy: "pp_h_eqv Prop w x y"
    and future: "w \<le> u"
  have xy_u: "pp_h_eqv Prop u x y"
    using pp_h_eqv_persistent[OF xy future] .
  show "(\<exists>v \<ge> u.
      pp_h_eqv Prop v x (pp_zf_truth True)) =
    (\<exists>v \<ge> u.
      pp_h_eqv Prop v y (pp_zf_truth True))"
  proof
    assume "\<exists>v \<ge> u.
        pp_h_eqv Prop v x (pp_zf_truth True)"
    then obtain v where uv: "u \<le> v"
      and x_true: "pp_h_eqv Prop v x (pp_zf_truth True)"
      by blast
    have xy_v: "pp_h_eqv Prop v x y"
      using pp_h_eqv_persistent[OF xy_u uv] .
    have yx_v: "pp_h_eqv Prop v y x"
      using pp_h_eqv_symmetric[
        OF x y xy_v] .
    have y_true:
        "pp_h_eqv Prop v y (pp_zf_truth True)"
      using pp_h_eqv_transitive[
        OF y x pp_h_truth_in_domain yx_v x_true] .
    show "\<exists>v \<ge> u.
        pp_h_eqv Prop v y (pp_zf_truth True)"
      using uv y_true by blast
  next
    assume "\<exists>v \<ge> u.
        pp_h_eqv Prop v y (pp_zf_truth True)"
    then obtain v where uv: "u \<le> v"
      and y_true: "pp_h_eqv Prop v y (pp_zf_truth True)"
      by blast
    have xy_v: "pp_h_eqv Prop v x y"
      using pp_h_eqv_persistent[OF xy_u uv] .
    have x_true:
        "pp_h_eqv Prop v x (pp_zf_truth True)"
      using pp_h_eqv_transitive[
        OF x y pp_h_truth_in_domain xy_v y_true] .
    show "\<exists>v \<ge> u.
        pp_h_eqv Prop v x (pp_zf_truth True)"
      using uv x_true by blast
  qed
qed

lemma pp_h_box_classifier_in_domain:
  "Elem pp_h_box_classifier
    (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_h_box_classifier_def
  by (rule pp_h_classifier_in_domain)
    (rule pp_h_box_predicate_admissible)

lemma pp_h_not_box_classifier_in_domain:
  "Elem pp_h_not_box_classifier
    (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_h_not_box_classifier_def
  by (rule pp_h_classifier_in_domain)
    (rule pp_h_not_box_predicate_admissible)

lemma pp_h_diamond_box_classifier_in_domain:
  "Elem pp_h_diamond_box_classifier
    (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_h_diamond_box_classifier_def
  by (rule pp_h_classifier_in_domain)
    (rule pp_h_diamond_box_predicate_admissible)

lemma pp_h_box_classifier_holds:
  assumes q: "Elem q (pp_h_domain Prop)"
  shows "pp_zf_holds (pp_h_box_classifier \<acute> q) w
    \<longleftrightarrow> pp_h_eqv Prop w q (pp_zf_truth True)"
  unfolding pp_h_box_classifier_def
  using pp_h_classifier_holds[OF q,
    of "\<lambda>w q. pp_h_eqv Prop w q (pp_zf_truth True)" w]
  by simp

lemma pp_h_not_box_classifier_holds:
  assumes q: "Elem q (pp_h_domain Prop)"
  shows "pp_zf_holds (pp_h_not_box_classifier \<acute> q) w
    \<longleftrightarrow> \<not> pp_h_eqv Prop w q (pp_zf_truth True)"
  unfolding pp_h_not_box_classifier_def
  using pp_h_classifier_holds[OF q,
    of "\<lambda>w q. \<not> pp_h_eqv Prop w q (pp_zf_truth True)" w]
  by simp

lemma pp_h_box_classifier_member:
  assumes q: "Elem q (pp_h_domain Prop)"
  shows "Elem (nat2Nat w) (pp_h_box_classifier \<acute> q)
    \<longleftrightarrow> pp_h_eqv Prop w q (pp_zf_truth True)"
  using pp_h_box_classifier_holds[OF q, of w]
  by (simp only: pp_zf_holds_def)

lemma pp_h_not_box_classifier_member:
  assumes q: "Elem q (pp_h_domain Prop)"
  shows "Elem (nat2Nat w) (pp_h_not_box_classifier \<acute> q)
    \<longleftrightarrow> \<not> pp_h_eqv Prop w q (pp_zf_truth True)"
  using pp_h_not_box_classifier_holds[OF q, of w]
  by (simp only: pp_zf_holds_def)

lemma pp_h_diamond_box_classifier_member:
  assumes q: "Elem q (pp_h_domain Prop)"
  shows "Elem (nat2Nat w) (pp_h_diamond_box_classifier \<acute> q)
    \<longleftrightarrow>
    (\<exists>v \<ge> w. pp_h_eqv Prop v q (pp_zf_truth True))"
  unfolding pp_h_diamond_box_classifier_def
  using pp_h_classifier_holds[OF q,
    of "\<lambda>w q. \<exists>v \<ge> w.
      pp_h_eqv Prop v q (pp_zf_truth True)" w]
  by (simp only: pp_zf_holds_def)

lemma pp_h_false_not_true:
  "\<not> pp_h_eqv Prop w (pp_zf_truth False) (pp_zf_truth True)"
proof
  assume eqv:
      "pp_h_eqv Prop w (pp_zf_truth False) (pp_zf_truth True)"
  have "Elem (nat2Nat w) (pp_zf_truth False) \<longleftrightarrow>
      Elem (nat2Nat w) (pp_zf_truth True)"
    using pp_h_prop_eqv_at[OF eqv, of w] by simp
  then show False
    by (simp add: pp_zf_truth_def Elem_nat2Nat_Nat)
qed

definition pp_h_unary_recombines_at ::
    "(nat \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> nat \<Rightarrow> bool"
  where
  "pp_h_unary_recombines_at Pure r w \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      Pure w X \<longrightarrow>
      ((\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> r)) \<longrightarrow>
        (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
          Elem (nat2Nat w) (X \<acute> q))))"

theorem pp_h_not_box_diamond_box_block_recombination:
  assumes p: "Elem p (pp_h_domain Prop)"
    and recombination: "pp_h_unary_recombines_at Pure p w"
    and not_box_pure: "Pure w pp_h_not_box_classifier"
    and diamond_box_pure: "Pure w pp_h_diamond_box_classifier"
  shows False
proof -
  have eventually_necessary:
      "\<exists>v \<ge> w. pp_h_eqv Prop v p (pp_zf_truth True)"
  proof (rule ccontr)
    assume no_future:
        "\<not> (\<exists>v \<ge> w.
          pp_h_eqv Prop v p (pp_zf_truth True))"
    have necessary_not_box:
        "\<forall>v \<ge> w.
          Elem (nat2Nat v) (pp_h_not_box_classifier \<acute> p)"
    proof (intro allI impI)
      fix v
      assume future: "w \<le> v"
      have not_true:
          "\<not> pp_h_eqv Prop v p (pp_zf_truth True)"
        using no_future future by blast
      show "Elem (nat2Nat v)
          (pp_h_not_box_classifier \<acute> p)"
        using pp_h_not_box_classifier_member[OF p, of v]
          not_true by blast
    qed
    have universal_not_box:
        "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
          Elem (nat2Nat w) (pp_h_not_box_classifier \<acute> q)"
      using recombination pp_h_not_box_classifier_in_domain
        not_box_pure necessary_not_box
      unfolding pp_h_unary_recombines_at_def by blast
    have true_not_box:
        "Elem (nat2Nat w)
          (pp_h_not_box_classifier \<acute> pp_zf_truth True)"
      using universal_not_box pp_h_truth_in_domain by blast
    have true_refl:
        "pp_h_eqv Prop w
          (pp_zf_truth True) (pp_zf_truth True)"
      using pp_h_eqv_reflexive[OF pp_h_truth_in_domain] .
    show False
      using pp_h_not_box_classifier_member[
        OF pp_h_truth_in_domain[of True], of w]
        true_not_box true_refl by blast
  qed
  then obtain v where future_v: "w \<le> v"
    and p_true_v:
      "pp_h_eqv Prop v p (pp_zf_truth True)"
    by blast
  have necessary_diamond_box:
      "\<forall>u \<ge> w.
        Elem (nat2Nat u) (pp_h_diamond_box_classifier \<acute> p)"
  proof (intro allI impI)
    fix u
    assume future_u: "w \<le> u"
    have eventually_from_u:
        "\<exists>z \<ge> u. pp_h_eqv Prop z p (pp_zf_truth True)"
    proof (cases "u \<le> v")
      case True
      then show ?thesis
        using p_true_v by blast
    next
      case False
      then have vu: "v \<le> u"
        by simp
      have p_true_u:
          "pp_h_eqv Prop u p (pp_zf_truth True)"
        using pp_h_eqv_persistent[OF p_true_v vu] .
      show ?thesis
        using p_true_u by blast
    qed
    show "Elem (nat2Nat u)
        (pp_h_diamond_box_classifier \<acute> p)"
      using pp_h_diamond_box_classifier_member[OF p, of u]
        eventually_from_u by blast
  qed
  have universal_diamond_box:
      "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
        Elem (nat2Nat w) (pp_h_diamond_box_classifier \<acute> q)"
    using recombination pp_h_diamond_box_classifier_in_domain
      diamond_box_pure necessary_diamond_box
    unfolding pp_h_unary_recombines_at_def by blast
  have false_diamond_box:
      "Elem (nat2Nat w)
        (pp_h_diamond_box_classifier \<acute> pp_zf_truth False)"
    using universal_diamond_box pp_h_truth_in_domain by blast
  have false_eventually_true:
      "\<exists>v \<ge> w.
        pp_h_eqv Prop v (pp_zf_truth False) (pp_zf_truth True)"
    using pp_h_diamond_box_classifier_member[
      OF pp_h_truth_in_domain[of False], of w]
      false_diamond_box by blast
  then show False
    using pp_h_false_not_true by blast
qed

theorem pp_h_box_complement_blocks_global_recombination:
  assumes r: "Elem r (pp_h_domain Prop)"
    and recombination:
      "\<And>w. pp_h_unary_recombines_at Pure r w"
    and box_pure: "\<And>w. Pure w pp_h_box_classifier"
    and not_box_pure: "\<And>w. Pure w pp_h_not_box_classifier"
  shows False
proof -
  have r_ne_true: "\<And>w. \<not> pp_h_eqv Prop w r (pp_zf_truth True)"
  proof -
    fix w
    show "\<not> pp_h_eqv Prop w r (pp_zf_truth True)"
    proof
      assume r_true: "pp_h_eqv Prop w r (pp_zf_truth True)"
      have necessary:
          "\<forall>v \<ge> w.
            Elem (nat2Nat v) (pp_h_box_classifier \<acute> r)"
      proof (intro allI impI)
        fix v
        assume future: "w \<le> v"
        have "pp_h_eqv Prop v r (pp_zf_truth True)"
          using pp_h_eqv_persistent[OF r_true future] .
        then show "Elem (nat2Nat v) (pp_h_box_classifier \<acute> r)"
          using pp_h_box_classifier_member[OF r, of v] by blast
      qed
      have universal:
          "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
            Elem (nat2Nat w) (pp_h_box_classifier \<acute> q)"
        using recombination[of w] pp_h_box_classifier_in_domain
          box_pure[of w] necessary
        unfolding pp_h_unary_recombines_at_def by blast
      have false_box:
          "Elem (nat2Nat w)
            (pp_h_box_classifier \<acute> pp_zf_truth False)"
        using universal pp_h_truth_in_domain by blast
      have "pp_h_eqv Prop w
          (pp_zf_truth False) (pp_zf_truth True)"
        using pp_h_box_classifier_holds[
          OF pp_h_truth_in_domain[of False], of w]
          pp_h_box_classifier_member[
            OF pp_h_truth_in_domain[of False], of w]
          false_box by blast
      then show False
        using pp_h_false_not_true by blast
    qed
  qed
  have necessary_not_box:
      "\<forall>v \<ge> 0.
        Elem (nat2Nat v) (pp_h_not_box_classifier \<acute> r)"
  proof (intro allI impI)
    fix v :: nat
    assume "0 \<le> v"
    show "Elem (nat2Nat v) (pp_h_not_box_classifier \<acute> r)"
      using pp_h_not_box_classifier_member[OF r, of v]
        r_ne_true[of v] by blast
  qed
  have universal_not_box:
      "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
        Elem (nat2Nat 0) (pp_h_not_box_classifier \<acute> q)"
    using recombination[of 0] pp_h_not_box_classifier_in_domain
      not_box_pure[of 0] necessary_not_box
    unfolding pp_h_unary_recombines_at_def by blast
  have true_not_box:
      "Elem (nat2Nat 0)
        (pp_h_not_box_classifier \<acute> pp_zf_truth True)"
    using universal_not_box pp_h_truth_in_domain by blast
  have true_refl:
      "pp_h_eqv Prop 0 (pp_zf_truth True) (pp_zf_truth True)"
    using pp_h_eqv_reflexive[OF pp_h_truth_in_domain] .
  show False
    using pp_h_not_box_classifier_member[
      OF pp_h_truth_in_domain[of True], of 0]
      true_not_box true_refl by blast
qed

lemma pp_h_eval_forall_Var2_app:
  "pp_zf_holds
      (pp_h_eval C (extend_env r (extend_env X \<rho>))
        (Forall Prop (App (Var 2) (Var 0)))) w
  \<longleftrightarrow>
    (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
      Elem (nat2Nat w) (X \<acute> q))"
  by (simp add: numeral_2_eq_2 pp_zf_holds_def Elem_nat2Nat_Nat)

context pp_h_internal_parameters
begin

lemma pp_h_gvalid_pure_closed:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and denotation:
      "pp_h_eval (pp_h_internal_constants Pure r)
        (pp_h_list_env []) M = x"
    and valid:
      "Constants.HHenkin.gvalid [] (pp_pure \<sigma> M)"
  shows "Pure \<sigma> w x"
proof -
  have env: "pp_h_env_typed [] (pp_h_list_env [])"
    by (simp add: pp_h_env_typed_def lookup_def)
  have holds:
      "pp_zf_holds
        (pp_h_eval (pp_h_internal_constants Pure r)
          (pp_h_list_env []) (pp_pure \<sigma> M)) w"
  proof -
    have "pp_zf_holds
        (Constants.pp_h_den (pp_pure \<sigma> M) []) w"
      using Constants.HHenkin.gvalidD[OF valid] by simp
    then show ?thesis
      by (simp add: Constants.pp_h_den_def)
  qed
  have iff:
      "pp_zf_holds
        (pp_h_eval (pp_h_internal_constants Pure r)
          (pp_h_list_env []) (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
        Pure \<sigma> w
          (pp_h_eval (pp_h_internal_constants Pure r)
            (pp_h_list_env []) M)"
    using pp_h_eval_pure_holds[OF typed env, of w] .
  show ?thesis
    using holds iff denotation by blast
qed

lemma pp_h_gvalid_unary_recombination_implies_semantic:
  assumes valid:
      "Constants.HHenkin.gvalid [] pp_unary_recombination"
  shows "pp_h_unary_recombines_at
    (Pure (Prop \<rightarrow>\<^sub>o Prop)) r w"
proof -
  show ?thesis
    unfolding pp_h_unary_recombines_at_def
  proof (rule allI)
  fix X
  show "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      Pure (Prop \<rightarrow>\<^sub>o Prop) w X \<longrightarrow>
      (\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> r)) \<longrightarrow>
      (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
        Elem (nat2Nat w) (X \<acute> q))"
  proof (intro impI)
  assume X: "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and pure_X: "Pure (Prop \<rightarrow>\<^sub>o Prop) w X"
    and necessary: "\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> r)"
  let ?C = "pp_h_internal_constants Pure r"
  let ?\<rho>0 = "pp_h_list_env []"
  let ?\<rho>X = "extend_env X ?\<rho>0"
  let ?\<rho>r = "extend_env r ?\<rho>X"
  have env0: "pp_h_env_typed [] ?\<rho>0"
    by (simp add: pp_h_env_typed_def lookup_def)
  have envX:
      "pp_h_env_typed [Prop \<rightarrow>\<^sub>o Prop] ?\<rho>X"
    using pp_h_env_typed_extend[OF env0 X] .
  have envr:
      "pp_h_env_typed [Prop, Prop \<rightarrow>\<^sub>o Prop] ?\<rho>r"
    using pp_h_env_typed_extend[OF envX r_typed] .
  have closed:
      "pp_zf_holds (pp_h_eval ?C ?\<rho>0 pp_unary_recombination) w"
  proof -
    have "pp_zf_holds
        (Constants.pp_h_den pp_unary_recombination []) w"
      using Constants.HHenkin.gvalidD[OF valid] by simp
    then show ?thesis
      by (simp add: Constants.pp_h_den_def)
  qed
  let ?body =
      "Imp
        (Conj
          (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
          (pp_fun Prop (Var 0)))
        (Imp
          (\<box>\<^sub>o (App (Var 1) (Var 0)))
          (Forall Prop (App (Var 2) (Var 0))))"
  have at_X:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>X (Forall Prop ?body)) w"
    using closed X
    unfolding pp_unary_recombination_def
    by (simp only: pp_h_eval_Forall_holds) blast
  have at_r:
      "pp_zf_holds (pp_h_eval ?C ?\<rho>r ?body) w"
    using at_X r_typed
    by (simp only: pp_h_eval_Forall_holds)
  have var1_type:
      "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile>
        Var 1 : Prop \<rightarrow>\<^sub>o Prop"
    by simp
  have var0_type:
      "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile> Var 0 : Prop"
    by simp
  have pure_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))) w"
    using pp_h_eval_pure_holds[OF var1_type envr, of w]
      pure_X by simp
  have fun_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r (pp_fun Prop (Var 0))) w"
  proof -
    have rr: "pp_h_eqv Prop w r r"
      using pp_h_eqv_reflexive[OF r_typed] .
    show ?thesis
      using pp_h_eval_fun_holds[OF var0_type envr, of w] rr by simp
  qed
  have premise:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))) w"
    using pure_holds fun_holds
    by (simp only: pp_h_eval_Conj_holds)
  have implication:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (Imp
            (\<box>\<^sub>o (App (Var 1) (Var 0)))
            (Forall Prop (App (Var 2) (Var 0))))) w"
    using at_r premise
    by (simp only: pp_h_eval_Imp_holds) blast
  have app_typed: "Elem (X \<acute> r) (pp_h_domain Prop)"
    using pp_h_app_closed[OF X r_typed] .
  have box_relation:
      "pp_h_eqv Prop w (X \<acute> r) (pp_zf_truth True)"
    using necessary
    by (simp add: pp_zf_truth_def Elem_nat2Nat_Nat)
  have box_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (\<box>\<^sub>o (App (Var 1) (Var 0)))) w"
    unfolding ObjBox_def
    using box_relation pp_h_eval_ObjTrue[of ?C ?\<rho>r]
    by simp
  show "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
      Elem (nat2Nat w) (X \<acute> q)"
    by (metis implication box_holds pp_h_eval_Imp_holds
      pp_h_eval_forall_Var2_app[of ?C r X ?\<rho>0 w])
  qed
  qed
qed

theorem pp_h_internal_frame_not_central_stock:
  "\<not> Constants.HHenkin.gvalid_set pp_recombination_PP_axioms"
proof
  assume stock:
      "Constants.HHenkin.gvalid_set pp_recombination_PP_axioms"
  have box_member:
      "pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_zf_eq_truth_operator
        \<in> pp_recombination_PP_axioms"
    using pp_h_box_logical_operator_purity_axiom
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  have not_box_member:
      "pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_zf_neq_truth_operator
        \<in> pp_recombination_PP_axioms"
    using pp_h_not_box_logical_operator_purity_axiom
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  have recombination_member:
      "pp_unary_recombination \<in> pp_recombination_PP_axioms"
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def by blast
  have box_valid:
      "Constants.HHenkin.gvalid []
        (pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_zf_eq_truth_operator)"
    using stock box_member
    unfolding Constants.HHenkin.gvalid_set_def by blast
  have not_box_valid:
      "Constants.HHenkin.gvalid []
        (pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_zf_neq_truth_operator)"
    using stock not_box_member
    unfolding Constants.HHenkin.gvalid_set_def by blast
  have recombination_valid:
      "Constants.HHenkin.gvalid [] pp_unary_recombination"
    using stock recombination_member
    unfolding Constants.HHenkin.gvalid_set_def by blast
  have box_pure:
      "\<And>w. Pure (Prop \<rightarrow>\<^sub>o Prop) w pp_h_box_classifier"
    using pp_h_gvalid_pure_closed[
      OF pp_zf_eq_truth_operator_typed
        pp_h_eval_box_logical_operator box_valid] .
  have not_box_pure:
      "\<And>w. Pure (Prop \<rightarrow>\<^sub>o Prop) w
        pp_h_not_box_classifier"
    using pp_h_gvalid_pure_closed[
      OF pp_zf_neq_truth_operator_typed
        pp_h_eval_not_box_logical_operator not_box_valid] .
  have recombines:
      "\<And>w. pp_h_unary_recombines_at
        (Pure (Prop \<rightarrow>\<^sub>o Prop)) r w"
    using pp_h_gvalid_unary_recombination_implies_semantic[
      OF recombination_valid] .
  show False
    using r_typed recombines box_pure not_box_pure
    by (rule pp_h_box_complement_blocks_global_recombination)
qed

end

section \<open>A moving fundamental proposition\<close>

text \<open>
  The preceding obstruction uses one fixed representative \<open>r\<close> for the
  fundamental proposition at every world.  Unique fundamentality itself is
  local and does not impose that restriction.  The proposition that is false
  exactly through world \<open>w\<close> is contingent at \<open>w\<close> but necessary at
  \<open>Suc w\<close>.  It therefore makes both antecedents used by the box/complement
  obstruction fail.
\<close>

definition pp_h_moving_seed :: "nat \<Rightarrow> ZF" where
  "pp_h_moving_seed w = pp_zf_prop (\<lambda>z. w < Nat2nat z)"

lemma pp_h_moving_seed_in_domain:
  "Elem (pp_h_moving_seed w) (pp_h_domain Prop)"
  unfolding pp_h_moving_seed_def
  by (rule pp_h_prop_in_domain)

lemma pp_h_moving_seed_false_now:
  "\<not> pp_h_eqv Prop w (pp_h_moving_seed w) (pp_zf_truth True)"
proof
  assume eqv:
      "pp_h_eqv Prop w (pp_h_moving_seed w) (pp_zf_truth True)"
  have at_w:
      "Elem (nat2Nat w) (pp_h_moving_seed w) \<longleftrightarrow>
        Elem (nat2Nat w) (pp_zf_truth True)"
    using pp_h_prop_eqv_at[OF eqv, of w] by simp
  show False
    using at_w
    by (simp add: pp_h_moving_seed_def pp_zf_truth_def
        Elem_nat2Nat_Nat)
qed

lemma pp_h_moving_seed_true_next:
  "pp_h_eqv Prop (Suc w) (pp_h_moving_seed w) (pp_zf_truth True)"
  unfolding pp_h_moving_seed_def pp_zf_truth_def
    pp_h_prop_eqv_pp_zf_prop_iff
  by simp

fun pp_h_moving_fundamental_at ::
    "otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_h_moving_fundamental_at Ind w x = False"
| "pp_h_moving_fundamental_at Prop w x =
    pp_h_eqv Prop w x (pp_h_moving_seed w)"
| "pp_h_moving_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x = False"

lemma pp_h_moving_fundamental_admissible:
  "pp_h_predicate_admissible \<sigma> (pp_h_moving_fundamental_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_h_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_h_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_h_domain Prop)"
      and y: "Elem y (pp_h_domain Prop)"
      and xy: "pp_h_eqv Prop w x y"
      and future: "w \<le> v"
    have xy_v: "pp_h_eqv Prop v x y"
      using pp_h_eqv_persistent[OF xy future] .
    have seed_refl:
        "pp_h_eqv Prop v
          (pp_h_moving_seed v) (pp_h_moving_seed v)"
      using pp_h_eqv_reflexive[OF pp_h_moving_seed_in_domain] .
    show "pp_h_moving_fundamental_at Prop v x =
        pp_h_moving_fundamental_at Prop v y"
      using pp_h_eqv_congruence[
        OF x y pp_h_moving_seed_in_domain pp_h_moving_seed_in_domain
          xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_h_predicate_admissible_def)
qed

lemma pp_h_moving_box_antecedent_fails:
  assumes p: "Elem p (pp_h_domain Prop)"
    and fundamental: "pp_h_moving_fundamental_at Prop w p"
  shows "\<not> (\<forall>v \<ge> w.
    Elem (nat2Nat v) (pp_h_box_classifier \<acute> p))"
proof
  assume necessary:
      "\<forall>v \<ge> w. Elem (nat2Nat v) (pp_h_box_classifier \<acute> p)"
  have p_true: "pp_h_eqv Prop w p (pp_zf_truth True)"
    using necessary pp_h_box_classifier_member[OF p, of w] by blast
  have p_seed: "pp_h_eqv Prop w p (pp_h_moving_seed w)"
    using fundamental by simp
  have seed_p:
      "pp_h_eqv Prop w (pp_h_moving_seed w) p"
    using pp_h_eqv_symmetric[
      OF p pp_h_moving_seed_in_domain p_seed] .
  have seed_true:
      "pp_h_eqv Prop w (pp_h_moving_seed w) (pp_zf_truth True)"
    using pp_h_eqv_transitive[
      OF pp_h_moving_seed_in_domain p pp_h_truth_in_domain
        seed_p p_true] .
  show False
    using pp_h_moving_seed_false_now seed_true by blast
qed

lemma pp_h_moving_not_box_antecedent_fails:
  assumes p: "Elem p (pp_h_domain Prop)"
    and fundamental: "pp_h_moving_fundamental_at Prop w p"
  shows "\<not> (\<forall>v \<ge> w.
    Elem (nat2Nat v) (pp_h_not_box_classifier \<acute> p))"
proof
  assume necessary:
      "\<forall>v \<ge> w.
        Elem (nat2Nat v) (pp_h_not_box_classifier \<acute> p)"
  have not_true:
      "\<not> pp_h_eqv Prop (Suc w) p (pp_zf_truth True)"
  proof -
    have member:
        "Elem (nat2Nat (Suc w)) (pp_h_not_box_classifier \<acute> p)"
    proof -
      have future: "w \<le> Suc w"
        by simp
      show ?thesis
        using necessary[rule_format, OF future] .
    qed
    have iff:
        "Elem (nat2Nat (Suc w)) (pp_h_not_box_classifier \<acute> p)
          \<longleftrightarrow>
        \<not> pp_h_eqv Prop (Suc w) p (pp_zf_truth True)"
      by (rule pp_h_not_box_classifier_member[OF p])
    show ?thesis
      using iff member by (rule iffD1)
  qed
  have p_seed_w:
      "pp_h_eqv Prop w p (pp_h_moving_seed w)"
    using fundamental by simp
  have p_seed_next:
      "pp_h_eqv Prop (Suc w) p (pp_h_moving_seed w)"
  proof -
    have future: "w \<le> Suc w"
      by simp
    show ?thesis
      using pp_h_eqv_persistent[OF p_seed_w future] .
  qed
  have p_true_next:
      "pp_h_eqv Prop (Suc w) p (pp_zf_truth True)"
    using pp_h_eqv_transitive[
      OF p pp_h_moving_seed_in_domain pp_h_truth_in_domain
        p_seed_next pp_h_moving_seed_true_next] .
  show False
    using not_true p_true_next by blast
qed

lemma pp_h_moving_box_recombination_instances:
  assumes X:
      "X = pp_h_box_classifier \<or> X = pp_h_not_box_classifier"
    and p: "Elem p (pp_h_domain Prop)"
    and fundamental: "pp_h_moving_fundamental_at Prop w p"
  shows "((\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> p)) \<longrightarrow>
    (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
      Elem (nat2Nat w) (X \<acute> q)))"
proof
  assume necessary:
      "\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> p)"
  consider (box) "X = pp_h_box_classifier"
    | (not_box) "X = pp_h_not_box_classifier"
    using X by blast
  then show "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
      Elem (nat2Nat w) (X \<acute> q)"
  proof cases
    case box
    then show ?thesis
      using necessary pp_h_moving_box_antecedent_fails[OF p fundamental]
      by blast
  next
    case not_box
    then show ?thesis
      using necessary
        pp_h_moving_not_box_antecedent_fails[OF p fundamental]
      by blast
  qed
qed

definition pp_h_box_pair_pure ::
    "otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_h_box_pair_pure \<sigma> w X \<longleftrightarrow>
    \<sigma> = (Prop \<rightarrow>\<^sub>o Prop) \<and>
    (pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) w X pp_h_box_classifier \<or>
     pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) w X
       pp_h_not_box_classifier)"

lemma pp_h_box_pair_pure_admissible:
  "pp_h_predicate_admissible \<sigma> (pp_h_box_pair_pure \<sigma>)"
  unfolding pp_h_predicate_admissible_def
proof (intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_h_domain \<sigma>)"
    and y: "Elem y (pp_h_domain \<sigma>)"
    and xy: "pp_h_eqv \<sigma> w x y"
    and future: "w \<le> v"
  show "pp_h_box_pair_pure \<sigma> v x =
      pp_h_box_pair_pure \<sigma> v y"
  proof (cases "\<sigma> = (Prop \<rightarrow>\<^sub>o Prop)")
    case False
    then show ?thesis
      by (simp add: pp_h_box_pair_pure_def)
  next
    case True
    have x_typed:
        "Elem x (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
      using x True by simp
    have y_typed:
        "Elem y (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
      using y True by simp
    have xy_v:
        "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v x y"
      using pp_h_eqv_persistent[OF xy future] True by simp
    have box_refl:
        "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          pp_h_box_classifier pp_h_box_classifier"
      using pp_h_eqv_reflexive[OF pp_h_box_classifier_in_domain] .
    have not_box_refl:
        "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          pp_h_not_box_classifier pp_h_not_box_classifier"
      using pp_h_eqv_reflexive[
        OF pp_h_not_box_classifier_in_domain] .
    have box_iff:
        "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          x pp_h_box_classifier
        \<longleftrightarrow>
        pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          y pp_h_box_classifier"
      using pp_h_eqv_congruence[
        OF x_typed y_typed pp_h_box_classifier_in_domain
          pp_h_box_classifier_in_domain xy_v box_refl] .
    have not_box_iff:
        "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          x pp_h_not_box_classifier
        \<longleftrightarrow>
        pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) v
          y pp_h_not_box_classifier"
      using pp_h_eqv_congruence[
        OF x_typed y_typed pp_h_not_box_classifier_in_domain
          pp_h_not_box_classifier_in_domain xy_v not_box_refl] .
    show ?thesis
      using True box_iff not_box_iff
      by (simp add: pp_h_box_pair_pure_def)
  qed
qed

lemma pp_h_box_pair_pure_contains_box:
  "pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop) w
    pp_h_box_classifier"
  unfolding pp_h_box_pair_pure_def
  using pp_h_eqv_reflexive[OF pp_h_box_classifier_in_domain]
  by blast

lemma pp_h_box_pair_pure_contains_not_box:
  "pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop) w
    pp_h_not_box_classifier"
  unfolding pp_h_box_pair_pure_def
  using pp_h_eqv_reflexive[OF pp_h_not_box_classifier_in_domain]
  by blast

lemma pp_h_eqv_operator_member_transfer:
  assumes X: "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and Y: "Elem Y (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and p: "Elem p (pp_h_domain Prop)"
    and XY: "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) w X Y"
    and future: "w \<le> v"
  shows "Elem (nat2Nat v) (X \<acute> p)
    \<longleftrightarrow> Elem (nat2Nat v) (Y \<acute> p)"
proof -
  have pp: "pp_h_eqv Prop v p p"
    using pp_h_eqv_reflexive[OF p] .
  have apps: "pp_h_eqv Prop v (X \<acute> p) (Y \<acute> p)"
    using XY future p p pp by auto
  show ?thesis
    using pp_h_prop_eqv_at[OF apps, of v] by simp
qed

theorem pp_h_moving_box_pair_recombines:
  "\<And>w. pp_h_unary_recombines_at
    (pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop))
    (pp_h_moving_seed w) w"
proof -
  fix w
  show "pp_h_unary_recombines_at
      (pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop))
      (pp_h_moving_seed w) w"
    unfolding pp_h_unary_recombines_at_def
  proof (rule allI)
    fix X
    show "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
        pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop) w X \<longrightarrow>
        (\<forall>v \<ge> w.
          Elem (nat2Nat v) (X \<acute> pp_h_moving_seed w)) \<longrightarrow>
        (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
          Elem (nat2Nat w) (X \<acute> q))"
    proof (intro impI)
      assume X_typed:
          "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
        and X_pure:
          "pp_h_box_pair_pure (Prop \<rightarrow>\<^sub>o Prop) w X"
        and necessary:
          "\<forall>v \<ge> w.
            Elem (nat2Nat v) (X \<acute> pp_h_moving_seed w)"
      have seed_fundamental:
          "pp_h_moving_fundamental_at Prop w
            (pp_h_moving_seed w)"
        using pp_h_eqv_reflexive[OF pp_h_moving_seed_in_domain]
        by simp
      consider (box)
          "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) w
            X pp_h_box_classifier"
        | (not_box)
          "pp_h_eqv (Prop \<rightarrow>\<^sub>o Prop) w
            X pp_h_not_box_classifier"
        using X_pure
        by (auto simp: pp_h_box_pair_pure_def)
      then show "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
          Elem (nat2Nat w) (X \<acute> q)"
      proof cases
        case box
        have box_necessary:
            "\<forall>v \<ge> w.
              Elem (nat2Nat v)
                (pp_h_box_classifier \<acute> pp_h_moving_seed w)"
        proof (intro allI impI)
          fix v
          assume future: "w \<le> v"
          have transfer:
              "Elem (nat2Nat v) (X \<acute> pp_h_moving_seed w)
              \<longleftrightarrow>
              Elem (nat2Nat v)
                (pp_h_box_classifier \<acute> pp_h_moving_seed w)"
            using pp_h_eqv_operator_member_transfer[
              OF X_typed pp_h_box_classifier_in_domain
                pp_h_moving_seed_in_domain box future] .
          show "Elem (nat2Nat v)
              (pp_h_box_classifier \<acute> pp_h_moving_seed w)"
            using necessary future transfer by blast
        qed
        show ?thesis
          using pp_h_moving_box_antecedent_fails[
            OF pp_h_moving_seed_in_domain seed_fundamental]
            box_necessary
          by blast
      next
        case not_box
        have not_box_necessary:
            "\<forall>v \<ge> w.
              Elem (nat2Nat v)
                (pp_h_not_box_classifier \<acute> pp_h_moving_seed w)"
        proof (intro allI impI)
          fix v
          assume future: "w \<le> v"
          have transfer:
              "Elem (nat2Nat v) (X \<acute> pp_h_moving_seed w)
              \<longleftrightarrow>
              Elem (nat2Nat v)
                (pp_h_not_box_classifier \<acute> pp_h_moving_seed w)"
            using pp_h_eqv_operator_member_transfer[
              OF X_typed pp_h_not_box_classifier_in_domain
                pp_h_moving_seed_in_domain not_box future] .
          show "Elem (nat2Nat v)
              (pp_h_not_box_classifier \<acute> pp_h_moving_seed w)"
            using necessary future transfer by blast
        qed
        show ?thesis
          using pp_h_moving_not_box_antecedent_fails[
            OF pp_h_moving_seed_in_domain seed_fundamental]
            not_box_necessary
          by blast
      qed
    qed
  qed
qed

fun pp_h_moving_internal_constants ::
    "(otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_h_moving_internal_constants Pure c Ind = pp_h_default Ind"
| "pp_h_moving_internal_constants Pure c Prop = pp_h_default Prop"
| "pp_h_moving_internal_constants Pure c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_h_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_h_classifier \<sigma> (pp_h_moving_fundamental_at \<sigma>)
     else pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

locale pp_h_moving_internal_parameters =
  fixes Pure :: "otype \<Rightarrow> nat \<Rightarrow> ZF \<Rightarrow> bool"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_h_predicate_admissible \<sigma> (Pure \<sigma>)"
begin

lemma pp_h_moving_internal_constants_typed:
  "Elem (pp_h_moving_internal_constants Pure c \<sigma>)
    (pp_h_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_h_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_h_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem (pp_h_classifier \<sigma> (Pure \<sigma>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_h_classifier_in_domain[OF Pure_admissible] .
  have fun_classifier:
      "Elem
        (pp_h_classifier \<sigma> (pp_h_moving_fundamental_at \<sigma>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_h_classifier_in_domain[
      OF pp_h_moving_fundamental_admissible] .
  have default:
      "Elem (pp_h_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_h_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_h_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

sublocale MovingConstants:
  pp_h_constants "pp_h_moving_internal_constants Pure"
  by standard (rule pp_h_moving_internal_constants_typed)

lemma pp_h_moving_eval_Pure[simp]:
  "pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> (pp_Pure \<sigma>) =
    pp_h_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_h_moving_eval_Fun[simp]:
  "pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> (pp_Fun \<sigma>) =
    pp_h_classifier \<sigma> (pp_h_moving_fundamental_at \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_h_moving_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_zf_holds
      (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      Pure \<sigma> w
        (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> M)
        (pp_h_domain \<sigma>)"
    using MovingConstants.pp_h_eval_type[OF typed env]
    by (simp add: pp_h_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_h_classifier_holds[OF argument, of "Pure \<sigma>" w]
    by simp
qed

lemma pp_h_moving_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_h_env_typed \<Gamma> \<rho>"
  shows "pp_zf_holds
      (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_h_moving_fundamental_at \<sigma> w
        (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho> M)
        (pp_h_domain \<sigma>)"
    using MovingConstants.pp_h_eval_type[OF typed env]
    by (simp add: pp_h_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_h_classifier_holds[
      OF argument, of "pp_h_moving_fundamental_at \<sigma>" w]
    by simp
qed

lemma pp_h_moving_unique_fundamental_holds:
  "pp_zf_holds
    (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_h_moving_seed w"
  have base: "pp_h_env_typed [] \<rho>"
    by (simp add: pp_h_env_typed_def lookup_def)
  have r_env:
      "pp_h_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_h_env_typed_extend[
      OF base pp_h_moving_seed_in_domain] .
  have r_is_fundamental:
      "pp_zf_holds
        (pp_h_eval (pp_h_moving_internal_constants Pure)
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_h_eqv Prop w ?r ?r"
      using pp_h_eqv_reflexive[OF pp_h_moving_seed_in_domain] .
    show ?thesis
      using pp_h_moving_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_h_domain Prop) \<longrightarrow>
        pp_zf_holds
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_h_domain Prop)"
    have yr_env:
        "pp_h_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_h_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_h_eqv Prop w y ?r"
      using pp_h_moving_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_h_eqv Prop w y ?r"
      by simp
    show "pp_zf_holds
        (pp_h_eval (pp_h_moving_internal_constants Pure)
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_h_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_h_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_h_moving_seed_in_domain r_is_fundamental uniqueness
    by (simp only: pp_h_eval_Conj_holds pp_h_eval_Forall_holds)
qed

lemma pp_h_moving_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_zf_holds
    (pp_h_eval (pp_h_moving_internal_constants Pure) \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_h_env_typed [] \<rho>"
    by (simp add: pp_h_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_h_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_h_domain \<sigma>)"
    have extended:
        "pp_h_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_h_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_h_moving_fundamental_at \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_zf_holds
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_h_moving_fundamental_at \<sigma> w x"
      using pp_h_moving_eval_fun_holds[
        OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_zf_holds
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_zf_holds
        (pp_h_eval (pp_h_moving_internal_constants Pure)
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_h_eval_Neg_holds[
        of "pp_h_moving_internal_constants Pure" "extend_env x \<rho>"
          "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_h_moving_unique_fundamental_gvalid:
  "MovingConstants.HHenkin.gvalid []
    (pp_unique_fundamental Prop)"
  unfolding MovingConstants.HHenkin.gvalid_def
    MovingConstants.pp_h_den_def
  using pp_h_moving_unique_fundamental_holds by blast

theorem pp_h_moving_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "MovingConstants.HHenkin.gvalid []
    (pp_no_fundamentals \<sigma>)"
  unfolding MovingConstants.HHenkin.gvalid_def
    MovingConstants.pp_h_den_def
  using pp_h_moving_no_fundamentals_holds[OF assms] by blast

lemma pp_h_moving_gvalid_unary_recombination_implies_semantic:
  assumes valid:
      "MovingConstants.HHenkin.gvalid [] pp_unary_recombination"
    and r_typed: "Elem r (pp_h_domain Prop)"
    and fundamental: "pp_h_moving_fundamental_at Prop w r"
  shows "pp_h_unary_recombines_at
    (Pure (Prop \<rightarrow>\<^sub>o Prop)) r w"
proof -
  show ?thesis
    unfolding pp_h_unary_recombines_at_def
  proof (rule allI)
  fix X
  show "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      Pure (Prop \<rightarrow>\<^sub>o Prop) w X \<longrightarrow>
      (\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> r)) \<longrightarrow>
      (\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
        Elem (nat2Nat w) (X \<acute> q))"
  proof (intro impI)
  assume X: "Elem X (pp_h_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and pure_X: "Pure (Prop \<rightarrow>\<^sub>o Prop) w X"
    and necessary: "\<forall>v \<ge> w. Elem (nat2Nat v) (X \<acute> r)"
  let ?C = "pp_h_moving_internal_constants Pure"
  let ?\<rho>0 = "pp_h_list_env []"
  let ?\<rho>X = "extend_env X ?\<rho>0"
  let ?\<rho>r = "extend_env r ?\<rho>X"
  have env0: "pp_h_env_typed [] ?\<rho>0"
    by (simp add: pp_h_env_typed_def lookup_def)
  have envX:
      "pp_h_env_typed [Prop \<rightarrow>\<^sub>o Prop] ?\<rho>X"
    using pp_h_env_typed_extend[OF env0 X] .
  have envr:
      "pp_h_env_typed [Prop, Prop \<rightarrow>\<^sub>o Prop] ?\<rho>r"
    using pp_h_env_typed_extend[OF envX r_typed] .
  have closed:
      "pp_zf_holds (pp_h_eval ?C ?\<rho>0 pp_unary_recombination) w"
  proof -
    have "pp_zf_holds
        (MovingConstants.pp_h_den pp_unary_recombination []) w"
      using MovingConstants.HHenkin.gvalidD[OF valid] by simp
    then show ?thesis
      by (simp add: MovingConstants.pp_h_den_def)
  qed
  let ?body =
      "Imp
        (Conj
          (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
          (pp_fun Prop (Var 0)))
        (Imp
          (\<box>\<^sub>o (App (Var 1) (Var 0)))
          (Forall Prop (App (Var 2) (Var 0))))"
  have at_X:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>X (Forall Prop ?body)) w"
    using closed X
    unfolding pp_unary_recombination_def
    by (simp only: pp_h_eval_Forall_holds) blast
  have at_r:
      "pp_zf_holds (pp_h_eval ?C ?\<rho>r ?body) w"
    using at_X r_typed
    by (simp only: pp_h_eval_Forall_holds)
  have var1_type:
      "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile>
        Var 1 : Prop \<rightarrow>\<^sub>o Prop"
    by simp
  have var0_type:
      "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile> Var 0 : Prop"
    by simp
  have pure_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))) w"
    using pp_h_moving_eval_pure_holds[OF var1_type envr, of w]
      pure_X by simp
  have fun_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r (pp_fun Prop (Var 0))) w"
  proof -
    have rr: "pp_h_eqv Prop w r r"
      using pp_h_eqv_reflexive[OF r_typed] .
    show ?thesis
      using pp_h_moving_eval_fun_holds[OF var0_type envr, of w] fundamental by simp
  qed
  have premise:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))) w"
    using pure_holds fun_holds
    by (simp only: pp_h_eval_Conj_holds)
  have implication:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (Imp
            (\<box>\<^sub>o (App (Var 1) (Var 0)))
            (Forall Prop (App (Var 2) (Var 0))))) w"
    using at_r premise
    by (simp only: pp_h_eval_Imp_holds) blast
  have app_typed: "Elem (X \<acute> r) (pp_h_domain Prop)"
    using pp_h_app_closed[OF X r_typed] .
  have box_relation:
      "pp_h_eqv Prop w (X \<acute> r) (pp_zf_truth True)"
    using necessary
    by (simp add: pp_zf_truth_def Elem_nat2Nat_Nat)
  have box_holds:
      "pp_zf_holds
        (pp_h_eval ?C ?\<rho>r
          (\<box>\<^sub>o (App (Var 1) (Var 0)))) w"
    unfolding ObjBox_def
    using box_relation pp_h_eval_ObjTrue[of ?C ?\<rho>r]
    by simp
  show "\<forall>q. Elem q (pp_h_domain Prop) \<longrightarrow>
      Elem (nat2Nat w) (X \<acute> q)"
    by (metis implication box_holds pp_h_eval_Imp_holds
      pp_h_eval_forall_Var2_app[of ?C r X ?\<rho>0 w])
  qed
  qed
qed
lemma pp_h_moving_gvalid_pure_closed:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and denotation:
      "pp_h_eval (pp_h_moving_internal_constants Pure)
        (pp_h_list_env []) M = x"
    and valid:
      "MovingConstants.HHenkin.gvalid [] (pp_pure \<sigma> M)"
  shows "Pure \<sigma> w x"
proof -
  have env: "pp_h_env_typed [] (pp_h_list_env [])"
    by (simp add: pp_h_env_typed_def lookup_def)
  have holds:
      "pp_zf_holds
        (pp_h_eval (pp_h_moving_internal_constants Pure)
          (pp_h_list_env []) (pp_pure \<sigma> M)) w"
  proof -
    have "pp_zf_holds
        (MovingConstants.pp_h_den (pp_pure \<sigma> M) []) w"
      using MovingConstants.HHenkin.gvalidD[OF valid] by simp
    then show ?thesis
      by (simp add: MovingConstants.pp_h_den_def)
  qed
  have iff:
      "pp_zf_holds
        (pp_h_eval (pp_h_moving_internal_constants Pure)
          (pp_h_list_env []) (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
        Pure \<sigma> w
          (pp_h_eval (pp_h_moving_internal_constants Pure)
            (pp_h_list_env []) M)"
    using pp_h_moving_eval_pure_holds[OF typed env, of w] .
  show ?thesis
    using holds iff denotation by blast
qed

theorem pp_h_moving_internal_frame_not_central_stock:
  "\<not> MovingConstants.HHenkin.gvalid_set
    pp_recombination_PP_axioms"
proof
  assume stock:
      "MovingConstants.HHenkin.gvalid_set
        pp_recombination_PP_axioms"
  have not_box_member:
      "pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_zf_neq_truth_operator
        \<in> pp_recombination_PP_axioms"
    using pp_h_not_box_logical_operator_purity_axiom
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  have diamond_box_member:
      "pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_h_diamond_box_logical_operator
        \<in> pp_recombination_PP_axioms"
    using pp_h_diamond_box_logical_operator_purity_axiom
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  have recombination_member:
      "pp_unary_recombination \<in> pp_recombination_PP_axioms"
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def by blast
  have not_box_valid:
      "MovingConstants.HHenkin.gvalid []
        (pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_zf_neq_truth_operator)"
    using stock not_box_member
    unfolding MovingConstants.HHenkin.gvalid_set_def by blast
  have diamond_box_valid:
      "MovingConstants.HHenkin.gvalid []
        (pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_h_diamond_box_logical_operator)"
    using stock diamond_box_member
    unfolding MovingConstants.HHenkin.gvalid_set_def by blast
  have recombination_valid:
      "MovingConstants.HHenkin.gvalid [] pp_unary_recombination"
    using stock recombination_member
    unfolding MovingConstants.HHenkin.gvalid_set_def by blast
  have not_box_pure:
      "Pure (Prop \<rightarrow>\<^sub>o Prop) 0
        pp_h_not_box_classifier"
    using pp_h_moving_gvalid_pure_closed[
      OF pp_zf_neq_truth_operator_typed
        pp_h_eval_not_box_logical_operator not_box_valid] .
  have diamond_box_pure:
      "Pure (Prop \<rightarrow>\<^sub>o Prop) 0
        pp_h_diamond_box_classifier"
    using pp_h_moving_gvalid_pure_closed[
      OF pp_h_diamond_box_logical_operator_typed
        pp_h_eval_diamond_box_logical_operator diamond_box_valid] .
  have seed_fundamental:
      "pp_h_moving_fundamental_at Prop 0
        (pp_h_moving_seed 0)"
    using pp_h_eqv_reflexive[OF pp_h_moving_seed_in_domain]
    by simp
  have recombines:
      "pp_h_unary_recombines_at
        (Pure (Prop \<rightarrow>\<^sub>o Prop))
        (pp_h_moving_seed 0) 0"
    using pp_h_moving_gvalid_unary_recombination_implies_semantic[
      OF recombination_valid pp_h_moving_seed_in_domain
        seed_fundamental] .
  show False
    using pp_h_not_box_diamond_box_block_recombination[
      OF pp_h_moving_seed_in_domain recombines
        not_box_pure diamond_box_pure] .
qed


end

interpretation MovingBoxPair:
  pp_h_moving_internal_parameters pp_h_box_pair_pure
  by standard (rule pp_h_box_pair_pure_admissible)


text \<open>
  The evaluator is ordinary recursion on \<open>oterm\<close>.  Its quantifier clauses
  range over the already constructed sets, and its equality clause merely
  packages the preconstructed relation as a proposition.
  The combined theorem \<open>pp_h_eval_fundamental\<close> proves type preservation
  and relational invariance simultaneously.  In particular, its lambda case
  proves both that every body value has the target type and that the body
  respects related arguments, which puts each lambda denotation into the
  restricted arrow domain without a closure evaluator.
  The resulting locale interpretation
  \<open>DefaultHConstants.HHenkin\<close> is a concrete
  \<open>henkin_action_model\<close> over the hyperintensional frame.
  The locale \<open>pp_h_internal_parameters\<close> then replaces the default
  interpretations of \<open>Pure\<close> and \<open>Fun\<close> by admissible world-indexed
  classifiers.  In particular, \<open>Fun\<close> at proposition type expresses local
  identity with the selected fundamental proposition \<open>r\<close>; at all other
  types it is empty.  The interpretation already validates unique
  fundamentality at \<open>Prop\<close> and the no-fundamentals schema at every other
  type.

  The fixed-representative interpretation cannot validate the central stock.
  If its selected proposition ever becomes identical with truth, the box
  classifier violates Recombination there; if it never does, the complement
  classifier violates Recombination at the root.  This excludes only a
  globally fixed representative, not unique fundamentality as such.

  The moving interpretation uses
  \<open>pp_h_moving_seed w = {v. w < v}\<close>.  Its fundamental proposition is
  contingent at \<open>w\<close> and necessary from \<open>Suc w\<close> onward.  The associated
  classifier is admissible, and its Henkin interpretation validates unique
  fundamentality at proposition type and no fundamentality at every other
  type.  Moreover, \<open>pp_h_box_pair_pure\<close> is an admissible purity fragment
  containing the box and not-box operators up to local identity, and
  \<open>pp_h_moving_box_pair_recombines\<close> proves unary Recombination for the
  whole fragment.  Thus the moving seed genuinely avoids the original
  box/complement obstruction.

  It does not, however, survive the full logical-purity schema.  The closed
  logical operator \<open>\<lambda>q. \<diamond>\<box>q\<close> denotes
  \<open>pp_h_diamond_box_classifier\<close>.  At any world and for any proposed
  fundamental proposition \<open>p\<close>, purity of \<open>\<lambda>q. \<not>\<box>q\<close> plus
  Recombination first forces \<open>\<diamond>\<box>p\<close>.  Directedness and
  persistence of the natural-number tail then make
  \<open>\<diamond>\<box>p\<close> necessary.
  Recombination applied to the pure operator \<open>\<lambda>q. \<diamond>\<box>q\<close>
  would consequently make \<open>\<diamond>\<box>q\<close> hold for every proposition,
  including falsity.  The theorem
  \<open>pp_h_not_box_diamond_box_block_recombination\<close> proves this semantic
  obstruction, and \<open>pp_h_moving_internal_frame_not_central_stock\<close> connects
  it to the literal object-language purity and Recombination axioms.

  Hence no admissible interpretation of \<open>Pure\<close> repairs the present
  natural-number-tail model.  This is a frame-level exclusion, not a
  contradiction in Goodman's central stock.  The abstract theorem
  \<open>pp_directed_frame_not_box_diamond_box_obstruction\<close> isolates the
  decisive frame property: every pair of accessible futures has a common
  successor.  The binary prefix frame is a checked genuinely nonconvergent
  replacement.  At every node \<open>w\<close>, \<open>pp_tree_seed w\<close> is true exactly
  in the subtree rooted at \<open>w @ [True]\<close>.  It is necessary on that branch,
  while no stabilization is possible on the incomparable false branch.
  Consequently
  \<open>pp_tree_local_seed_escapes_directed_obstruction\<close> proves that both
  problematic Recombination antecedents fail at \<open>w\<close>.  The remaining
  construction task is to lift this frame and seed into the preconstructed
  HOL-ZF domains and structural evaluator.
\<close>

end
