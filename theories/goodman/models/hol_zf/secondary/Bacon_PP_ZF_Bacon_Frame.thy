theory Bacon_PP_ZF_Bacon_Frame
  imports Bacon_PP_ZF_Hyper_Frame
    Higher_Order_Metaphysics_PP_ZF_Model.Bacon_PP_ZF_Word_Propositions
begin

section \<open>Natural-number-word worlds inside the HOL-ZF proposition domain\<close>

text \<open>
  The semantic worlds are finite natural-number words ordered by prefix.  Object
  propositions remain elements of \<open>Power Nat\<close>, so we fix a bijection
  between natural-number words and natural numbers and use its ZF numeral as the
  membership coordinate of a world.  The bijection is total in both
  directions; no unused or duplicated proposition coordinates remain.
\<close>

section \<open>Preconstructed branching domains and logical relation\<close>

fun pp_n_domain :: "otype \<Rightarrow> ZF"
and pp_n_eqv ::
  "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_n_domain Ind = Nat"
| "pp_n_domain Prop = Power Nat"
| "pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Sep (Fun (pp_n_domain \<sigma>) (pp_n_domain \<tau>))
      (\<lambda>f. \<forall>w x y.
        Elem x (pp_n_domain \<sigma>) \<longrightarrow>
        Elem y (pp_n_domain \<sigma>) \<longrightarrow>
        pp_n_eqv \<sigma> w x y \<longrightarrow>
        pp_n_eqv \<tau> w (f \<acute> x) (f \<acute> y))"
| "pp_n_eqv Ind w x y = (x = y)"
| "pp_n_eqv Prop w P Q =
    (\<forall>v. prefix w v \<longrightarrow>
      (pp_n_holds P v \<longleftrightarrow> pp_n_holds Q v))"
| "pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g =
    (\<forall>v. prefix w v \<longrightarrow> (\<forall>x y.
      Elem x (pp_n_domain \<sigma>) \<longrightarrow>
      Elem y (pp_n_domain \<sigma>) \<longrightarrow>
      pp_n_eqv \<sigma> v x y \<longrightarrow>
      pp_n_eqv \<tau> v (f \<acute> x) (g \<acute> y)))"

lemma pp_n_prop_eqv_refl:
  "pp_n_eqv Prop w P P"
  by simp

lemma pp_n_prop_eqv_symmetric:
  "pp_n_eqv Prop w P Q \<Longrightarrow> pp_n_eqv Prop w Q P"
  by auto

lemma pp_n_prop_eqv_transitive:
  "pp_n_eqv Prop w P Q \<Longrightarrow>
    pp_n_eqv Prop w Q R \<Longrightarrow>
    pp_n_eqv Prop w P R"
  by auto

lemma pp_n_prop_eqv_persistent:
  assumes eqv: "pp_n_eqv Prop w P Q"
    and future: "prefix w v"
  shows "pp_n_eqv Prop v P Q"
  using eqv future prefix_order.trans by auto

lemma pp_n_prop_eqv_truth_iff:
  "pp_n_eqv Prop w P (pp_zf_truth True) \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> pp_n_holds P v)"
  by simp

lemma pp_n_arrow_member_function:
  assumes "Elem f (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Elem f (Fun (pp_n_domain \<sigma>) (pp_n_domain \<tau>))"
  using assms by (simp add: Sep)

lemma pp_n_arrow_member_respects:
  assumes f: "Elem f (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
  shows "pp_n_eqv \<tau> w (f \<acute> x) (f \<acute> y)"
  using f x y xy by (auto simp: Sep)

lemma pp_n_app_closed:
  assumes f: "Elem f (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_n_domain \<sigma>)"
  shows "Elem (f \<acute> x) (pp_n_domain \<tau>)"
proof -
  have f_fun: "Elem f (Fun (pp_n_domain \<sigma>) (pp_n_domain \<tau>))"
    using pp_n_arrow_member_function[OF f] .
  have is_fun: "isFun f"
    using pp_zf_function_isFun[OF f_fun] .
  have domain: "Domain f = pp_n_domain \<sigma>"
    using pp_zf_function_domain[OF f_fun] .
  have in_range: "Elem (f \<acute> x) (Range f)"
    using fun_value_in_range[OF is_fun] x domain by simp
  have range_subset: "subset (Range f) (pp_n_domain \<tau>)"
    using Fun_Range[OF f_fun] .
  show ?thesis
    using in_range range_subset by (auto simp: subset_def)
qed

lemma pp_n_eqv_persistent:
  assumes eqv: "pp_n_eqv \<sigma> w x y"
    and future: "prefix w v"
  shows "pp_n_eqv \<sigma> v x y"
  using eqv future
proof (induction \<sigma> arbitrary: w v x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    using prefix_order.trans by auto
next
  case (Arr \<sigma> \<tau>)
  then show ?case
    using prefix_order.trans by auto
qed

subsection \<open>Nonempty domains\<close>

fun pp_n_default :: "otype \<Rightarrow> ZF" where
  "pp_n_default Ind = Empty"
| "pp_n_default Prop = Empty"
| "pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Lambda (pp_n_domain \<sigma>) (\<lambda>_. pp_n_default \<tau>)"

lemma pp_n_default_in_domain_and_reflexive:
  "Elem (pp_n_default \<sigma>) (pp_n_domain \<sigma>) \<and>
    (\<forall>w. pp_n_eqv \<sigma> w
      (pp_n_default \<sigma>) (pp_n_default \<sigma>))"
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
  have target:
      "Elem (pp_n_default \<tau>) (pp_n_domain \<tau>)"
    using Arr.IH(2) by blast
  have target_refl:
      "\<And>w. pp_n_eqv \<tau> w
        (pp_n_default \<tau>) (pp_n_default \<tau>)"
    using Arr.IH(2) by blast
  have function_member:
      "Elem
        (Lambda (pp_n_domain \<sigma>) (\<lambda>_. pp_n_default \<tau>))
        (Fun (pp_n_domain \<sigma>) (pp_n_domain \<tau>))"
    by (simp add: Elem_Lambda_Fun target)
  have respects:
      "\<forall>w x y.
        Elem x (pp_n_domain \<sigma>) \<longrightarrow>
        Elem y (pp_n_domain \<sigma>) \<longrightarrow>
        pp_n_eqv \<sigma> w x y \<longrightarrow>
        pp_n_eqv \<tau> w
          ((Lambda (pp_n_domain \<sigma>) (\<lambda>_. pp_n_default \<tau>)) \<acute> x)
          ((Lambda (pp_n_domain \<sigma>) (\<lambda>_. pp_n_default \<tau>)) \<acute> y)"
    using target_refl
    by (auto simp: Lambda_app)
  have member:
      "Elem (pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using function_member respects by (simp add: Sep)
  have reflexive:
      "\<And>w. pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
        (pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using target_refl
    by (auto simp: Lambda_app)
  show ?case
    using member reflexive by blast
qed

lemma pp_n_default_in_domain:
  "Elem (pp_n_default \<sigma>) (pp_n_domain \<sigma>)"
  using pp_n_default_in_domain_and_reflexive by blast

theorem pp_n_domain_nonempty:
  "\<exists>x. Elem x (pp_n_domain \<sigma>)"
  using pp_n_default_in_domain by blast

subsection \<open>Equivalence laws\<close>

lemma pp_n_eqv_reflexive:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
  shows "pp_n_eqv \<sigma> w x x"
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

lemma pp_n_eqv_symmetric:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
  shows "pp_n_eqv \<sigma> w y x"
  using x y xy
proof (induction \<sigma> arbitrary: w x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by auto
next
  case (Arr \<sigma> \<tau>)
  have x_fun: "Elem x (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have y_fun: "Elem y (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  show ?case
    unfolding pp_n_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "prefix w v"
      and a: "Elem a (pp_n_domain \<sigma>)"
      and b: "Elem b (pp_n_domain \<sigma>)"
      and ab: "pp_n_eqv \<sigma> v a b"
    have ba: "pp_n_eqv \<sigma> v b a"
      using Arr.IH(1)[OF a b ab] .
    have old:
        "pp_n_eqv \<tau> v (x \<acute> b) (y \<acute> a)"
      using Arr.prems(3) future b a ba by auto
    have xb: "Elem (x \<acute> b) (pp_n_domain \<tau>)"
      using pp_n_app_closed[OF x_fun b] .
    have ya: "Elem (y \<acute> a) (pp_n_domain \<tau>)"
      using pp_n_app_closed[OF y_fun a] .
    show "pp_n_eqv \<tau> v (y \<acute> a) (x \<acute> b)"
      using Arr.IH(2)[OF xb ya old] .
  qed
qed

lemma pp_n_eqv_transitive:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and z: "Elem z (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
    and yz: "pp_n_eqv \<sigma> w y z"
  shows "pp_n_eqv \<sigma> w x z"
  using x y z xy yz
proof (induction \<sigma> arbitrary: w x y z)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by auto
next
  case (Arr \<sigma> \<tau>)
  have x_fun: "Elem x (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(1) .
  have y_fun: "Elem y (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(2) .
  have z_fun: "Elem z (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Arr.prems(3) .
  show ?case
    unfolding pp_n_eqv.simps
  proof (intro allI impI)
    fix v a b
    assume future: "prefix w v"
      and a: "Elem a (pp_n_domain \<sigma>)"
      and b: "Elem b (pp_n_domain \<sigma>)"
      and ab: "pp_n_eqv \<sigma> v a b"
    have yy: "pp_n_eqv \<sigma> v b b"
      using pp_n_eqv_reflexive[OF b] .
    have first: "pp_n_eqv \<tau> v (x \<acute> a) (y \<acute> b)"
      using Arr.prems(4) future a b ab by auto
    have second: "pp_n_eqv \<tau> v (y \<acute> b) (z \<acute> b)"
      using Arr.prems(5) future b b yy by auto
    have xa: "Elem (x \<acute> a) (pp_n_domain \<tau>)"
      using pp_n_app_closed[OF x_fun a] .
    have yb: "Elem (y \<acute> b) (pp_n_domain \<tau>)"
      using pp_n_app_closed[OF y_fun b] .
    have zb: "Elem (z \<acute> b) (pp_n_domain \<tau>)"
      using pp_n_app_closed[OF z_fun b] .
    show "pp_n_eqv \<tau> v (x \<acute> a) (z \<acute> b)"
      using Arr.IH(2)[OF xa yb zb first second] .
  qed
qed

section \<open>Structural denotation on the branching frame\<close>

fun pp_n_eval ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> oterm \<Rightarrow> ZF" where
  "pp_n_eval C \<rho> (Var n) = \<rho> n"
| "pp_n_eval C \<rho> (Const c \<sigma>) = C c \<sigma>"
| "pp_n_eval C \<rho> (App M N) =
    (pp_n_eval C \<rho> M) \<acute> (pp_n_eval C \<rho> N)"
| "pp_n_eval C \<rho> (Lam \<sigma> M) =
    Lambda (pp_n_domain \<sigma>)
      (\<lambda>x. pp_n_eval C (extend_env x \<rho>) M)"
| "pp_n_eval C \<rho> (Eq \<sigma> M N) =
    pp_n_prop (\<lambda>w.
      pp_n_eqv \<sigma> w (pp_n_eval C \<rho> M) (pp_n_eval C \<rho> N))"
| "pp_n_eval C \<rho> (Neg A) =
    pp_n_prop (\<lambda>w. \<not> pp_n_holds (pp_n_eval C \<rho> A) w)"
| "pp_n_eval C \<rho> (Conj A B) =
    pp_n_prop (\<lambda>w.
      pp_n_holds (pp_n_eval C \<rho> A) w \<and>
      pp_n_holds (pp_n_eval C \<rho> B) w)"
| "pp_n_eval C \<rho> (Disj A B) =
    pp_n_prop (\<lambda>w.
      pp_n_holds (pp_n_eval C \<rho> A) w \<or>
      pp_n_holds (pp_n_eval C \<rho> B) w)"
| "pp_n_eval C \<rho> (Imp A B) =
    pp_n_prop (\<lambda>w.
      pp_n_holds (pp_n_eval C \<rho> A) w \<longrightarrow>
      pp_n_holds (pp_n_eval C \<rho> B) w)"
| "pp_n_eval C \<rho> (Forall \<sigma> A) =
    pp_n_prop (\<lambda>w.
      \<forall>x. Elem x (pp_n_domain \<sigma>) \<longrightarrow>
        pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) w)"
| "pp_n_eval C \<rho> (Exists \<sigma> A) =
    pp_n_prop (\<lambda>w.
      \<exists>x. Elem x (pp_n_domain \<sigma>) \<and>
        pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) w)"

lemma pp_n_eval_Eq_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Eq \<sigma> M N)) w \<longleftrightarrow>
    pp_n_eqv \<sigma> w (pp_n_eval C \<rho> M) (pp_n_eval C \<rho> N)"
  by simp

lemma pp_n_eval_Neg_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Neg A)) w \<longleftrightarrow>
    \<not> pp_n_holds (pp_n_eval C \<rho> A) w"
  by simp

lemma pp_n_eval_Conj_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Conj A B)) w \<longleftrightarrow>
    pp_n_holds (pp_n_eval C \<rho> A) w \<and>
    pp_n_holds (pp_n_eval C \<rho> B) w"
  by simp

lemma pp_n_eval_Disj_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Disj A B)) w \<longleftrightarrow>
    pp_n_holds (pp_n_eval C \<rho> A) w \<or>
    pp_n_holds (pp_n_eval C \<rho> B) w"
  by simp

lemma pp_n_eval_Imp_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Imp A B)) w \<longleftrightarrow>
    (pp_n_holds (pp_n_eval C \<rho> A) w \<longrightarrow>
      pp_n_holds (pp_n_eval C \<rho> B) w)"
  by simp

lemma pp_n_eval_Forall_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Forall \<sigma> A)) w \<longleftrightarrow>
    (\<forall>x. Elem x (pp_n_domain \<sigma>) \<longrightarrow>
      pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) w)"
  by simp

lemma pp_n_eval_Exists_holds[simp]:
  "pp_n_holds (pp_n_eval C \<rho> (Exists \<sigma> A)) w \<longleftrightarrow>
    (\<exists>x. Elem x (pp_n_domain \<sigma>) \<and>
      pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) w)"
  by simp

definition pp_n_env_typed ::
    "ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_n_env_typed \<Gamma> \<rho> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      Elem (\<rho> n) (pp_n_domain \<sigma>))"

definition pp_n_env_eqv ::
    "nat list \<Rightarrow> ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longleftrightarrow>
    pp_n_env_typed \<Gamma> \<rho> \<and>
    pp_n_env_typed \<Gamma> \<eta> \<and>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      pp_n_eqv \<sigma> w (\<rho> n) (\<eta> n))"

lemma pp_n_env_typed_lookup:
  assumes env: "pp_n_env_typed \<Gamma> \<rho>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "Elem (\<rho> n) (pp_n_domain \<sigma>)"
  using env lookup unfolding pp_n_env_typed_def by blast

lemma pp_n_env_typed_extend:
  assumes env: "pp_n_env_typed \<Gamma> \<rho>"
    and x: "Elem x (pp_n_domain \<sigma>)"
  shows "pp_n_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
proof (unfold pp_n_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "Elem (extend_env x \<rho> n) (pp_n_domain \<tau>)"
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
    then have "Elem (\<rho> m) (pp_n_domain \<tau>)"
      using pp_n_env_typed_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_n_env_eqv_typed_left:
  "pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_n_env_typed \<Gamma> \<rho>"
  unfolding pp_n_env_eqv_def by blast

lemma pp_n_env_eqv_typed_right:
  "pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_n_env_typed \<Gamma> \<eta>"
  unfolding pp_n_env_eqv_def by blast

lemma pp_n_env_eqv_lookup:
  assumes env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_n_eqv \<sigma> w (\<rho> n) (\<eta> n)"
  using env lookup unfolding pp_n_env_eqv_def by blast

lemma pp_n_env_eqv_refl:
  assumes env: "pp_n_env_typed \<Gamma> \<rho>"
  shows "pp_n_env_eqv w \<Gamma> \<rho> \<rho>"
proof (unfold pp_n_env_eqv_def, intro conjI allI impI)
  show "pp_n_env_typed \<Gamma> \<rho>"
    using env .
  show "pp_n_env_typed \<Gamma> \<rho>"
    using env .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "Elem (\<rho> n) (pp_n_domain \<sigma>)"
    using pp_n_env_typed_lookup[OF env lookup] .
  then show "pp_n_eqv \<sigma> w (\<rho> n) (\<rho> n)"
    by (rule pp_n_eqv_reflexive)
qed

lemma pp_n_env_eqv_persistent:
  assumes env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
    and future: "prefix w v"
  shows "pp_n_env_eqv v \<Gamma> \<rho> \<eta>"
proof (unfold pp_n_env_eqv_def, intro conjI allI impI)
  show "pp_n_env_typed \<Gamma> \<rho>"
    using pp_n_env_eqv_typed_left[OF env] .
  show "pp_n_env_typed \<Gamma> \<eta>"
    using pp_n_env_eqv_typed_right[OF env] .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "pp_n_eqv \<sigma> w (\<rho> n) (\<eta> n)"
    using pp_n_env_eqv_lookup[OF env lookup] .
  then show "pp_n_eqv \<sigma> v (\<rho> n) (\<eta> n)"
    using future by (rule pp_n_eqv_persistent)
qed

lemma pp_n_env_eqv_extend:
  assumes env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
    and x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
  shows "pp_n_env_eqv w (\<sigma> # \<Gamma>)
    (extend_env x \<rho>) (extend_env y \<eta>)"
proof (unfold pp_n_env_eqv_def, intro conjI allI impI)
  show "pp_n_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
    using pp_n_env_typed_extend[OF pp_n_env_eqv_typed_left[OF env] x] .
  show "pp_n_env_typed (\<sigma> # \<Gamma>) (extend_env y \<eta>)"
    using pp_n_env_typed_extend[OF pp_n_env_eqv_typed_right[OF env] y] .
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "pp_n_eqv \<tau> w
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
    then have "pp_n_eqv \<tau> w (\<rho> m) (\<eta> m)"
      using pp_n_env_eqv_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_n_app_respects:
  assumes fg: "pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
    and x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
  shows "pp_n_eqv \<tau> w (f \<acute> x) (g \<acute> y)"
  using fg x y xy by auto

lemma pp_n_lambda_closed:
  assumes typed:
      "\<And>x. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
        Elem (F x) (pp_n_domain \<tau>)"
    and respects:
      "\<And>w x y. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_n_domain \<sigma>) \<Longrightarrow>
        pp_n_eqv \<sigma> w x y \<Longrightarrow>
        pp_n_eqv \<tau> w (F x) (F y)"
  shows "Elem (Lambda (pp_n_domain \<sigma>) F)
    (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
proof -
  have function_member:
      "Elem (Lambda (pp_n_domain \<sigma>) F)
        (Fun (pp_n_domain \<sigma>) (pp_n_domain \<tau>))"
    using typed by (simp add: Elem_Lambda_Fun)
  have relation_respecting:
      "\<forall>w x y.
        Elem x (pp_n_domain \<sigma>) \<longrightarrow>
        Elem y (pp_n_domain \<sigma>) \<longrightarrow>
        pp_n_eqv \<sigma> w x y \<longrightarrow>
        pp_n_eqv \<tau> w
          ((Lambda (pp_n_domain \<sigma>) F) \<acute> x)
          ((Lambda (pp_n_domain \<sigma>) F) \<acute> y)"
    using respects by (auto simp: Lambda_app)
  show ?thesis
    using function_member relation_respecting by (simp add: Sep)
qed

lemma pp_n_eqv_congruence:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
    and x': "Elem x' (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and y': "Elem y' (pp_n_domain \<sigma>)"
    and xx': "pp_n_eqv \<sigma> w x x'"
    and yy': "pp_n_eqv \<sigma> w y y'"
  shows "pp_n_eqv \<sigma> w x y \<longleftrightarrow>
    pp_n_eqv \<sigma> w x' y'"
proof
  assume xy: "pp_n_eqv \<sigma> w x y"
  have x'x: "pp_n_eqv \<sigma> w x' x"
    using pp_n_eqv_symmetric[OF x x' xx'] .
  have x'y: "pp_n_eqv \<sigma> w x' y"
    using pp_n_eqv_transitive[OF x' x y x'x xy] .
  show "pp_n_eqv \<sigma> w x' y'"
    using pp_n_eqv_transitive[OF x' y y' x'y yy'] .
next
  assume x'y': "pp_n_eqv \<sigma> w x' y'"
  have y'y: "pp_n_eqv \<sigma> w y' y"
    using pp_n_eqv_symmetric[OF y y' yy'] .
  have xy': "pp_n_eqv \<sigma> w x y'"
    using pp_n_eqv_transitive[OF x x' y' xx' x'y'] .
  show "pp_n_eqv \<sigma> w x y"
    using pp_n_eqv_transitive[OF x y' y xy' y'y] .
qed

lemma pp_n_prop_eqv_pp_n_prop_iff:
  "pp_n_eqv Prop w (pp_n_prop P) (pp_n_prop Q) \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> (P v \<longleftrightarrow> Q v))"
  by simp

lemma pp_n_prop_in_domain:
  "Elem (pp_n_prop P) (pp_n_domain Prop)"
  using pp_n_prop_in_power by simp

lemma pp_n_prop_eqv_at:
  assumes PQ: "pp_n_eqv Prop w P Q"
    and future: "prefix w v"
  shows "pp_n_holds P v \<longleftrightarrow> pp_n_holds Q v"
  using PQ future by simp

definition pp_n_dom :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_n_dom \<sigma> x \<longleftrightarrow> Elem x (pp_n_domain \<sigma>)"

lemma pp_n_eval_rename:
  "pp_n_eval C \<rho> (rename r M) =
    pp_n_eval C (\<lambda>n. \<rho> (r n)) M"
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

lemma pp_n_eval_shift:
  "pp_n_eval C (extend_env x \<rho>) (shift M) = pp_n_eval C \<rho> M"
  unfolding shift_def
  using pp_n_eval_rename[of C "extend_env x \<rho>" Suc M]
  by simp

definition pp_n_list_env :: "ZF list \<Rightarrow> nat \<Rightarrow> ZF" where
  "pp_n_list_env env = nth_default Empty env"

lemma pp_n_list_env_Cons:
  "pp_n_list_env (x # env) = extend_env x (pp_n_list_env env)"
  by (rule ext, rename_tac n, case_tac n)
    (simp_all add: pp_n_list_env_def nth_default_def)

lemma env_ok_implies_pp_n_env_typed:
  assumes env: "env_ok (map pp_n_dom \<Gamma>) xs"
  shows "pp_n_env_typed \<Gamma> (pp_n_list_env xs)"
proof (unfold pp_n_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  then have n_lt: "n < length \<Gamma>" and nth: "\<Gamma> ! n = \<sigma>"
    by (auto simp: lookup_def split: if_splits)
  from env have len: "length xs = length \<Gamma>"
    and entries:
      "\<forall>k<length \<Gamma>. pp_n_dom (\<Gamma> ! k) (xs ! k)"
    by (auto simp: env_ok_def)
  have env_n: "pp_n_list_env xs n = xs ! n"
    using n_lt len
    by (simp add: pp_n_list_env_def nth_default_nth)
  have typed_n: "pp_n_dom (\<Gamma> ! n) (xs ! n)"
    using entries n_lt by blast
  show "Elem (pp_n_list_env xs n) (pp_n_domain \<sigma>)"
    using env_n typed_n nth by (simp add: pp_n_dom_def)
qed

locale pp_n_constants =
  fixes C :: "string \<Rightarrow> otype \<Rightarrow> ZF"
  assumes C_typed: "Elem (C c \<sigma>) (pp_n_domain \<sigma>)"
begin

theorem pp_n_eval_fundamental:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
  shows
    "(\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> M) (pp_n_domain \<tau>)) \<and>
     (\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv \<tau> w (pp_n_eval C \<rho> M) (pp_n_eval C \<eta> M))"
  using typed
proof (induction rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Var n)) (pp_n_domain \<tau>)"
      using Var.hyps pp_n_env_typed_lookup by simp
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv \<tau> w
          (pp_n_eval C \<rho> (Var n)) (pp_n_eval C \<eta> (Var n))"
      using Var.hyps pp_n_env_eqv_lookup by simp
  qed
next
  case (Const \<Gamma> c \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Const c \<tau>)) (pp_n_domain \<tau>)"
      using C_typed by simp
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv \<tau> w
          (pp_n_eval C \<rho> (Const c \<tau>))
          (pp_n_eval C \<eta> (Const c \<tau>))"
      using C_typed pp_n_eqv_reflexive by simp
  qed
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (App M N)) (pp_n_domain \<tau>)"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_n_env_typed \<Gamma> \<rho>"
      have function_member:
          "Elem (pp_n_eval C \<rho> M)
            (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using App.IH(1) env by blast
      have argument:
          "Elem (pp_n_eval C \<rho> N) (pp_n_domain \<sigma>)"
        using App.IH(2) env by blast
      show "Elem (pp_n_eval C \<rho> (App M N)) (pp_n_domain \<tau>)"
        using pp_n_app_closed[OF function_member argument] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv \<tau> w
          (pp_n_eval C \<rho> (App M N)) (pp_n_eval C \<eta> (App M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      have functions_related:
          "pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_n_eval C \<rho> M) (pp_n_eval C \<eta> M)"
        using App.IH(1) env by blast
      have left_argument:
          "Elem (pp_n_eval C \<rho> N) (pp_n_domain \<sigma>)"
        using App.IH(2) pp_n_env_eqv_typed_left[OF env] by blast
      have right_argument:
          "Elem (pp_n_eval C \<eta> N) (pp_n_domain \<sigma>)"
        using App.IH(2) pp_n_env_eqv_typed_right[OF env] by blast
      have arguments:
          "pp_n_eqv \<sigma> w
            (pp_n_eval C \<rho> N) (pp_n_eval C \<eta> N)"
        using App.IH(2) env by blast
      show "pp_n_eqv \<tau> w
          (pp_n_eval C \<rho> (App M N)) (pp_n_eval C \<eta> (App M N))"
        using pp_n_app_respects[
          OF functions_related left_argument right_argument arguments]
        by simp
    qed
  qed
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Lam \<sigma> M))
          (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_n_env_typed \<Gamma> \<rho>"
      have body_typed:
          "\<And>x. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
            Elem (pp_n_eval C (extend_env x \<rho>) M)
              (pp_n_domain \<tau>)"
      proof -
        fix x
        assume x: "Elem x (pp_n_domain \<sigma>)"
        have extended:
            "pp_n_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
          using pp_n_env_typed_extend[OF env x] .
        show "Elem (pp_n_eval C (extend_env x \<rho>) M)
            (pp_n_domain \<tau>)"
          using Lam.IH extended by blast
      qed
      have body_respects:
          "\<And>w x y. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
            Elem y (pp_n_domain \<sigma>) \<Longrightarrow>
            pp_n_eqv \<sigma> w x y \<Longrightarrow>
            pp_n_eqv \<tau> w
              (pp_n_eval C (extend_env x \<rho>) M)
              (pp_n_eval C (extend_env y \<rho>) M)"
      proof -
        fix w x y
        assume x: "Elem x (pp_n_domain \<sigma>)"
          and y: "Elem y (pp_n_domain \<sigma>)"
          and xy: "pp_n_eqv \<sigma> w x y"
        have base: "pp_n_env_eqv w \<Gamma> \<rho> \<rho>"
          using pp_n_env_eqv_refl[OF env] .
        have extended:
            "pp_n_env_eqv w (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<rho>)"
          using pp_n_env_eqv_extend[OF base x y xy] .
        show "pp_n_eqv \<tau> w
            (pp_n_eval C (extend_env x \<rho>) M)
            (pp_n_eval C (extend_env y \<rho>) M)"
          using Lam.IH extended by blast
      qed
      show "Elem (pp_n_eval C \<rho> (Lam \<sigma> M))
          (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using pp_n_lambda_closed[OF body_typed body_respects] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_n_eval C \<rho> (Lam \<sigma> M))
          (pp_n_eval C \<eta> (Lam \<sigma> M))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_n_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_n_eval C \<rho> (Lam \<sigma> M))
          (pp_n_eval C \<eta> (Lam \<sigma> M))"
        unfolding pp_n_eval.simps pp_n_eqv.simps
      proof (intro allI impI)
        fix v x y
        assume future: "prefix w v"
          and x: "Elem x (pp_n_domain \<sigma>)"
          and y: "Elem y (pp_n_domain \<sigma>)"
          and xy: "pp_n_eqv \<sigma> v x y"
        have base: "pp_n_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_n_env_eqv_persistent[OF env future] .
        have extended:
            "pp_n_env_eqv v (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<eta>)"
          using pp_n_env_eqv_extend[OF base x y xy] .
        have body:
            "pp_n_eqv \<tau> v
              (pp_n_eval C (extend_env x \<rho>) M)
              (pp_n_eval C (extend_env y \<eta>) M)"
          using Lam.IH extended by blast
        show "pp_n_eqv \<tau> v
            ((Lambda (pp_n_domain \<sigma>)
              (\<lambda>x. pp_n_eval C (extend_env x \<rho>) M)) \<acute> x)
            ((Lambda (pp_n_domain \<sigma>)
              (\<lambda>x. pp_n_eval C (extend_env x \<eta>) M)) \<acute> y)"
          using body x y by (simp add: Lambda_app)
      qed
    qed
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Eq \<sigma> M N)) (pp_n_domain Prop)"
    proof (intro allI impI)
      fix \<rho>
      assume "pp_n_env_typed \<Gamma> \<rho>"
      show "Elem (pp_n_eval C \<rho> (Eq \<sigma> M N)) (pp_n_domain Prop)"
        unfolding pp_n_eval.simps
        by (rule pp_n_prop_in_domain)
    qed
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Eq \<sigma> M N))
          (pp_n_eval C \<eta> (Eq \<sigma> M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Eq \<sigma> M N))
          (pp_n_eval C \<eta> (Eq \<sigma> M N))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have env_v: "pp_n_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_n_env_eqv_persistent[OF env future] .
        have M_left:
            "Elem (pp_n_eval C \<rho> M) (pp_n_domain \<sigma>)"
          using Eq.IH(1) pp_n_env_eqv_typed_left[OF env] by blast
        have M_right:
            "Elem (pp_n_eval C \<eta> M) (pp_n_domain \<sigma>)"
          using Eq.IH(1) pp_n_env_eqv_typed_right[OF env] by blast
        have N_left:
            "Elem (pp_n_eval C \<rho> N) (pp_n_domain \<sigma>)"
          using Eq.IH(2) pp_n_env_eqv_typed_left[OF env] by blast
        have N_right:
            "Elem (pp_n_eval C \<eta> N) (pp_n_domain \<sigma>)"
          using Eq.IH(2) pp_n_env_eqv_typed_right[OF env] by blast
        have M_related:
            "pp_n_eqv \<sigma> v
              (pp_n_eval C \<rho> M) (pp_n_eval C \<eta> M)"
          using Eq.IH(1) env_v by blast
        have N_related:
            "pp_n_eqv \<sigma> v
              (pp_n_eval C \<rho> N) (pp_n_eval C \<eta> N)"
          using Eq.IH(2) env_v by blast
        show "pp_n_eqv \<sigma> (v)
              (pp_n_eval C \<rho> M) (pp_n_eval C \<rho> N) =
            pp_n_eqv \<sigma> (v)
              (pp_n_eval C \<eta> M) (pp_n_eval C \<eta> N)"
          using pp_n_eqv_congruence[
            OF M_left M_right N_left N_right M_related N_related]
          by simp
      qed
    qed
  qed
next
  case (Neg \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Neg A)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Neg A)) (pp_n_eval C \<eta> (Neg A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      have related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> A) (pp_n_eval C \<eta> A)"
        using Neg.IH env by blast
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Neg A)) (pp_n_eval C \<eta> (Neg A))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
        using pp_n_prop_eqv_at[OF related] by blast
    qed
  qed
next
  case (Conj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Conj A B)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Conj A B))
          (pp_n_eval C \<eta> (Conj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> A) (pp_n_eval C \<eta> A)"
        using Conj.IH(1) env by blast
      have B_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> B) (pp_n_eval C \<eta> B)"
        using Conj.IH(2) env by blast
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Conj A B))
          (pp_n_eval C \<eta> (Conj A B))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
        using pp_n_prop_eqv_at[OF A_related]
          pp_n_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Disj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Disj A B)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Disj A B))
          (pp_n_eval C \<eta> (Disj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> A) (pp_n_eval C \<eta> A)"
        using Disj.IH(1) env by blast
      have B_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> B) (pp_n_eval C \<eta> B)"
        using Disj.IH(2) env by blast
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Disj A B))
          (pp_n_eval C \<eta> (Disj A B))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
        using pp_n_prop_eqv_at[OF A_related]
          pp_n_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Imp \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Imp A B)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Imp A B))
          (pp_n_eval C \<eta> (Imp A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> A) (pp_n_eval C \<eta> A)"
        using Imp.IH(1) env by blast
      have B_related:
          "pp_n_eqv Prop w (pp_n_eval C \<rho> B) (pp_n_eval C \<eta> B)"
        using Imp.IH(2) env by blast
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Imp A B))
          (pp_n_eval C \<eta> (Imp A B))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
        using pp_n_prop_eqv_at[OF A_related]
          pp_n_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Forall \<sigma> A)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Forall \<sigma> A))
          (pp_n_eval C \<eta> (Forall \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Forall \<sigma> A))
          (pp_n_eval C \<eta> (Forall \<sigma> A))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have base: "pp_n_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_n_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
              (pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
               pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v)"
        proof -
          fix x
          assume x: "Elem x (pp_n_domain \<sigma>)"
          have xx: "pp_n_eqv \<sigma> v x x"
            using pp_n_eqv_reflexive[OF x] .
          have extended:
              "pp_n_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_n_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_n_eqv Prop v
                (pp_n_eval C (extend_env x \<rho>) A)
                (pp_n_eval C (extend_env x \<eta>) A)"
            using Forall.IH extended by blast
          show "pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
              pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v"
            using pp_n_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<forall>x. Elem x (pp_n_domain \<sigma>) \<longrightarrow>
              pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v) =
            (\<forall>x. Elem x (pp_n_domain \<sigma>) \<longrightarrow>
              pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v)"
          using body_iff by blast
      qed
    qed
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_n_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_n_eval C \<rho> (Exists \<sigma> A)) (pp_n_domain Prop)"
      by (intro allI impI; simp only: pp_n_eval.simps;
          rule pp_n_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_n_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Exists \<sigma> A))
          (pp_n_eval C \<eta> (Exists \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_n_eqv Prop w
          (pp_n_eval C \<rho> (Exists \<sigma> A))
          (pp_n_eval C \<eta> (Exists \<sigma> A))"
        unfolding pp_n_eval.simps pp_n_prop_eqv_pp_n_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have base: "pp_n_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_n_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
              (pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
               pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v)"
        proof -
          fix x
          assume x: "Elem x (pp_n_domain \<sigma>)"
          have xx: "pp_n_eqv \<sigma> v x x"
            using pp_n_eqv_reflexive[OF x] .
          have extended:
              "pp_n_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_n_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_n_eqv Prop v
                (pp_n_eval C (extend_env x \<rho>) A)
                (pp_n_eval C (extend_env x \<eta>) A)"
            using Exists.IH extended by blast
          show "pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
              pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v"
            using pp_n_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<exists>x. Elem x (pp_n_domain \<sigma>) \<and>
              pp_n_holds (pp_n_eval C (extend_env x \<rho>) A) v) =
            (\<exists>x. Elem x (pp_n_domain \<sigma>) \<and>
              pp_n_holds (pp_n_eval C (extend_env x \<eta>) A) v)"
          using body_iff by blast
      qed
    qed
  qed
qed

lemma pp_n_eval_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_n_env_typed \<Gamma> \<rho>"
  shows "pp_n_dom \<tau> (pp_n_eval C \<rho> M)"
  using pp_n_eval_fundamental[OF typed] env
  unfolding pp_n_dom_def by blast

lemma pp_n_eval_respects:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_n_env_eqv w \<Gamma> \<rho> \<eta>"
  shows "pp_n_eqv \<tau> w
    (pp_n_eval C \<rho> M) (pp_n_eval C \<eta> M)"
  using pp_n_eval_fundamental[OF typed] env by blast

definition pp_n_den :: "oterm \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "pp_n_den A env = pp_n_eval C (pp_n_list_env env) A"

sublocale TreeHenkin:
  henkin_action_model pp_n_dom pp_n_holds pp_n_den
proof
  fix \<Gamma> A \<sigma> env
  assume typed: "\<Gamma> \<turnstile> A : \<sigma>"
    and env: "env_ok (map pp_n_dom \<Gamma>) env"
  show "pp_n_dom \<sigma> (pp_n_den A env)"
    unfolding pp_n_den_def
    using pp_n_eval_type[
      OF typed env_ok_implies_pp_n_env_typed[OF env]] .
next
  show "pp_n_holds (pp_n_den (Neg A) env) w \<longleftrightarrow>
      \<not> pp_n_holds (pp_n_den A env) w" for A env w
    by (simp only: pp_n_den_def pp_n_eval_Neg_holds)
next
  show "pp_n_holds (pp_n_den (Imp A B) env) w \<longleftrightarrow>
      (pp_n_holds (pp_n_den A env) w \<longrightarrow>
       pp_n_holds (pp_n_den B env) w)" for A B env w
    by (simp only: pp_n_den_def pp_n_eval_Imp_holds)
next
  show "pp_n_holds (pp_n_den (Forall \<sigma> Q) env) w \<longleftrightarrow>
      (\<forall>x. pp_n_dom \<sigma> x \<longrightarrow>
        pp_n_holds (pp_n_den Q (x # env)) w)" for \<sigma> Q env w
    by (simp only: pp_n_den_def pp_n_dom_def pp_n_list_env_Cons
      pp_n_eval_Forall_holds)
next
  show "pp_n_holds (pp_n_den (Exists \<sigma> P) env) w \<longleftrightarrow>
      (\<exists>x. pp_n_dom \<sigma> x \<and>
        pp_n_holds (pp_n_den P (x # env)) w)" for \<sigma> P env w
    by (simp only: pp_n_den_def pp_n_dom_def pp_n_list_env_Cons
      pp_n_eval_Exists_holds)
next
  show "pp_n_den (shift A) (x # env) = pp_n_den A env" for A x env
    by (simp add: pp_n_den_def pp_n_list_env_Cons pp_n_eval_shift)
next
  show "\<exists>x. pp_n_dom \<sigma> x" for \<sigma>
    using pp_n_domain_nonempty by (simp add: pp_n_dom_def)
qed


end

definition pp_n_default_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_n_default_constants c \<sigma> = pp_n_default \<sigma>"

interpretation DefaultTreeConstants:
  pp_n_constants pp_n_default_constants
  by standard
    (simp add: pp_n_default_constants_def pp_n_default_in_domain)

section \<open>Internal classifiers and moving fundamentality\<close>

definition pp_n_predicate_admissible ::
    "otype \<Rightarrow> (nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "pp_n_predicate_admissible \<sigma> Q \<longleftrightarrow>
    (\<forall>w x y.
      Elem x (pp_n_domain \<sigma>) \<longrightarrow>
      Elem y (pp_n_domain \<sigma>) \<longrightarrow>
      pp_n_eqv \<sigma> w x y \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> (Q v x \<longleftrightarrow> Q v y)))"

definition pp_n_classifier ::
    "otype \<Rightarrow> (nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF"
  where
  "pp_n_classifier \<sigma> Q =
    Lambda (pp_n_domain \<sigma>) (\<lambda>x. pp_n_prop (\<lambda>w. Q w x))"

lemma pp_n_classifier_in_domain:
  assumes admissible: "pp_n_predicate_admissible \<sigma> Q"
  shows "Elem (pp_n_classifier \<sigma> Q)
    (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
proof (unfold pp_n_classifier_def, rule pp_n_lambda_closed)
  show "\<And>x. Elem x (pp_n_domain \<sigma>) \<Longrightarrow>
      Elem (pp_n_prop (\<lambda>w. Q w x)) (pp_n_domain Prop)"
    by (rule pp_n_prop_in_domain)
  fix w x y
  assume x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
  show "pp_n_eqv Prop w
      (pp_n_prop (\<lambda>v. Q v x))
      (pp_n_prop (\<lambda>v. Q v y))"
    unfolding pp_n_prop_eqv_pp_n_prop_iff
    using admissible x y xy
    by (simp add: pp_n_predicate_admissible_def)
qed

lemma pp_n_classifier_apply:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
  shows "(pp_n_classifier \<sigma> Q) \<acute> x =
    pp_n_prop (\<lambda>w. Q w x)"
  using x by (simp add: pp_n_classifier_def Lambda_app)

lemma pp_n_classifier_holds:
  assumes x: "Elem x (pp_n_domain \<sigma>)"
  shows "pp_n_holds ((pp_n_classifier \<sigma> Q) \<acute> x) w
    \<longleftrightarrow> Q w x"
  using pp_n_classifier_apply[OF x, of Q] by simp

lemma pp_n_truth_in_domain:
  "Elem (pp_zf_truth b) (pp_n_domain Prop)"
  using pp_zf_truth_in_domain[of b] by simp

definition pp_n_moving_seed :: "nat list \<Rightarrow> ZF" where
  "pp_n_moving_seed w =
    pp_n_prop (\<lambda>v. prefix (w @ [Suc 0]) v)"

lemma pp_n_moving_seed_in_domain:
  "Elem (pp_n_moving_seed w) (pp_n_domain Prop)"
  unfolding pp_n_moving_seed_def
  by (rule pp_n_prop_in_domain)

lemma pp_n_moving_seed_holds[simp]:
  "pp_n_holds (pp_n_moving_seed w) v \<longleftrightarrow>
    prefix (w @ [Suc 0]) v"
  by (simp add: pp_n_moving_seed_def)

lemma pp_n_split_no_common_successor:
  "\<not> (\<exists>z.
    prefix (w @ [0]) z \<and>
    prefix (w @ [Suc 0]) z)"
proof
  assume "\<exists>z.
      prefix (w @ [0]) z \<and>
      prefix (w @ [Suc 0]) z"
  then obtain z where zero_z: "prefix (w @ [0]) z"
    and one_z: "prefix (w @ [Suc 0]) z"
    by blast
  have "prefix (w @ [0]) (w @ [Suc 0]) \<or>
      prefix (w @ [Suc 0]) (w @ [0])"
    using prefix_same_cases[OF zero_z one_z] .
  then show False by simp
qed

lemma pp_n_moving_seed_false_now:
  "\<not> pp_n_eqv Prop w
    (pp_n_moving_seed w) (pp_zf_truth True)"
proof
  assume eqv:
      "pp_n_eqv Prop w
        (pp_n_moving_seed w) (pp_zf_truth True)"
  have at_w:
      "pp_n_holds (pp_n_moving_seed w) w \<longleftrightarrow>
        pp_n_holds (pp_zf_truth True) w"
    using pp_n_prop_eqv_at[OF eqv, of w] by simp
  then show False by simp
qed

lemma pp_n_moving_seed_true_on_left:
  "pp_n_eqv Prop (w @ [Suc 0])
    (pp_n_moving_seed w) (pp_zf_truth True)"
  by simp

lemma pp_n_moving_seed_no_box_on_false_cone:
  assumes future: "prefix (w @ [0]) v"
  shows "\<not> pp_n_eqv Prop v
    (pp_n_moving_seed w) (pp_zf_truth True)"
proof
  assume box:
      "pp_n_eqv Prop v
        (pp_n_moving_seed w) (pp_zf_truth True)"
  have at_v:
      "pp_n_holds (pp_n_moving_seed w) v \<longleftrightarrow>
        pp_n_holds (pp_zf_truth True) v"
    using pp_n_prop_eqv_at[OF box, of v] by simp
  have true_branch: "prefix (w @ [Suc 0]) v"
    using at_v by simp
  show False
    using pp_n_split_no_common_successor[of w]
      future true_branch by blast
qed

fun pp_n_moving_fundamental_at ::
    "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_n_moving_fundamental_at Ind w x = False"
| "pp_n_moving_fundamental_at Prop w x =
    pp_n_eqv Prop w x (pp_n_moving_seed w)"
| "pp_n_moving_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x =
    False"

lemma pp_n_moving_fundamental_admissible:
  "pp_n_predicate_admissible \<sigma>
    (pp_n_moving_fundamental_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_n_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_n_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_n_domain Prop)"
      and y: "Elem y (pp_n_domain Prop)"
      and xy: "pp_n_eqv Prop w x y"
      and future: "prefix w v"
    have xy_v: "pp_n_eqv Prop v x y"
      using pp_n_eqv_persistent[OF xy future] .
    have seed_refl:
        "pp_n_eqv Prop v
          (pp_n_moving_seed v) (pp_n_moving_seed v)"
      using pp_n_eqv_reflexive[OF pp_n_moving_seed_in_domain] .
    show "pp_n_moving_fundamental_at Prop v x =
        pp_n_moving_fundamental_at Prop v y"
      using pp_n_eqv_congruence[
        OF x y pp_n_moving_seed_in_domain
          pp_n_moving_seed_in_domain xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_n_predicate_admissible_def)
qed

fun pp_n_moving_internal_constants ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_n_moving_internal_constants Pure c Ind = pp_n_default Ind"
| "pp_n_moving_internal_constants Pure c Prop = pp_n_default Prop"
| "pp_n_moving_internal_constants Pure c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_n_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_n_classifier \<sigma> (pp_n_moving_fundamental_at \<sigma>)
     else pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

locale pp_n_moving_internal_parameters =
  fixes Pure :: "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_n_predicate_admissible \<sigma> (Pure \<sigma>)"
begin

lemma pp_n_moving_internal_constants_typed:
  "Elem (pp_n_moving_internal_constants Pure c \<sigma>)
    (pp_n_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_n_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_n_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem (pp_n_classifier \<sigma> (Pure \<sigma>))
        (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_n_classifier_in_domain[OF Pure_admissible] .
  have fun_classifier:
      "Elem
        (pp_n_classifier \<sigma> (pp_n_moving_fundamental_at \<sigma>))
        (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_n_classifier_in_domain[
      OF pp_n_moving_fundamental_admissible] .
  have default:
      "Elem (pp_n_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_n_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_n_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

sublocale MovingTreeConstants:
  pp_n_constants "pp_n_moving_internal_constants Pure"
  by standard (rule pp_n_moving_internal_constants_typed)

lemma pp_n_moving_eval_Pure[simp]:
  "pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> (pp_Pure \<sigma>) =
    pp_n_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_n_moving_eval_Fun[simp]:
  "pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> (pp_Fun \<sigma>) =
    pp_n_classifier \<sigma> (pp_n_moving_fundamental_at \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_n_moving_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_n_env_typed \<Gamma> \<rho>"
  shows "pp_n_holds
      (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      Pure \<sigma> w
        (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> M)
        (pp_n_domain \<sigma>)"
    using MovingTreeConstants.pp_n_eval_type[OF typed env]
    by (simp add: pp_n_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_n_classifier_holds[OF argument, of "Pure \<sigma>" w]
    by simp
qed

lemma pp_n_moving_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_n_env_typed \<Gamma> \<rho>"
  shows "pp_n_holds
      (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_n_moving_fundamental_at \<sigma> w
        (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho> M)
        (pp_n_domain \<sigma>)"
    using MovingTreeConstants.pp_n_eval_type[OF typed env]
    by (simp add: pp_n_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_n_classifier_holds[
      OF argument, of "pp_n_moving_fundamental_at \<sigma>" w]
    by simp
qed

lemma pp_n_moving_unique_fundamental_holds:
  "pp_n_holds
    (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_n_moving_seed w"
  have base: "pp_n_env_typed [] \<rho>"
    by (simp add: pp_n_env_typed_def lookup_def)
  have r_env:
      "pp_n_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_n_env_typed_extend[
      OF base pp_n_moving_seed_in_domain] .
  have r_is_fundamental:
      "pp_n_holds
        (pp_n_eval (pp_n_moving_internal_constants Pure)
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_n_eqv Prop w ?r ?r"
      using pp_n_eqv_reflexive[OF pp_n_moving_seed_in_domain] .
    show ?thesis
      using pp_n_moving_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_n_domain Prop) \<longrightarrow>
        pp_n_holds
          (pp_n_eval (pp_n_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_n_domain Prop)"
    have yr_env:
        "pp_n_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_n_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_n_holds
          (pp_n_eval (pp_n_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_n_eqv Prop w y ?r"
      using pp_n_moving_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_n_holds
          (pp_n_eval (pp_n_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_n_eqv Prop w y ?r"
      by simp
    show "pp_n_holds
        (pp_n_eval (pp_n_moving_internal_constants Pure)
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_n_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_n_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_n_moving_seed_in_domain r_is_fundamental uniqueness
    by (simp only: pp_n_eval_Conj_holds pp_n_eval_Forall_holds)
qed

lemma pp_n_moving_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_n_holds
    (pp_n_eval (pp_n_moving_internal_constants Pure) \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_n_env_typed [] \<rho>"
    by (simp add: pp_n_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_n_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_n_domain \<sigma>)"
    have extended:
        "pp_n_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_n_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_n_moving_fundamental_at \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_n_holds
          (pp_n_eval (pp_n_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_n_moving_fundamental_at \<sigma> w x"
      using pp_n_moving_eval_fun_holds[
        OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_n_holds
          (pp_n_eval (pp_n_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_n_holds
        (pp_n_eval (pp_n_moving_internal_constants Pure)
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_n_eval_Neg_holds[
        of "pp_n_moving_internal_constants Pure" "extend_env x \<rho>"
          "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_n_moving_unique_fundamental_gvalid:
  "MovingTreeConstants.TreeHenkin.gvalid []
    (pp_unique_fundamental Prop)"
  unfolding MovingTreeConstants.TreeHenkin.gvalid_def
    MovingTreeConstants.pp_n_den_def
  using pp_n_moving_unique_fundamental_holds by blast

theorem pp_n_moving_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "MovingTreeConstants.TreeHenkin.gvalid []
    (pp_no_fundamentals \<sigma>)"
  unfolding MovingTreeConstants.TreeHenkin.gvalid_def
    MovingTreeConstants.pp_n_den_def
  using pp_n_moving_no_fundamentals_holds[OF assms] by blast


end

section \<open>The first logical-purity Recombination test\<close>

lemma pp_n_identity_predicate_admissible:
  assumes a: "Elem a (pp_n_domain \<sigma>)"
  shows "pp_n_predicate_admissible \<sigma>
    (\<lambda>w x. pp_n_eqv \<sigma> w x a)"
  unfolding pp_n_predicate_admissible_def
proof (intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_n_domain \<sigma>)"
    and y: "Elem y (pp_n_domain \<sigma>)"
    and xy: "pp_n_eqv \<sigma> w x y"
    and future: "prefix w v"
  have xy_v: "pp_n_eqv \<sigma> v x y"
    using pp_n_eqv_persistent[OF xy future] .
  have aa: "pp_n_eqv \<sigma> v a a"
    using pp_n_eqv_reflexive[OF a] .
  show "pp_n_eqv \<sigma> v x a = pp_n_eqv \<sigma> v y a"
    using pp_n_eqv_congruence[OF x y a a xy_v aa] .
qed

definition pp_n_not_box_classifier :: ZF where
  "pp_n_not_box_classifier =
    pp_n_classifier Prop
      (\<lambda>w q. \<not> pp_n_eqv Prop w q (pp_zf_truth True))"

definition pp_n_diamond_box_classifier :: ZF where
  "pp_n_diamond_box_classifier =
    pp_n_classifier Prop
      (\<lambda>w q. \<exists>v.
        prefix w v \<and>
        pp_n_eqv Prop v q (pp_zf_truth True))"

lemma pp_n_not_box_predicate_admissible:
  "pp_n_predicate_admissible Prop
    (\<lambda>w q. \<not> pp_n_eqv Prop w q (pp_zf_truth True))"
  using pp_n_identity_predicate_admissible[
    OF pp_n_truth_in_domain[of True]]
  unfolding pp_n_predicate_admissible_def by blast

lemma pp_n_diamond_box_predicate_admissible:
  "pp_n_predicate_admissible Prop
    (\<lambda>w q. \<exists>v.
      prefix w v \<and>
      pp_n_eqv Prop v q (pp_zf_truth True))"
  unfolding pp_n_predicate_admissible_def
proof (intro allI impI)
  fix w x y u
  assume x: "Elem x (pp_n_domain Prop)"
    and y: "Elem y (pp_n_domain Prop)"
    and xy: "pp_n_eqv Prop w x y"
    and future: "prefix w u"
  have xy_u: "pp_n_eqv Prop u x y"
    using pp_n_eqv_persistent[OF xy future] .
  show "(\<exists>v. prefix u v \<and>
      pp_n_eqv Prop v x (pp_zf_truth True)) =
    (\<exists>v. prefix u v \<and>
      pp_n_eqv Prop v y (pp_zf_truth True))"
  proof
    assume "\<exists>v. prefix u v \<and>
        pp_n_eqv Prop v x (pp_zf_truth True)"
    then obtain v where uv: "prefix u v"
      and x_true:
        "pp_n_eqv Prop v x (pp_zf_truth True)"
      by blast
    have xy_v: "pp_n_eqv Prop v x y"
      using pp_n_eqv_persistent[OF xy_u uv] .
    have yx_v: "pp_n_eqv Prop v y x"
      using pp_n_eqv_symmetric[OF x y xy_v] .
    have y_true:
        "pp_n_eqv Prop v y (pp_zf_truth True)"
      using pp_n_eqv_transitive[
        OF y x pp_n_truth_in_domain yx_v x_true] .
    show "\<exists>v. prefix u v \<and>
        pp_n_eqv Prop v y (pp_zf_truth True)"
      using uv y_true by blast
  next
    assume "\<exists>v. prefix u v \<and>
        pp_n_eqv Prop v y (pp_zf_truth True)"
    then obtain v where uv: "prefix u v"
      and y_true:
        "pp_n_eqv Prop v y (pp_zf_truth True)"
      by blast
    have xy_v: "pp_n_eqv Prop v x y"
      using pp_n_eqv_persistent[OF xy_u uv] .
    have x_true:
        "pp_n_eqv Prop v x (pp_zf_truth True)"
      using pp_n_eqv_transitive[
        OF x y pp_n_truth_in_domain xy_v y_true] .
    show "\<exists>v. prefix u v \<and>
        pp_n_eqv Prop v x (pp_zf_truth True)"
      using uv x_true by blast
  qed
qed

lemma pp_n_not_box_classifier_in_domain:
  "Elem pp_n_not_box_classifier
    (pp_n_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_n_not_box_classifier_def
  by (rule pp_n_classifier_in_domain)
    (rule pp_n_not_box_predicate_admissible)

lemma pp_n_diamond_box_classifier_in_domain:
  "Elem pp_n_diamond_box_classifier
    (pp_n_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_n_diamond_box_classifier_def
  by (rule pp_n_classifier_in_domain)
    (rule pp_n_diamond_box_predicate_admissible)

lemma pp_n_not_box_classifier_holds:
  assumes q: "Elem q (pp_n_domain Prop)"
  shows "pp_n_holds (pp_n_not_box_classifier \<acute> q) w
    \<longleftrightarrow>
      \<not> pp_n_eqv Prop w q (pp_zf_truth True)"
  unfolding pp_n_not_box_classifier_def
  using pp_n_classifier_holds[
    OF q,
    of "\<lambda>w q. \<not> pp_n_eqv Prop w q (pp_zf_truth True)" w]
  by simp

lemma pp_n_diamond_box_classifier_holds:
  assumes q: "Elem q (pp_n_domain Prop)"
  shows "pp_n_holds (pp_n_diamond_box_classifier \<acute> q) w
    \<longleftrightarrow>
      (\<exists>v. prefix w v \<and>
        pp_n_eqv Prop v q (pp_zf_truth True))"
  unfolding pp_n_diamond_box_classifier_def
  using pp_n_classifier_holds[
    OF q,
    of "\<lambda>w q. \<exists>v.
      prefix w v \<and>
      pp_n_eqv Prop v q (pp_zf_truth True)" w]
  by simp

lemma pp_n_eval_ObjTrue:
  "pp_n_eval C \<rho> ObjTrue = pp_zf_truth True"
  unfolding ObjTrue_def
  apply simp
  unfolding pp_zf_truth_def pp_n_prop_def
    pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep Elem_nat2Nat_Nat)

lemma pp_n_prop_ext:
  assumes P: "Elem P (pp_n_domain Prop)"
    and Q: "Elem Q (pp_n_domain Prop)"
    and holds: "\<And>w. pp_n_holds P w \<longleftrightarrow> pp_n_holds Q w"
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
    let ?w = "pp_n_decode (Nat2nat z)"
    have code:
        "nat2Nat (pp_n_encode ?w) = z"
      using True by simp
    show ?thesis
      using holds[of ?w]
      unfolding pp_n_holds_def code .
  next
    case False
    have "\<not> Elem z P" and "\<not> Elem z Q"
      using P_sub Q_sub False
      by (auto simp: subset_def)
    then show ?thesis by simp
  qed
qed

lemma pp_n_eval_not_box_logical_operator:
  "pp_n_eval C \<rho> pp_zf_neq_truth_operator =
    pp_n_not_box_classifier"
  unfolding pp_zf_neq_truth_operator_def
    pp_n_not_box_classifier_def pp_n_classifier_def
  apply (simp only: pp_n_eval.simps pp_n_eval_ObjTrue)
  apply (simp only: Lambda_ext)
  apply (intro conjI allI impI)
   apply simp
  apply (simp only: extend_env.simps pp_n_eval.simps
      pp_n_eval_ObjTrue)
  by simp

lemma pp_n_eval_ObjBox_holds:
  "pp_n_holds (pp_n_eval C \<rho> (\<box>\<^sub>o A)) w
    \<longleftrightarrow>
    pp_n_eqv Prop w (pp_n_eval C \<rho> A) (pp_zf_truth True)"
  by (simp add: ObjBox_def pp_n_eval_ObjTrue)

lemma pp_n_eval_ObjDiamond_holds:
  "pp_n_holds (pp_n_eval C \<rho> (\<diamond>\<^sub>o A)) w
    \<longleftrightarrow>
      (\<exists>v. prefix w v \<and>
        pp_n_holds (pp_n_eval C \<rho> A) v)"
  unfolding ObjDiamond_def
  by (simp only: pp_n_eval_Neg_holds
      pp_n_eval_ObjBox_holds pp_n_prop_eqv_truth_iff;
      blast)

lemma pp_n_eval_diamond_box_logical_operator:
  "pp_n_eval C \<rho> pp_h_diamond_box_logical_operator =
    pp_n_diamond_box_classifier"
  unfolding pp_h_diamond_box_logical_operator_def
    pp_n_diamond_box_classifier_def pp_n_classifier_def
  apply (simp only: pp_n_eval.simps Lambda_ext)
  apply (intro conjI allI impI)
   apply simp
  apply (rule pp_n_prop_ext)
  subgoal
    unfolding ObjDiamond_def ObjBox_def
    by (simp only: pp_n_eval.simps; rule pp_n_prop_in_domain)
  subgoal
    by (rule pp_n_prop_in_domain)
  subgoal for q w
    using pp_n_eval_ObjDiamond_holds[
      of C "extend_env q \<rho>" "\<box>\<^sub>o (Var 0)" w]
      pp_n_eval_ObjBox_holds[
        of C "extend_env q \<rho>" "Var 0"]
    by (simp add: pp_n_classifier_holds)
  done

definition pp_n_obstruction_pair_pure ::
    "nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_n_obstruction_pair_pure w X \<longleftrightarrow>
    pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
      X pp_n_not_box_classifier \<or>
    pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
      X pp_n_diamond_box_classifier"

lemma pp_n_obstruction_pair_pure_admissible:
  "pp_n_predicate_admissible (Prop \<rightarrow>\<^sub>o Prop)
    pp_n_obstruction_pair_pure"
proof -
  have not_box:
      "pp_n_predicate_admissible (Prop \<rightarrow>\<^sub>o Prop)
        (\<lambda>w X. pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
          X pp_n_not_box_classifier)"
    using pp_n_identity_predicate_admissible[
      OF pp_n_not_box_classifier_in_domain] .
  have diamond_box:
      "pp_n_predicate_admissible (Prop \<rightarrow>\<^sub>o Prop)
        (\<lambda>w X. pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
          X pp_n_diamond_box_classifier)"
    using pp_n_identity_predicate_admissible[
      OF pp_n_diamond_box_classifier_in_domain] .
  show ?thesis
    using not_box diamond_box
    unfolding pp_n_predicate_admissible_def
      pp_n_obstruction_pair_pure_def
    by blast
qed

lemma pp_n_obstruction_pair_contains_not_box:
  "pp_n_obstruction_pair_pure w
    (pp_n_eval C \<rho> pp_zf_neq_truth_operator)"
  unfolding pp_n_eval_not_box_logical_operator
    pp_n_obstruction_pair_pure_def
  using pp_n_eqv_reflexive[
    OF pp_n_not_box_classifier_in_domain, of w]
  by blast

lemma pp_n_obstruction_pair_contains_diamond_box:
  "pp_n_obstruction_pair_pure w
    (pp_n_eval C \<rho> pp_h_diamond_box_logical_operator)"
  unfolding pp_n_eval_diamond_box_logical_operator
    pp_n_obstruction_pair_pure_def
  using pp_n_eqv_reflexive[
    OF pp_n_diamond_box_classifier_in_domain, of w]
  by blast

definition pp_n_unary_recombines_at ::
    "(nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      ZF \<Rightarrow> nat list \<Rightarrow> bool"
  where
  "pp_n_unary_recombines_at Pure r w \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_n_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      Pure w X \<longrightarrow>
      ((\<forall>v. prefix w v \<longrightarrow>
          pp_n_holds (X \<acute> r) v) \<longrightarrow>
        (\<forall>q. Elem q (pp_n_domain Prop) \<longrightarrow>
          pp_n_holds (X \<acute> q) w)))"

lemma pp_n_not_box_antecedent_impossible:
  assumes X: "Elem X (pp_n_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_not_box:
      "pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
        X pp_n_not_box_classifier"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_n_holds (X \<acute> pp_n_moving_seed w) v"
  shows False
proof -
  have seed: "Elem (pp_n_moving_seed w) (pp_n_domain Prop)"
    by (rule pp_n_moving_seed_in_domain)
  have future: "prefix w (w @ [Suc 0])"
    by simp
  have X_related:
      "pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) (w @ [Suc 0])
        X pp_n_not_box_classifier"
    using pp_n_eqv_persistent[OF X_not_box future] .
  have seed_refl:
      "pp_n_eqv Prop (w @ [Suc 0])
        (pp_n_moving_seed w) (pp_n_moving_seed w)"
    using pp_n_eqv_reflexive[OF seed] .
  have applications_related:
      "pp_n_eqv Prop (w @ [Suc 0])
        (X \<acute> pp_n_moving_seed w)
        (pp_n_not_box_classifier \<acute> pp_n_moving_seed w)"
    using pp_n_app_respects[
      OF X_related seed seed seed_refl] .
  have X_true:
      "pp_n_holds (X \<acute> pp_n_moving_seed w) (w @ [Suc 0])"
    using necessary future by blast
  have transfer:
      "pp_n_holds (X \<acute> pp_n_moving_seed w) (w @ [Suc 0])
        \<longleftrightarrow>
      pp_n_holds
        (pp_n_not_box_classifier \<acute> pp_n_moving_seed w)
        (w @ [Suc 0])"
    using pp_n_prop_eqv_at[
      OF applications_related, of "w @ [Suc 0]"] by simp
  have not_box_false:
      "\<not> pp_n_holds
        (pp_n_not_box_classifier \<acute> pp_n_moving_seed w)
        (w @ [Suc 0])"
    using pp_n_not_box_classifier_holds[
      OF seed, of "w @ [Suc 0]"]
      pp_n_moving_seed_true_on_left[of w]
    by blast
  show False
    using X_true transfer not_box_false by blast
qed

lemma pp_n_diamond_box_antecedent_impossible:
  assumes X: "Elem X (pp_n_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_diamond_box:
      "pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) w
        X pp_n_diamond_box_classifier"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_n_holds (X \<acute> pp_n_moving_seed w) v"
  shows False
proof -
  have seed: "Elem (pp_n_moving_seed w) (pp_n_domain Prop)"
    by (rule pp_n_moving_seed_in_domain)
  have future: "prefix w (w @ [0])"
    by simp
  have X_related:
      "pp_n_eqv (Prop \<rightarrow>\<^sub>o Prop) (w @ [0])
        X pp_n_diamond_box_classifier"
    using pp_n_eqv_persistent[OF X_diamond_box future] .
  have seed_refl:
      "pp_n_eqv Prop (w @ [0])
        (pp_n_moving_seed w) (pp_n_moving_seed w)"
    using pp_n_eqv_reflexive[OF seed] .
  have applications_related:
      "pp_n_eqv Prop (w @ [0])
        (X \<acute> pp_n_moving_seed w)
        (pp_n_diamond_box_classifier \<acute> pp_n_moving_seed w)"
    using pp_n_app_respects[
      OF X_related seed seed seed_refl] .
  have X_true:
      "pp_n_holds (X \<acute> pp_n_moving_seed w) (w @ [0])"
    using necessary future by blast
  have transfer:
      "pp_n_holds (X \<acute> pp_n_moving_seed w) (w @ [0])
        \<longleftrightarrow>
      pp_n_holds
        (pp_n_diamond_box_classifier \<acute> pp_n_moving_seed w)
        (w @ [0])"
    using pp_n_prop_eqv_at[
      OF applications_related, of "w @ [0]"] by simp
  have diamond_box_false:
      "\<not> pp_n_holds
        (pp_n_diamond_box_classifier \<acute> pp_n_moving_seed w)
        (w @ [0])"
  proof
    assume holds:
        "pp_n_holds
          (pp_n_diamond_box_classifier \<acute> pp_n_moving_seed w)
          (w @ [0])"
    obtain v where false_v: "prefix (w @ [0]) v"
      and box_v:
        "pp_n_eqv Prop v
          (pp_n_moving_seed w) (pp_zf_truth True)"
      using pp_n_diamond_box_classifier_holds[
        OF seed, of "w @ [0]"] holds by blast
    show False
      using pp_n_moving_seed_no_box_on_false_cone[
        OF false_v] box_v by blast
  qed
  show False
    using X_true transfer diamond_box_false by blast
qed

theorem pp_n_moving_obstruction_pair_recombines:
  "pp_n_unary_recombines_at pp_n_obstruction_pair_pure
    (pp_n_moving_seed w) w"
  unfolding pp_n_unary_recombines_at_def
  apply (intro allI impI)
  subgoal for X q
    unfolding pp_n_obstruction_pair_pure_def
    by (meson pp_n_not_box_antecedent_impossible
        pp_n_diamond_box_antecedent_impossible)
  done

end
