theory Bacon_PP_ZF_Full_Frame
  imports
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Central_Model_Obligations"
    "HOL-ZF.MainZF"
    "HOL-Library.More_List"
begin

section \<open>A preconstructed HOL-ZF full frame\<close>

text \<open>
  This is the semantic pivot forced by the quantifier self-call obstruction.
  The object-type domains are sets in HOL-ZF's axiomatized ZFC universe.  In
  particular, the domain at an arrow type is fixed as a genuine set-theoretic
  function space before object-language denotation is defined.  Application is
  therefore meta-application of a set-theoretic function and never launches a
  closure evaluator.

  This construction is explicitly relative to the additional axioms of
  \<open>HOL-ZF\<close>.  It is not a pure-HOL consistency certificate.
\<close>

fun pp_zf_domain :: "otype \<Rightarrow> ZF" where
  "pp_zf_domain Ind = Nat"
| "pp_zf_domain Prop = Power Nat"
| "pp_zf_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Fun (pp_zf_domain \<sigma>) (pp_zf_domain \<tau>)"

fun pp_zf_default :: "otype \<Rightarrow> ZF" where
  "pp_zf_default Ind = Empty"
| "pp_zf_default Prop = Empty"
| "pp_zf_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Lambda (pp_zf_domain \<sigma>) (\<lambda>_. pp_zf_default \<tau>)"

lemma pp_zf_default_in_domain:
  "Elem (pp_zf_default \<sigma>) (pp_zf_domain \<sigma>)"
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
  then show ?case
    by (simp add: Elem_Lambda_Fun)
qed

theorem pp_zf_domain_nonempty:
  "\<exists>x. Elem x (pp_zf_domain \<sigma>)"
  using pp_zf_default_in_domain by blast

definition pp_zf_app :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_zf_app f x = f \<acute> x"

lemma pp_zf_function_isFun:
  assumes "Elem f (Fun U V)"
  shows "isFun f"
  using assms
  by (simp add: Fun_def PFun_def Sep)

lemma pp_zf_function_domain:
  assumes "Elem f (Fun U V)"
  shows "Domain f = U"
  using assms
  by (simp add: Fun_def Sep)

lemma pp_zf_app_closed:
  assumes f: "Elem f (pp_zf_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_zf_domain \<sigma>)"
  shows "Elem (pp_zf_app f x) (pp_zf_domain \<tau>)"
proof -
  have f_typed:
      "Elem f (Fun (pp_zf_domain \<sigma>) (pp_zf_domain \<tau>))"
    using f by simp
  have is_fun: "isFun f"
    using pp_zf_function_isFun[OF f_typed] .
  have domain: "Domain f = pp_zf_domain \<sigma>"
    using pp_zf_function_domain[OF f_typed] .
  have in_range: "Elem (f \<acute> x) (Range f)"
    using fun_value_in_range[OF is_fun] x domain by simp
  have range_subset: "subset (Range f) (pp_zf_domain \<tau>)"
    using Fun_Range[OF f_typed] .
  show ?thesis
    using in_range range_subset
    by (auto simp: pp_zf_app_def subset_def)
qed

lemma pp_zf_lambda_closed:
  assumes body:
      "\<And>x. Elem x (pp_zf_domain \<sigma>) \<Longrightarrow>
        Elem (F x) (pp_zf_domain \<tau>)"
  shows "Elem (Lambda (pp_zf_domain \<sigma>) F)
    (pp_zf_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  using body by (simp add: Elem_Lambda_Fun)

lemma pp_zf_beta:
  assumes "Elem x (pp_zf_domain \<sigma>)"
  shows "pp_zf_app (Lambda (pp_zf_domain \<sigma>) F) x = F x"
  using assms by (simp add: pp_zf_app_def Lambda_app)

lemma pp_zf_eta:
  assumes f: "Elem f (pp_zf_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Lambda (pp_zf_domain \<sigma>) (pp_zf_app f) = f"
proof -
  have f_typed:
      "Elem f (Fun (pp_zf_domain \<sigma>) (pp_zf_domain \<tau>))"
    using f by simp
  obtain F where f_rep:
      "f = Lambda (pp_zf_domain \<sigma>) F"
    using Elem_Fun_Lambda[OF f_typed] by auto
  show ?thesis
    unfolding f_rep
    by (simp add: Lambda_ext pp_zf_app_def Lambda_app)
qed

subsection \<open>The equality PER and its domains\<close>

definition pp_zf_per :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_zf_per \<sigma> x y \<longleftrightarrow>
    Elem x (pp_zf_domain \<sigma>) \<and> x = y"

lemma pp_zf_per_symmetric:
  "pp_zf_per \<sigma> x y \<Longrightarrow> pp_zf_per \<sigma> y x"
  by (auto simp: pp_zf_per_def)

lemma pp_zf_per_transitive:
  "pp_zf_per \<sigma> x y \<Longrightarrow>
    pp_zf_per \<sigma> y z \<Longrightarrow>
    pp_zf_per \<sigma> x z"
  by (auto simp: pp_zf_per_def)

lemma pp_zf_per_domain_iff:
  "pp_zf_per \<sigma> x x \<longleftrightarrow> Elem x (pp_zf_domain \<sigma>)"
  by (simp add: pp_zf_per_def)

theorem pp_zf_per_domain_nonempty:
  "\<exists>x. pp_zf_per \<sigma> x x"
  using pp_zf_domain_nonempty
  by (simp add: pp_zf_per_domain_iff)

lemma pp_zf_app_respects_per:
  assumes fg: "pp_zf_per (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g"
    and xy: "pp_zf_per \<sigma> x y"
  shows "pp_zf_per \<tau> (pp_zf_app f x) (pp_zf_app g y)"
  using fg xy pp_zf_app_closed
  by (auto simp: pp_zf_per_def)

text \<open>
  The requested nonempty PER domains are therefore no longer generated by
  application.  They are the diagonals of equality restricted to the already
  constructed typed sets.  This reverses the circular dependency that defeated
  the closure evaluator.
\<close>

section \<open>Structural denotation over the preconstructed frame\<close>

definition pp_zf_dom :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_zf_dom \<sigma> x \<longleftrightarrow> Elem x (pp_zf_domain \<sigma>)"

definition pp_zf_prop :: "(ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_zf_prop P = Sep Nat P"

lemma pp_zf_prop_member[simp]:
  "Elem w (pp_zf_prop P) \<longleftrightarrow> Elem w Nat \<and> P w"
  by (simp add: pp_zf_prop_def Sep)

lemma pp_zf_prop_in_domain:
  "Elem (pp_zf_prop P) (pp_zf_domain Prop)"
  by (auto simp: pp_zf_prop_def Power subset_def Sep)

lemma pp_zf_prop_dom[simp]:
  "pp_zf_dom Prop (pp_zf_prop P)"
  unfolding pp_zf_dom_def
  by (rule pp_zf_prop_in_domain)

definition pp_zf_holds :: "ZF \<Rightarrow> nat \<Rightarrow> bool" where
  "pp_zf_holds P w \<longleftrightarrow> Elem (nat2Nat w) P"

lemma pp_zf_holds_prop[simp]:
  "pp_zf_holds (pp_zf_prop P) w \<longleftrightarrow> P (nat2Nat w)"
  by (simp add: pp_zf_holds_def Elem_nat2Nat_Nat)

definition pp_zf_env_typed ::
    "ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_zf_env_typed \<Gamma> \<rho> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      pp_zf_dom \<sigma> (\<rho> n))"

lemma pp_zf_env_typed_lookup:
  assumes "pp_zf_env_typed \<Gamma> \<rho>"
    and "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_zf_dom \<sigma> (\<rho> n)"
  using assms unfolding pp_zf_env_typed_def by blast

lemma pp_zf_env_typed_extend:
  assumes env: "pp_zf_env_typed \<Gamma> \<rho>"
    and x: "pp_zf_dom \<sigma> x"
  shows "pp_zf_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
proof (unfold pp_zf_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "pp_zf_dom \<tau> (extend_env x \<rho> n)"
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
    then have "pp_zf_dom \<tau> (\<rho> m)"
      using env unfolding pp_zf_env_typed_def by blast
    then show ?thesis
      using Suc by simp
  qed
qed

fun pp_zf_eval ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> oterm \<Rightarrow> ZF" where
  "pp_zf_eval C \<rho> (Var n) = \<rho> n"
| "pp_zf_eval C \<rho> (Const c \<sigma>) = C c \<sigma>"
| "pp_zf_eval C \<rho> (App M N) =
    pp_zf_app (pp_zf_eval C \<rho> M) (pp_zf_eval C \<rho> N)"
| "pp_zf_eval C \<rho> (Lam \<sigma> M) =
    Lambda (pp_zf_domain \<sigma>)
      (\<lambda>x. pp_zf_eval C (extend_env x \<rho>) M)"
| "pp_zf_eval C \<rho> (Eq \<sigma> M N) =
    pp_zf_prop (\<lambda>_. pp_zf_eval C \<rho> M = pp_zf_eval C \<rho> N)"
| "pp_zf_eval C \<rho> (Neg A) =
    pp_zf_prop (\<lambda>w. \<not> Elem w (pp_zf_eval C \<rho> A))"
| "pp_zf_eval C \<rho> (Conj A B) =
    pp_zf_prop (\<lambda>w.
      Elem w (pp_zf_eval C \<rho> A) \<and> Elem w (pp_zf_eval C \<rho> B))"
| "pp_zf_eval C \<rho> (Disj A B) =
    pp_zf_prop (\<lambda>w.
      Elem w (pp_zf_eval C \<rho> A) \<or> Elem w (pp_zf_eval C \<rho> B))"
| "pp_zf_eval C \<rho> (Imp A B) =
    pp_zf_prop (\<lambda>w.
      Elem w (pp_zf_eval C \<rho> A) \<longrightarrow> Elem w (pp_zf_eval C \<rho> B))"
| "pp_zf_eval C \<rho> (Forall \<sigma> A) =
    pp_zf_prop (\<lambda>w.
      \<forall>x. pp_zf_dom \<sigma> x \<longrightarrow>
        Elem w (pp_zf_eval C (extend_env x \<rho>) A))"
| "pp_zf_eval C \<rho> (Exists \<sigma> A) =
    pp_zf_prop (\<lambda>w.
      \<exists>x. pp_zf_dom \<sigma> x \<and>
        Elem w (pp_zf_eval C (extend_env x \<rho>) A))"

locale pp_zf_constants =
  fixes C :: "string \<Rightarrow> otype \<Rightarrow> ZF"
  assumes C_typed: "pp_zf_dom \<sigma> (C c \<sigma>)"
begin

lemma pp_zf_eval_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_zf_env_typed \<Gamma> \<rho>"
  shows "pp_zf_dom \<tau> (pp_zf_eval C \<rho> M)"
  using typed env
proof (induction arbitrary: \<rho> rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case
    using pp_zf_env_typed_lookup by simp
next
  case (Const \<Gamma> c \<tau>)
  then show ?case
    using C_typed by simp
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have M: "pp_zf_dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) (pp_zf_eval C \<rho> M)"
    using App.IH(1) App.prems by blast
  have N: "pp_zf_dom \<sigma> (pp_zf_eval C \<rho> N)"
    using App.IH(2) App.prems by blast
  show ?case
    using pp_zf_app_closed M N
    by (simp add: pp_zf_dom_def)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have body:
      "\<And>x. Elem x (pp_zf_domain \<sigma>) \<Longrightarrow>
        Elem (pp_zf_eval C (extend_env x \<rho>) M) (pp_zf_domain \<tau>)"
  proof -
    fix x
    assume x: "Elem x (pp_zf_domain \<sigma>)"
    have "pp_zf_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      using pp_zf_env_typed_extend[OF Lam.prems]
      x by (simp add: pp_zf_dom_def)
    then show "Elem (pp_zf_eval C (extend_env x \<rho>) M)
        (pp_zf_domain \<tau>)"
      using Lam.IH by (simp add: pp_zf_dom_def)
  qed
  show ?case
    using pp_zf_lambda_closed[OF body]
    by (simp add: pp_zf_dom_def)
next
  case (Eq \<Gamma> M \<sigma> N)
  then show ?case
    by simp
next
  case (Neg \<Gamma> A)
  then show ?case
    by simp
next
  case (Conj \<Gamma> A B)
  then show ?case
    by simp
next
  case (Disj \<Gamma> A B)
  then show ?case
    by simp
next
  case (Imp \<Gamma> A B)
  then show ?case
    by simp
next
  case (Forall \<sigma> \<Gamma> A)
  then show ?case
    by simp
next
  case (Exists \<sigma> \<Gamma> A)
  then show ?case
    by simp
qed

lemma pp_zf_eval_rename:
  "pp_zf_eval C \<rho> (rename r M) =
    pp_zf_eval C (\<lambda>n. \<rho> (r n)) M"
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

lemma pp_zf_eval_shift:
  "pp_zf_eval C (extend_env x \<rho>) (shift M) = pp_zf_eval C \<rho> M"
  unfolding shift_def
  using pp_zf_eval_rename[of "extend_env x \<rho>" Suc M]
  by simp

definition pp_zf_list_env :: "ZF list \<Rightarrow> nat \<Rightarrow> ZF" where
  "pp_zf_list_env env = nth_default Empty env"

definition pp_zf_den :: "oterm \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "pp_zf_den A env = pp_zf_eval C (pp_zf_list_env env) A"

lemma pp_zf_list_env_Cons:
  "pp_zf_list_env (x # env) = extend_env x (pp_zf_list_env env)"
  by (rule ext, rename_tac n, case_tac n)
    (simp_all add: pp_zf_list_env_def nth_default_def)

lemma env_ok_implies_pp_zf_env_typed:
  assumes "env_ok (map pp_zf_dom \<Gamma>) env"
  shows "pp_zf_env_typed \<Gamma> (pp_zf_list_env env)"
proof (unfold pp_zf_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  then have n_lt: "n < length \<Gamma>" and nth: "\<Gamma> ! n = \<sigma>"
    by (auto simp: lookup_def split: if_splits)
  from assms have len: "length env = length \<Gamma>"
    and entries:
      "\<forall>k<length \<Gamma>. pp_zf_dom (\<Gamma> ! k) (env ! k)"
    by (auto simp: env_ok_def)
  have env_n: "pp_zf_list_env env n = env ! n"
    using n_lt len
    by (simp add: pp_zf_list_env_def nth_default_nth)
  have typed_n: "pp_zf_dom (\<Gamma> ! n) (env ! n)"
    using entries n_lt by blast
  show "pp_zf_dom \<sigma> (pp_zf_list_env env n)"
    using env_n typed_n nth by simp
qed

sublocale ZFHenkin:
  henkin_action_model pp_zf_dom pp_zf_holds pp_zf_den
proof
  fix \<Gamma> A \<sigma> env
  assume typed: "\<Gamma> \<turnstile> A : \<sigma>"
    and env: "env_ok (map pp_zf_dom \<Gamma>) env"
  show "pp_zf_dom \<sigma> (pp_zf_den A env)"
    unfolding pp_zf_den_def
    using pp_zf_eval_type[OF typed env_ok_implies_pp_zf_env_typed[OF env]] .
next
  show "pp_zf_holds (pp_zf_den (Neg A) env) w \<longleftrightarrow>
      \<not> pp_zf_holds (pp_zf_den A env) w" for A env w
    by (simp add: pp_zf_den_def pp_zf_holds_def Elem_nat2Nat_Nat)
next
  show "pp_zf_holds (pp_zf_den (Imp A B) env) w \<longleftrightarrow>
      (pp_zf_holds (pp_zf_den A env) w \<longrightarrow>
       pp_zf_holds (pp_zf_den B env) w)" for A B env w
    by (simp add: pp_zf_den_def pp_zf_holds_def Elem_nat2Nat_Nat)
next
  show "pp_zf_holds (pp_zf_den (Forall \<sigma> Q) env) w \<longleftrightarrow>
      (\<forall>x. pp_zf_dom \<sigma> x \<longrightarrow>
        pp_zf_holds (pp_zf_den Q (x # env)) w)" for \<sigma> Q env w
    by (simp add: pp_zf_den_def pp_zf_holds_def pp_zf_list_env_Cons
      Elem_nat2Nat_Nat)
next
  show "pp_zf_holds (pp_zf_den (Exists \<sigma> P) env) w \<longleftrightarrow>
      (\<exists>x. pp_zf_dom \<sigma> x \<and>
        pp_zf_holds (pp_zf_den P (x # env)) w)" for \<sigma> P env w
    by (simp add: pp_zf_den_def pp_zf_holds_def pp_zf_list_env_Cons
      Elem_nat2Nat_Nat)
next
  show "pp_zf_den (shift A) (x # env) = pp_zf_den A env" for A x env
    by (simp add: pp_zf_den_def pp_zf_list_env_Cons pp_zf_eval_shift)
next
  show "\<exists>x. pp_zf_dom \<sigma> x" for \<sigma>
    using pp_zf_domain_nonempty
    by (simp add: pp_zf_dom_def)
qed

end

definition pp_zf_default_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_zf_default_constants c \<sigma> = pp_zf_default \<sigma>"

interpretation DefaultZFConstants:
  pp_zf_constants pp_zf_default_constants
  by standard
    (simp add: pp_zf_default_constants_def pp_zf_dom_def
      pp_zf_default_in_domain)

text \<open>
  \<open>DefaultZFConstants.ZFHenkin\<close> is the first concrete interpretation of
  \<open>henkin_action_model\<close> in the direct model program.  Unlike the earlier
  \<open>triv_model\<close>, it interprets every object-language constructor by the
  standard operation on a preconstructed full frame.  Its nonlogical constants
  are still defaults.  The next tranche replaces the interpretations of
  \<open>Pure\<close> and \<open>Fun\<close> by typed internal relations and tests global validity
  of the central stock; it must also discharge the stronger base-CEV and zeta
  soundness obligations of \<open>pp_central_stock_model\<close>.
\<close>

section \<open>Internal interpretations of Pure and Fun\<close>

definition pp_zf_truth :: "bool \<Rightarrow> ZF" where
  "pp_zf_truth b = pp_zf_prop (\<lambda>_. b)"

lemma pp_zf_truth_in_domain:
  "Elem (pp_zf_truth b) (pp_zf_domain Prop)"
  unfolding pp_zf_truth_def
  by (rule pp_zf_prop_in_domain)

lemma pp_zf_holds_truth[simp]:
  "pp_zf_holds (pp_zf_truth b) w \<longleftrightarrow> b"
  by (simp add: pp_zf_truth_def)

lemma pp_zf_prop_const:
  "pp_zf_prop (\<lambda>_. b) = pp_zf_truth b"
  by (simp add: pp_zf_truth_def)

definition pp_zf_classifier ::
    "otype \<Rightarrow> (ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_zf_classifier \<sigma> Q =
    Lambda (pp_zf_domain \<sigma>) (\<lambda>x. pp_zf_truth (Q x))"

lemma pp_zf_classifier_in_domain:
  "Elem (pp_zf_classifier \<sigma> Q)
    (pp_zf_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
  unfolding pp_zf_classifier_def
  by (rule pp_zf_lambda_closed)
    (rule pp_zf_truth_in_domain)

lemma pp_zf_classifier_in_function_space:
  "Elem (pp_zf_classifier \<sigma> Q)
    (Fun (pp_zf_domain \<sigma>) (Power Nat))"
  using pp_zf_classifier_in_domain[of \<sigma> Q] by simp

lemma pp_zf_classifier_apply:
  assumes "pp_zf_dom \<sigma> x"
  shows "pp_zf_app (pp_zf_classifier \<sigma> Q) x = pp_zf_truth (Q x)"
  using assms
  by (simp add: pp_zf_classifier_def pp_zf_dom_def pp_zf_beta)

fun pp_zf_fundamental :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_zf_fundamental Ind x = False"
| "pp_zf_fundamental Prop x = (x = Empty)"
| "pp_zf_fundamental (\<sigma> \<rightarrow>\<^sub>o \<tau>) x = False"

lemma pp_zf_fundamental_witness:
  "pp_zf_dom Prop Empty \<and> pp_zf_fundamental Prop Empty"
  by (simp add: pp_zf_dom_def Power subset_empty)

lemma pp_zf_fundamental_unique:
  assumes "pp_zf_fundamental Prop x"
    and "pp_zf_fundamental Prop y"
  shows "x = y"
  using assms by simp

lemma pp_zf_no_other_fundamentals:
  assumes "\<sigma> \<noteq> Prop"
  shows "\<not> pp_zf_fundamental \<sigma> x"
  using assms by (cases \<sigma>) auto

lemma pp_zf_default_arrow_in_function_space:
  "Elem (Lambda (pp_zf_domain \<sigma>) (\<lambda>_. pp_zf_default \<tau>))
    (Fun (pp_zf_domain \<sigma>) (pp_zf_domain \<tau>))"
  by (simp add: Elem_Lambda_Fun pp_zf_default_in_domain)

fun pp_zf_internal_constants ::
    "(otype \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_zf_internal_constants Pure c Ind = pp_zf_default Ind"
| "pp_zf_internal_constants Pure c Prop = pp_zf_default Prop"
| "pp_zf_internal_constants Pure c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_zf_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_zf_classifier \<sigma> (pp_zf_fundamental \<sigma>)
     else pp_zf_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

lemma pp_zf_internal_constants_typed:
  "pp_zf_dom \<sigma> (pp_zf_internal_constants Pure c \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_zf_dom_def Elem_Empty_Nat)
next
  case Prop
  then show ?thesis
    by (simp add: pp_zf_dom_def Power subset_empty)
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (auto simp: pp_zf_dom_def
        intro: pp_zf_classifier_in_function_space
          pp_zf_default_arrow_in_function_space)
qed

interpretation InternalZFConstants:
  pp_zf_constants "pp_zf_internal_constants Pure" for Pure
  by standard (rule pp_zf_internal_constants_typed)

lemma pp_zf_eval_Pure[simp]:
  "pp_zf_eval (pp_zf_internal_constants Pure) \<rho> (pp_Pure \<sigma>) =
    pp_zf_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_zf_eval_Fun[simp]:
  "pp_zf_eval (pp_zf_internal_constants Pure) \<rho> (pp_Fun \<sigma>) =
    pp_zf_classifier \<sigma> (pp_zf_fundamental \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_zf_eval_pure:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_zf_env_typed \<Gamma> \<rho>"
  shows
    "pp_zf_eval (pp_zf_internal_constants Pure) \<rho> (pp_pure \<sigma> M) =
      pp_zf_truth (Pure \<sigma>
        (pp_zf_eval (pp_zf_internal_constants Pure) \<rho> M))"
proof -
  have arg:
      "pp_zf_dom \<sigma>
        (pp_zf_eval (pp_zf_internal_constants Pure) \<rho> M)"
    using InternalZFConstants.pp_zf_eval_type[OF typed env] .
  show ?thesis
    unfolding pp_pure_def
    using pp_zf_classifier_apply[OF arg, of "Pure \<sigma>"]
    by simp
qed

lemma pp_zf_eval_fun:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_zf_env_typed \<Gamma> \<rho>"
  shows
    "pp_zf_eval (pp_zf_internal_constants Pure) \<rho> (pp_fun \<sigma> M) =
      pp_zf_truth (pp_zf_fundamental \<sigma>
        (pp_zf_eval (pp_zf_internal_constants Pure) \<rho> M))"
proof -
  have arg:
      "pp_zf_dom \<sigma>
        (pp_zf_eval (pp_zf_internal_constants Pure) \<rho> M)"
    using InternalZFConstants.pp_zf_eval_type[OF typed env] .
  show ?thesis
    unfolding pp_fun_def
    using pp_zf_classifier_apply[OF arg,
      of "pp_zf_fundamental \<sigma>"]
    by simp
qed

text \<open>
  The constant \<open>Fun\<^sub>\<sigma>\<close> now denotes the characteristic function of a
  genuine internal relation: at proposition type it selects exactly
  \<open>Empty\<close>, and at every other type it selects nothing.  Thus the intended
  unique-fundamentality and no-other-fundamentals clauses have a fixed semantic
  witness before the central-stock validation begins.

  The parameter \<open>Pure\<close> is deliberately exposed as a type-indexed relation.
  Choosing it so that the logical purity schema, application closure, PP, and
  both Recombination principles are globally valid is precisely the remaining
  model-theoretic core.  Quantifiers continue to range over the full
  preconstructed domains whatever that choice is, so this remaining problem
  introduces no evaluator/domain circularity.
\<close>

section \<open>The extensional-identity obstruction\<close>

definition pp_zf_eq_truth_operator :: oterm where
  "pp_zf_eq_truth_operator =
    Lam Prop (Eq Prop (Var 0) ObjTrue)"

definition pp_zf_neq_truth_operator :: oterm where
  "pp_zf_neq_truth_operator =
    Lam Prop (Neg (Eq Prop (Var 0) ObjTrue))"

lemma pp_zf_eq_truth_operator_typed:
  "[] \<turnstile> pp_zf_eq_truth_operator : (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound)
    (simp add: pp_zf_eq_truth_operator_def ObjTrue_def lookup_def)

lemma pp_zf_neq_truth_operator_typed:
  "[] \<turnstile> pp_zf_neq_truth_operator : (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound)
    (simp add: pp_zf_neq_truth_operator_def ObjTrue_def lookup_def)

lemma pp_zf_eq_truth_operator_logical:
  "pp_logical_vocabulary pp_zf_eq_truth_operator"
  by (simp add: pp_logical_vocabulary_def pp_zf_eq_truth_operator_def
      ObjTrue_def)

lemma pp_zf_neq_truth_operator_logical:
  "pp_logical_vocabulary pp_zf_neq_truth_operator"
  by (simp add: pp_logical_vocabulary_def pp_zf_neq_truth_operator_def
      ObjTrue_def)

lemma pp_zf_eval_ObjTrue:
  "pp_zf_eval C \<rho> ObjTrue = pp_zf_truth True"
  unfolding ObjTrue_def
  apply simp
  unfolding pp_zf_truth_def pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep)

lemma pp_zf_prop_neg_truth:
  "pp_zf_prop (\<lambda>w. \<not> Elem w (pp_zf_truth b)) =
    pp_zf_truth (\<not> b)"
  unfolding pp_zf_truth_def pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep)

lemma pp_zf_eval_eq_truth_operator:
  "pp_zf_eval C \<rho> pp_zf_eq_truth_operator =
    pp_zf_classifier Prop (\<lambda>x. x = pp_zf_truth True)"
  by (simp only: pp_zf_eq_truth_operator_def pp_zf_eval.simps
      pp_zf_eval_ObjTrue pp_zf_prop_const pp_zf_classifier_def)
    (simp add: extend_env.simps)

lemma pp_zf_eval_neq_truth_operator:
  "pp_zf_eval C \<rho> pp_zf_neq_truth_operator =
    pp_zf_classifier Prop (\<lambda>x. x \<noteq> pp_zf_truth True)"
  by (simp only: pp_zf_neq_truth_operator_def pp_zf_eval.simps
      pp_zf_eval_ObjTrue pp_zf_prop_const pp_zf_prop_neg_truth
      pp_zf_classifier_def)
    (simp add: extend_env.simps)

lemma pp_zf_truth_distinct:
  "pp_zf_truth False \<noteq> pp_zf_truth True"
proof
  assume equal: "pp_zf_truth False = pp_zf_truth True"
  have "pp_zf_holds (pp_zf_truth False) 0 =
      pp_zf_holds (pp_zf_truth True) 0"
    using equal by simp
  then show False by simp
qed

definition pp_zf_unary_recombines ::
    "(otype \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_zf_unary_recombines Pure r \<longleftrightarrow>
    pp_zf_dom Prop r \<and>
    (\<forall>X.
      pp_zf_dom (Prop \<rightarrow>\<^sub>o Prop) X \<longrightarrow>
      Pure (Prop \<rightarrow>\<^sub>o Prop) X \<longrightarrow>
      pp_zf_app X r = pp_zf_truth True \<longrightarrow>
      (\<forall>q. pp_zf_dom Prop q \<longrightarrow>
        pp_zf_app X q = pp_zf_truth True))"

theorem pp_zf_extensional_identity_blocks_recombination:
  assumes eq_pure:
      "Pure (Prop \<rightarrow>\<^sub>o Prop)
        (pp_zf_classifier Prop (\<lambda>x. x = pp_zf_truth True))"
    and neq_pure:
      "Pure (Prop \<rightarrow>\<^sub>o Prop)
        (pp_zf_classifier Prop (\<lambda>x. x \<noteq> pp_zf_truth True))"
  shows "\<not> pp_zf_unary_recombines Pure r"
proof
  assume recombines: "pp_zf_unary_recombines Pure r"
  then have r_typed: "pp_zf_dom Prop r"
    unfolding pp_zf_unary_recombines_def by blast
  show False
  proof (cases "r = pp_zf_truth True")
    case True
    let ?X = "pp_zf_classifier Prop (\<lambda>x. x = pp_zf_truth True)"
    have X_typed: "pp_zf_dom (Prop \<rightarrow>\<^sub>o Prop) ?X"
      using pp_zf_classifier_in_domain[of Prop
        "\<lambda>x. x = pp_zf_truth True"]
      by (simp add: pp_zf_dom_def)
    have Xr: "pp_zf_app ?X r = pp_zf_truth True"
      using pp_zf_classifier_apply[OF r_typed,
        of "\<lambda>x. x = pp_zf_truth True"]
      by (simp add: True)
    have all:
        "\<forall>q. pp_zf_dom Prop q \<longrightarrow>
          pp_zf_app ?X q = pp_zf_truth True"
      using recombines X_typed eq_pure Xr
      unfolding pp_zf_unary_recombines_def by blast
    have false_typed: "pp_zf_dom Prop (pp_zf_truth False)"
      unfolding pp_zf_dom_def
      by (rule pp_zf_truth_in_domain)
    have "pp_zf_app ?X (pp_zf_truth False) = pp_zf_truth True"
      using all false_typed by blast
    moreover have
        "pp_zf_app ?X (pp_zf_truth False) = pp_zf_truth False"
      using pp_zf_classifier_apply[OF false_typed,
        of "\<lambda>x. x = pp_zf_truth True"]
      pp_zf_truth_distinct by simp
    ultimately show False
      using pp_zf_truth_distinct by simp
  next
    case False
    let ?X = "pp_zf_classifier Prop (\<lambda>x. x \<noteq> pp_zf_truth True)"
    have X_typed: "pp_zf_dom (Prop \<rightarrow>\<^sub>o Prop) ?X"
      using pp_zf_classifier_in_domain[of Prop
        "\<lambda>x. x \<noteq> pp_zf_truth True"]
      by (simp add: pp_zf_dom_def)
    have Xr: "pp_zf_app ?X r = pp_zf_truth True"
      using pp_zf_classifier_apply[OF r_typed,
        of "\<lambda>x. x \<noteq> pp_zf_truth True"]
      by (simp add: False)
    have all:
        "\<forall>q. pp_zf_dom Prop q \<longrightarrow>
          pp_zf_app ?X q = pp_zf_truth True"
      using recombines X_typed neq_pure Xr
      unfolding pp_zf_unary_recombines_def by blast
    have true_typed: "pp_zf_dom Prop (pp_zf_truth True)"
      unfolding pp_zf_dom_def
      by (rule pp_zf_truth_in_domain)
    have "pp_zf_app ?X (pp_zf_truth True) = pp_zf_truth True"
      using all true_typed by blast
    moreover have
        "pp_zf_app ?X (pp_zf_truth True) = pp_zf_truth False"
      using pp_zf_classifier_apply[OF true_typed,
        of "\<lambda>x. x \<noteq> pp_zf_truth True"]
      by simp
    ultimately show False
      using pp_zf_truth_distinct by simp
  qed
qed

corollary pp_zf_logical_purity_blocks_recombination:
  assumes logical_pure:
      "\<And>M. [] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop) \<Longrightarrow>
        pp_logical_vocabulary M \<Longrightarrow>
        Pure (Prop \<rightarrow>\<^sub>o Prop) (pp_zf_eval C \<rho> M)"
  shows "\<not> pp_zf_unary_recombines Pure r"
proof (rule pp_zf_extensional_identity_blocks_recombination)
  show "Pure (Prop \<rightarrow>\<^sub>o Prop)
      (pp_zf_classifier Prop (\<lambda>x. x = pp_zf_truth True))"
    using logical_pure[OF pp_zf_eq_truth_operator_typed
      pp_zf_eq_truth_operator_logical]
    by (simp only: pp_zf_eval_eq_truth_operator)
  show "Pure (Prop \<rightarrow>\<^sub>o Prop)
      (pp_zf_classifier Prop (\<lambda>x. x \<noteq> pp_zf_truth True))"
    using logical_pure[OF pp_zf_neq_truth_operator_typed
      pp_zf_neq_truth_operator_logical]
    by (simp only: pp_zf_eval_neq_truth_operator)
qed

text \<open>
  Thus the full-frame pivot solves the evaluator/domain circularity but not yet
  Goodman's problem.  With object identity interpreted as metalanguage equality,
  the purity schema forces both the equality-to-truth and
  inequality-to-truth operators to be pure.  For every proposed fundamental
  proposition, exactly one of those operators is necessarily true there and
  fails somewhere else, contradicting unary Recombination.

  The required next refinement is not a return to closure-generated domains.
  It is a preconstructed frame equipped with a world-indexed, hyperintensional
  equivalence relation.  The denotation of \<open>Eq \<sigma> M N\<close> must record the
  worlds at which the two values are equivalent, rather than collapsing at
  definition time to \<open>UNIV\<close> or \<open>Empty\<close>.  This preserves the terminating
  structural evaluator while avoiding the illicit rigidity of distinctness.
\<close>

end
