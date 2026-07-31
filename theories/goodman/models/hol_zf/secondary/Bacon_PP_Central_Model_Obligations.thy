theory Bacon_PP_Central_Model_Obligations
  imports
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Axiom_Soundness"
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_QSS_Recombination_Bridge"
    "Higher_Order_Metaphysics_PP.Bacon_PP_Purity_Operator"
begin

section \<open>The direct central-stock model program\<close>

text \<open>
  This theory turns the positive consistency program into a sequence of exact
  Isabelle obligations.  The settlement target is intentionally narrow: a model of
  the Recombination-only central stock.  Failure of QSS, emptiness of
  \<open>fun\<acute>\<close>, and failure of a T6 premise are diagnostics for a proposed model; none
  is itself part of Goodman's consistency question.

  The carrier choice made below is the closure-code/PER route.  Propositions are
  sets of action worlds.  Values at all higher types are finite closure codes in one
  recursive universal carrier.  A type-indexed partial equivalence relation is to
  identify extensionally equal codes.  This avoids both the finite-level ceiling of
  \<open>pp_v\<close> and the full-function comprehension built into
  \<open>applicative_structure\<close>.
\<close>

subsection \<open>The exact settlement locale\<close>

locale pp_central_stock_model =
  henkin_action_model dom holds den
  for dom :: "otype \<Rightarrow> 'u \<Rightarrow> bool"
    and holds :: "'u \<Rightarrow> 'w \<Rightarrow> bool"
    and den :: "oterm \<Rightarrow> 'u list \<Rightarrow> 'u" +
  assumes central_base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma> B"
    and central_zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
    and central_stock_valid:
      "gvalid_set pp_recombination_PP_axioms"
begin

theorem central_stock_answers_Goodman:
  "pp_recombination_axiom_consistency_question"
  using central_base_sound central_zeta_sound central_stock_valid
  by (rule pp_recombination_question_of_gvalid)

end

text \<open>
  Thus an interpretation of \<open>pp_central_stock_model\<close>, not merely an
  interpretation of \<open>henkin_action_model\<close>, is the positive certificate.  In
  particular, root truth in an action model does not discharge
  \<open>central_stock_valid\<close>: every added axiom must be valid at every world and in
  every well-typed context.
\<close>

subsection \<open>Generic semantic exclusion of an inconsistent extension\<close>

theorem (in henkin_action_model) derivable_false_excludes_gvalid_set:
  assumes base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma> B"
    and zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
    and contradiction: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  shows "\<not> gvalid_set T"
proof
  assume valid: "gvalid_set T"
  have "gvalid [] ObjFalse"
    using base_sound zeta_sound valid contradiction
    by (rule CEV_axiom_soundness)
  then show False
    using ObjFalse_not_gvalid by blast
qed

context pp_central_stock_model
begin

text \<open>
  These four theorems are audited T6 diagnostics.  They do not say which extra
  premise fails.  They say exactly that no completed central model can also validate
  every member of any one of the four already refuted T6 stocks.
\<close>

theorem central_model_excludes_T6_Inv_stock:
  "\<not> gvalid_set pp_T6_Inv_axioms"
  using central_base_sound central_zeta_sound CEV_Goodman_T6_Inv
  by (rule derivable_false_excludes_gvalid_set)

theorem central_model_excludes_T6_TU_stock:
  "\<not> gvalid_set pp_T6_TU_axioms"
  using central_base_sound central_zeta_sound CEV_Goodman_T6_TU
  by (rule derivable_false_excludes_gvalid_set)

theorem central_model_excludes_T6_WI_stock:
  "\<not> gvalid_set pp_T6_WI_axioms"
  using central_base_sound central_zeta_sound CEV_Goodman_T6_WI
  by (rule derivable_false_excludes_gvalid_set)

theorem central_model_excludes_T6_RS_stock:
  "\<not> gvalid_set pp_T6_RS_axioms"
  using central_base_sound central_zeta_sound CEV_Goodman_T6_RS
  by (rule derivable_false_excludes_gvalid_set)

end

subsection \<open>The orbit-classifier negative control\<close>

definition pp_stock_recombines ::
    "pp_sem_prop set set \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_stock_recombines Stock r \<longleftrightarrow>
    (\<forall>S \<in> Stock. pp_root_unary_recombination S r)"

theorem pp_orbit_classifier_falsifies_recombination:
  "\<not> pp_root_unary_recombination (pp_orbit r) r"
  using pp_orbit_not_UNIV
  by (simp add: pp_root_unary_recombination_iff)

theorem pp_stock_containing_orbit_classifier_fails:
  assumes "pp_orbit r \<in> Stock"
  shows "\<not> pp_stock_recombines Stock r"
  using assms pp_orbit_classifier_falsifies_recombination
  unfolding pp_stock_recombines_def by blast

definition pp_invariant_operator_index_stock :: "pp_sem_prop set set" where
  "pp_invariant_operator_index_stock =
    {pp_operator_index F | F.
      pp_function_space_member F \<and> pp_fun_invariant F}"

lemma pp_orbit_in_invariant_operator_index_stock:
  "pp_orbit r \<in> pp_invariant_operator_index_stock"
proof -
  have member_invariant:
      "pp_function_space_member (pp_classifier (pp_orbit r)) \<and>
       pp_fun_invariant (pp_classifier (pp_orbit r))"
    by (rule pp_classifier_is_function_space_invariant)
  moreover have
      "pp_operator_index (pp_classifier (pp_orbit r)) = pp_orbit r"
    by simp
  ultimately show ?thesis
    unfolding pp_invariant_operator_index_stock_def by blast
qed

theorem pp_all_invariant_operator_indices_fail_recombination:
  "\<not> pp_stock_recombines pp_invariant_operator_index_stock r"
  using pp_orbit_in_invariant_operator_index_stock
  by (rule pp_stock_containing_orbit_classifier_fails)

corollary pp_all_invariant_operators_stock_fails:
  assumes orbit_classifier_in:
      "pp_classifier (pp_orbit r) \<in> Operators"
    and represented:
      "\<And>S. pp_classifier S \<in> Operators \<Longrightarrow> S \<in> Stock"
  shows "\<not> pp_stock_recombines Stock r"
  using represented[OF orbit_classifier_in]
  by (rule pp_stock_containing_orbit_classifier_fails)

text \<open>
  The last result is the promised broad-invariance negative control.  The classifier
  of an orbit is equivariant, hence invariant at the next type.  Any proposed
  interpretation of Pure that admits all such invariant operators and represents
  their classifier indices in its unary stock is therefore too broad.
\<close>

subsection \<open>A universal closure-code carrier\<close>

datatype pp_uval =
    PUVInd nat
  | PUVProp pp_sem_prop
  | PUVClosure otype otype oterm "pp_uval list"

fun pp_uval_tagged :: "otype \<Rightarrow> pp_uval \<Rightarrow> bool" where
  "pp_uval_tagged Ind (PUVInd n) = True"
| "pp_uval_tagged Prop (PUVProp P) = True"
| "pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (PUVClosure \<sigma>' \<tau>' A env) = (\<sigma> = \<sigma>' \<and> \<tau> = \<tau>')"
| "pp_uval_tagged \<sigma> v = False"

fun pp_uval_holds :: "pp_uval \<Rightarrow> pp_word \<Rightarrow> bool" where
  "pp_uval_holds (PUVProp P) w = (w \<in> P)"
| "pp_uval_holds (PUVInd n) w = False"
| "pp_uval_holds (PUVClosure \<sigma> \<tau> A env) w = False"

fun pp_closure_launch ::
    "pp_uval \<Rightarrow> pp_uval \<Rightarrow> (oterm \<times> pp_uval list) option" where
  "pp_closure_launch (PUVClosure \<sigma> \<tau> A env) x =
      Some (A, x # env)"
| "pp_closure_launch (PUVInd n) x = None"
| "pp_closure_launch (PUVProp P) x = None"

lemma pp_uval_tagged_nonempty:
  "\<exists>v. pp_uval_tagged \<sigma> v"
proof (cases \<sigma>)
  case Ind
  then show ?thesis by (intro exI[of _ "PUVInd 0"]) simp
next
  case Prop
  then show ?thesis by (intro exI[of _ "PUVProp {}"]) simp
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (intro exI[of _ "PUVClosure \<sigma> \<tau> (Var 0) []"]) simp
qed

lemma pp_closure_launch_preserves_tags:
  assumes f: "pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
    and launch: "pp_closure_launch f x = Some (A, env)"
  shows "\<exists>body captured.
    f = PUVClosure \<sigma> \<tau> body captured \<and>
    A = body \<and> env = x # captured"
  using f launch
  by (cases f) auto

text \<open>
  \<open>pp_uval\<close> removes the finite-rank obstruction: the same HOL carrier contains
  closure codes tagged by every object type, and closures recursively contain captured
  values.  The tag predicate is only a raw shape check.  The semantic domains of the
  eventual model must instead be the self-related elements of a type-indexed PER.
\<close>

subsection \<open>The type-indexed PER generated by application\<close>

fun pp_uval_per ::
    "(pp_uval \<Rightarrow> pp_uval \<Rightarrow> pp_uval) \<Rightarrow>
      otype \<Rightarrow> pp_uval \<Rightarrow> pp_uval \<Rightarrow> bool" where
  "pp_uval_per app Ind (PUVInd m) (PUVInd n) = (m = n)"
| "pp_uval_per app Ind x y = False"
| "pp_uval_per app Prop (PUVProp P) (PUVProp Q) = (P = Q)"
| "pp_uval_per app Prop x y = False"
| "pp_uval_per app (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g =
    (pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<and>
     pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<and>
     (\<forall>x y. pp_uval_per app \<sigma> x y \<longrightarrow>
       pp_uval_per app \<tau> (app f x) (app g y)))"

lemma pp_uval_per_symmetric:
  assumes "pp_uval_per app \<sigma> x y"
  shows "pp_uval_per app \<sigma> y x"
  using assms
proof (induction \<sigma> arbitrary: x y)
  case Ind
  then show ?case by (cases x; cases y) simp_all
next
  case Prop
  then show ?case by (cases x; cases y) simp_all
next
  case (Arr \<sigma> \<tau>)
  then show ?case by auto
qed

lemma pp_uval_per_transitive:
  assumes xy: "pp_uval_per app \<sigma> x y"
    and yz: "pp_uval_per app \<sigma> y z"
  shows "pp_uval_per app \<sigma> x z"
  using xy yz
proof (induction \<sigma> arbitrary: x y z)
  case Ind
  then show ?case by (cases x; cases y; cases z) simp_all
next
  case Prop
  then show ?case by (cases x; cases y; cases z) simp_all
next
  case (Arr \<sigma> \<tau>)
  show ?case
  proof (simp only: pp_uval_per.simps, intro conjI allI impI)
    show "pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>) x"
      using Arr.prems by simp
    show "pp_uval_tagged (\<sigma> \<rightarrow>\<^sub>o \<tau>) z"
      using Arr.prems by simp
    fix a c
    assume ac: "pp_uval_per app \<sigma> a c"
    have ca: "pp_uval_per app \<sigma> c a"
      using ac by (rule pp_uval_per_symmetric)
    have aa: "pp_uval_per app \<sigma> a a"
      using ac ca by (rule Arr.IH(1))
    have first:
        "pp_uval_per app \<tau> (app x a) (app y a)"
      using Arr.prems aa by simp
    have second:
        "pp_uval_per app \<tau> (app y a) (app z c)"
      using Arr.prems ac by simp
    show "pp_uval_per app \<tau> (app x a) (app z c)"
      using first second by (rule Arr.IH(2))
  qed
qed

lemma pp_uval_per_implies_tagged:
  assumes "pp_uval_per app \<sigma> x y"
  shows "pp_uval_tagged \<sigma> x \<and> pp_uval_tagged \<sigma> y"
  using assms
  by (cases \<sigma>; cases x; cases y) auto

lemma pp_uval_per_app:
  assumes "pp_uval_per app (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g"
    and "pp_uval_per app \<sigma> x y"
  shows "pp_uval_per app \<tau> (app f x) (app g y)"
  using assms by simp

fun pp_uval_default :: "otype \<Rightarrow> pp_uval" where
  "pp_uval_default Ind = PUVInd 0"
| "pp_uval_default Prop = PUVProp {}"
| "pp_uval_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    PUVClosure \<sigma> \<tau> (Var 0) []"

fun pp_uval_default_app :: "pp_uval \<Rightarrow> pp_uval \<Rightarrow> pp_uval" where
  "pp_uval_default_app (PUVClosure \<sigma> \<tau> A env) x =
    pp_uval_default \<tau>"
| "pp_uval_default_app (PUVInd n) x = PUVInd 0"
| "pp_uval_default_app (PUVProp P) x = PUVInd 0"

lemma pp_uval_default_self_related:
  "pp_uval_per pp_uval_default_app \<sigma>
    (pp_uval_default \<sigma>) (pp_uval_default \<sigma>)"
  by (induction \<sigma>) simp_all

locale pp_closure_PER =
  fixes per :: "otype \<Rightarrow> pp_uval \<Rightarrow> pp_uval \<Rightarrow> bool"
    and app :: "pp_uval \<Rightarrow> pp_uval \<Rightarrow> pp_uval"
  assumes per_symmetric:
      "per \<sigma> x y \<Longrightarrow> per \<sigma> y x"
    and per_transitive:
      "per \<sigma> x y \<Longrightarrow> per \<sigma> y z \<Longrightarrow> per \<sigma> x z"
    and per_implies_tagged:
      "per \<sigma> x y \<Longrightarrow>
        pp_uval_tagged \<sigma> x \<and> pp_uval_tagged \<sigma> y"
    and prop_per:
      "per Prop (PUVProp P) (PUVProp Q) \<longleftrightarrow> P = Q"
    and app_respects_PER:
      "per (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g \<Longrightarrow>
        per \<sigma> x y \<Longrightarrow>
        per \<tau> (app f x) (app g y)"
    and per_nonempty:
      "\<exists>x. per \<sigma> x x"
begin

definition pp_per_dom :: "otype \<Rightarrow> pp_uval \<Rightarrow> bool" where
  "pp_per_dom \<sigma> x \<longleftrightarrow> per \<sigma> x x"

lemma pp_per_dom_nonempty:
  "\<exists>x. pp_per_dom \<sigma> x"
  using per_nonempty unfolding pp_per_dom_def .

lemma pp_per_app_type:
  assumes "pp_per_dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
    and "pp_per_dom \<sigma> x"
  shows "pp_per_dom \<tau> (app f x)"
  using app_respects_PER[OF assms[unfolded pp_per_dom_def]]
  unfolding pp_per_dom_def .

lemma pp_per_prop_extensional:
  assumes "pp_per_dom Prop (PUVProp P)"
    and "pp_per_dom Prop (PUVProp Q)"
  shows "per Prop (PUVProp P) (PUVProp Q) \<longleftrightarrow> P = Q"
  by (rule prop_per)

end

text \<open>
  The following interpretation proves that the representation contract itself is
  consistent.  Its application operation is deliberately only a default operation;
  it is not the term evaluator and therefore is not a central model.
\<close>

interpretation DefaultClosurePER:
  pp_closure_PER
    "pp_uval_per pp_uval_default_app"
    pp_uval_default_app
proof
  show "pp_uval_per pp_uval_default_app \<sigma> x y \<Longrightarrow>
      pp_uval_per pp_uval_default_app \<sigma> y x"
    for \<sigma> x y
    by (rule pp_uval_per_symmetric)
  show "pp_uval_per pp_uval_default_app \<sigma> x y \<Longrightarrow>
      pp_uval_per pp_uval_default_app \<sigma> y z \<Longrightarrow>
      pp_uval_per pp_uval_default_app \<sigma> x z"
    for \<sigma> x y z
    by (rule pp_uval_per_transitive)
  show "pp_uval_per pp_uval_default_app \<sigma> x y \<Longrightarrow>
      pp_uval_tagged \<sigma> x \<and> pp_uval_tagged \<sigma> y"
    for \<sigma> x y
    by (rule pp_uval_per_implies_tagged)
  show "pp_uval_per pp_uval_default_app Prop (PUVProp P) (PUVProp Q)
      \<longleftrightarrow> P = Q"
    for P Q
    by simp
  show "pp_uval_per pp_uval_default_app (\<sigma> \<rightarrow>\<^sub>o \<tau>) f g
      \<Longrightarrow>
      pp_uval_per pp_uval_default_app \<sigma> x y
      \<Longrightarrow>
      pp_uval_per pp_uval_default_app \<tau>
        (pp_uval_default_app f x) (pp_uval_default_app g y)"
    for \<sigma> \<tau> f g x y
    by (rule pp_uval_per_app)
  show "\<exists>x. pp_uval_per pp_uval_default_app \<sigma> x x" for \<sigma>
    using pp_uval_default_self_related by blast
qed

subsection \<open>The quantifier self-call obstruction\<close>

definition pp_quantifier_cycle_body :: oterm where
  "pp_quantifier_cycle_body =
    Forall (Ind \<rightarrow>\<^sub>o Prop) (App (Var 0) (Var 1))"

definition pp_quantifier_cycle_term :: oterm where
  "pp_quantifier_cycle_term = Lam Ind pp_quantifier_cycle_body"

definition pp_quantifier_cycle_closure :: pp_uval where
  "pp_quantifier_cycle_closure =
    PUVClosure Ind Prop pp_quantifier_cycle_body []"

lemma pp_quantifier_cycle_term_typed:
  "[] \<turnstile> pp_quantifier_cycle_term : (Ind \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_quantifier_cycle_term_def pp_quantifier_cycle_body_def
        lookup_def)

lemma pp_quantifier_cycle_closure_tagged:
  "pp_uval_tagged (Ind \<rightarrow>\<^sub>o Prop)
    pp_quantifier_cycle_closure"
  by (simp add: pp_quantifier_cycle_closure_def)

lemma pp_quantifier_cycle_closure_self_related:
  assumes prop_total:
      "\<And>n. pp_uval_tagged Prop
        (app pp_quantifier_cycle_closure (PUVInd n))"
  shows "pp_uval_per app (Ind \<rightarrow>\<^sub>o Prop)
    pp_quantifier_cycle_closure pp_quantifier_cycle_closure"
proof (simp add: pp_quantifier_cycle_closure_tagged, intro allI impI)
  fix x y
  assume xy: "pp_uval_per app Ind x y"
  then obtain n where x: "x = PUVInd n" and y: "y = PUVInd n"
    by (cases x; cases y) auto
  obtain P where
      "app pp_quantifier_cycle_closure (PUVInd n) = PUVProp P"
    using prop_total[of n]
    by (cases "app pp_quantifier_cycle_closure (PUVInd n)") auto
  then show "pp_uval_per app Prop
      (app pp_quantifier_cycle_closure x)
      (app pp_quantifier_cycle_closure y)"
    by (simp add: x y)
qed

text \<open>
  These lemmas expose a circularity in the proposed closure evaluator.  Write
  \<open>F\<close> for \<open>\<lambda>a. \<forall>P\<^sub>i\<^sub>\<rightarrow>\<^sub>p. P a\<close>.  It is a closed term of type
  \<open>Ind \<rightarrow>\<^sub>o Prop\<close>.  Any tag-correct total application operation makes its
  closure self-related at that arrow type, so the closure belongs to the PER
  domain over which its own universal quantifier must range.  Evaluating
  \<open>F a\<close> and choosing that very closure as the quantified predicate returns
  the identical call \<open>F a\<close>.  Hence the natural evaluator is not structurally
  recursive or well-founded.  Strong normalization of the simply typed term
  calculus does not remove this semantic self-call.

  There is a second, independent circularity.  The universal-quantifier clause
  needs the diagonal of \<open>pp_uval_per app \<sigma>\<close>, but that PER is itself defined
  using \<open>app\<close>.  The occurrence is not monotone: the quantified domain occurs
  in the antecedent of the universal clause, and an arrow PER occurs in the
  antecedent of its compatibility implication.  Consequently neither primitive
  recursion nor an elementary least-fixed-point construction supplies the
  requested classical evaluator.

  The next honest construction must therefore replace closure-generated
  domains by preconstructed typed domains with genuine function data at arrow
  types.  Application and quantifier ranges are then available before term
  interpretation is defined.  A HOL-ZF universe supplies such a carrier
  directly but makes the result relative to its additional set-theoretic
  assumptions.  A pure-HOL universal-domain construction would avoid that
  qualification but requires a separate representation theorem.  No such
  stronger choice is made in this theory.
\<close>

end
