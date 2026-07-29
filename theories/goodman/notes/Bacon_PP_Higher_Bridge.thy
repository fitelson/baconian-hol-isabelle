theory Bacon_PP_Higher_Bridge
  imports
    Bacon_PP_Oterm_Bridge
    "Higher_Order_Metaphysics_PP.Bacon_PP_TypeCoherence"
begin

section \<open>Extending the bridge above the propositional fragment\<close>

text \<open>
  The propositional bridge gives \<open>Lam\<close> and \<open>App\<close> the value \<open>{}\<close>, so it says nothing
  about higher types.  This theory lifts that restriction as far as it can be lifted,
  and is explicit about where the ceiling is and why.

  A word first on what the type class does and does not do here.  \<open>pp_dom\<close> supplies,
  at every object type, a carrier, the local equivalence and the conjugation, and the
  coherence theorems of \<open>Bacon_PP_TypeCoherence\<close> hold at all of them.  What it does
  not supply is a single HOL type in which values of \emph{different} object types can
  sit together, and an evaluation function on \<open>oterm\<close> needs exactly that, because a
  de Bruijn environment mixes types.  No HOL datatype has values at unboundedly many
  type levels.  So the class and the bridge are complementary: the class gives
  type-indexed coherence with no evaluation function, the bridge gives an evaluation
  function up to a fixed level.

  Here the level is two, which is where the question lives: \<open>Prop\<close>, \<open>Prop \<rightarrow> Prop\<close>
  where the pure stock sits, and \<open>(Prop \<rightarrow> Prop) \<rightarrow> Prop\<close> where \<open>Pure\<^bsub>t \<rightarrow> t\<^esub>\<close> itself
  sits.  The universe is tied back to the class by \<open>pp_carrier\<close>: the operator level
  is Bacon's local function domain, which is the class carrier at \<open>pp_base \<Rightarrow>
  pp_base\<close>.
\<close>

subsection \<open>Closure properties inherited by the \<open>Pure\<close>-closure\<close>

lemma pp_pclosure_UNIV: "UNIV \<in> pp_pclosure G"
proof -
  have "\<Inter> {} \<in> pp_pclosure G"
    by (rule p_Inter) simp
  then show ?thesis by simp
qed

lemma pp_pclosure_empty: "{} \<in> pp_pclosure G"
proof -
  have "- UNIV \<in> pp_pclosure G"
    using pp_pclosure_UNIV by (rule p_compl)
  then show ?thesis by simp
qed

lemma pp_pclosure_Int:
  assumes X: "X \<in> pp_pclosure G" and Y: "Y \<in> pp_pclosure G"
  shows "X \<inter> Y \<in> pp_pclosure G"
proof -
  have "\<And>Z. Z \<in> {X, Y} \<Longrightarrow> Z \<in> pp_pclosure G"
    using X Y by blast
  then have "\<Inter> {X, Y} \<in> pp_pclosure G" by (rule p_Inter)
  moreover have "\<Inter> {X, Y} = X \<inter> Y" by simp
  ultimately show ?thesis by simp
qed

lemma pp_pclosure_Un:
  assumes X: "X \<in> pp_pclosure G" and Y: "Y \<in> pp_pclosure G"
  shows "X \<union> Y \<in> pp_pclosure G"
proof -
  have "- X \<inter> - Y \<in> pp_pclosure G"
    using p_compl[OF X] p_compl[OF Y] by (rule pp_pclosure_Int)
  then have compl: "- (- X \<inter> - Y) \<in> pp_pclosure G"
    by (rule p_compl)
  have eq: "- (- X \<inter> - Y) = X \<union> Y" by auto
  show ?thesis using compl unfolding eq .
qed

lemma pp_pclosure_Union:
  assumes S: "\<And>X. X \<in> S \<Longrightarrow> X \<in> pp_pclosure G"
  shows "\<Union> S \<in> pp_pclosure G"
proof -
  have "\<And>Y. Y \<in> uminus ` S \<Longrightarrow> Y \<in> pp_pclosure G"
    using S p_compl by blast
  then have "\<Inter> (uminus ` S) \<in> pp_pclosure G"
    by (rule p_Inter)
  then have "- (\<Inter> (uminus ` S)) \<in> pp_pclosure G"
    by (rule p_compl)
  moreover have "- (\<Inter> (uminus ` S)) = \<Union> S" by auto
  ultimately show ?thesis by simp
qed

lemma pp_pclosure_operator_equal:
  assumes A: "A \<in> pp_pclosure G" and B: "B \<in> pp_pclosure G"
  shows "pp_operator_equal A B \<in> pp_pclosure G"
proof -
  have "A \<inter> B \<in> pp_pclosure G" using A B by (rule pp_pclosure_Int)
  moreover have "- A \<inter> - B \<in> pp_pclosure G"
    using p_compl[OF A] p_compl[OF B] by (rule pp_pclosure_Int)
  ultimately have "(A \<inter> B) \<union> (- A \<inter> - B) \<in> pp_pclosure G"
    by (rule pp_pclosure_Un)
  then have "pp_sem_box ((A \<inter> B) \<union> (- A \<inter> - B)) \<in> pp_pclosure G"
    by (rule p_box)
  then show ?thesis
    by (simp add: pp_operator_equal_is_boxed_biconditional)
qed

lemma pp_qclosure_subset_pclosure:
  assumes "X \<in> pp_qclosure G"
  shows "X \<in> pp_pclosure G"
  using assms
proof (induct rule: pp_qclosure.induct)
  case (q_base X) then show ?case by (rule p_base)
next
  case (q_compl X)
  then have "X \<in> pp_pclosure G" by simp
  then show ?case by (rule p_compl)
next
  case (q_box X)
  then have "X \<in> pp_pclosure G" by simp
  then show ?case by (rule p_box)
next
  case (q_Inter S) then show ?case by (blast intro: p_Inter)
qed

subsection \<open>A universe up to level two\<close>

datatype pp_v =
    VP pp_sem_prop
  | VF "pp_sem_prop \<Rightarrow> pp_sem_prop"
  | VG "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop"
  | VBad

fun unVP :: "pp_v \<Rightarrow> pp_sem_prop" where
  "unVP (VP X) = X"
| "unVP _ = {}"

text \<open>
  Equality must inspect values at their object-language type.  In particular,
  equality at a function type is local extensional equality over the
  corresponding Henkin domain; it is not proposition equality after coercing
  non-propositional values to \<open>{}\<close>.
\<close>

fun pp_v_equal ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      otype \<Rightarrow> pp_v \<Rightarrow> pp_v \<Rightarrow> pp_sem_prop"
  where
  "pp_v_equal DP DF Prop (VP X) (VP Y) =
    pp_operator_equal X Y"
| "pp_v_equal DP DF (\<sigma> \<rightarrow>\<^sub>o \<tau>) (VF F) (VF H) =
    (if \<sigma> = Prop \<and> \<tau> = Prop
     then \<Inter> ((\<lambda>X. pp_operator_equal (F X) (H X)) ` DP)
     else {})"
| "pp_v_equal DP DF (\<sigma> \<rightarrow>\<^sub>o \<tau>) (VG F) (VG H) =
    (if \<sigma> = (Prop \<rightarrow>\<^sub>o Prop) \<and> \<tau> = Prop
     then \<Inter> ((\<lambda>X. pp_operator_equal (F X) (H X)) ` DF)
     else {})"
| "pp_v_equal DP DF ty v w = {}"

lemma pp_v_equal_unary_root_iff:
  "[] \<in> pp_v_equal DP DF (Prop \<rightarrow>\<^sub>o Prop) (VF F) (VF H)
    \<longleftrightarrow> (\<forall>X \<in> DP. F X = H X)"
  by (auto simp: pp_operator_equal_def pp_view_def set_eq_iff)

lemma pp_v_equal_classifier_root_iff:
  "[] \<in> pp_v_equal DP DF
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) (VG F) (VG H)
    \<longleftrightarrow> (\<forall>X \<in> DF. F X = H X)"
  by (auto simp: pp_operator_equal_def pp_view_def set_eq_iff)

subsection \<open>Good values\<close>

definition pp_fok ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool"
  where
  "pp_fok G F \<longleftrightarrow>
    F \<in> pp_fclosure G \<and>
    (\<forall>X \<in> pp_pclosure G. F X \<in> pp_pclosure G)"

definition pp_gok ::
    "pp_sem_prop set \<Rightarrow>
      ((pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop) \<Rightarrow> bool"
  where
  "pp_gok G H \<longleftrightarrow> (\<forall>F. pp_fok G F \<longrightarrow> H F \<in> pp_pclosure G)"

fun pp_v_ok :: "pp_sem_prop set \<Rightarrow> pp_v \<Rightarrow> bool" where
  "pp_v_ok G (VP X) = (X \<in> pp_pclosure G)"
| "pp_v_ok G (VF F) = pp_fok G F"
| "pp_v_ok G (VG H) = pp_gok G H"
| "pp_v_ok G VBad = True"

lemma pp_v_ok_unVP:
  assumes "pp_v_ok G v"
  shows "unVP v \<in> pp_pclosure G"
  using assms pp_pclosure_empty by (cases v) auto

lemma pp_v_equal_ok:
  assumes v: "pp_v_ok G v"
    and w: "pp_v_ok G w"
    and DP: "\<And>X. X \<in> DP \<Longrightarrow> X \<in> pp_pclosure G"
    and DF: "\<And>F. F \<in> DF \<Longrightarrow> pp_fok G F"
  shows "pp_v_equal DP DF ty v w \<in> pp_pclosure G"
  using v w DP DF
  by (cases ty; cases v; cases w)
    (auto simp: pp_fok_def pp_gok_def pp_pclosure_empty
      split: otype.splits
      intro!: p_Inter intro: pp_pclosure_operator_equal)

text \<open>
  The purity operator is a good level-two value.  This is where the induction of
  \<open>Bacon_PP_Cone_Determined\<close> is used: an operator of the function closure is
  cone-determined, so the \<open>p_pure\<close> rule applies to it.
\<close>

theorem pp_gok_purity: "pp_gok G pp_purity_operator"
  unfolding pp_gok_def
proof (intro allI impI)
  fix F
  assume "pp_fok G F"
  then have "F \<in> pp_fclosure G"
    unfolding pp_fok_def by simp
  then show "pp_purity_operator F \<in> pp_pclosure G"
    by (rule pp_fclosure_purity_in_pclosure)
qed

text \<open>
  Purity at type \<open>Prop\<close> is non-contingency, since the invariant propositions are
  exactly \<open>{}\<close> and \<open>UNIV\<close>.  It is a good level-one value.
\<close>

lemma pp_decided_in_fclosure: "pp_decided \<in> pp_fclosure G"
proof -
  have box_id: "(\<lambda>P. pp_sem_box P) \<in> pp_fclosure G"
    using f_id by (rule f_box)
  have "(\<lambda>P. - P) \<in> pp_fclosure G"
    using f_id by (rule f_compl)
  then have box_neg: "(\<lambda>P. pp_sem_box (- P)) \<in> pp_fclosure G"
    by (rule f_box)
  have inc: "(\<lambda>P. pp_sem_box P \<union> pp_sem_box (- P)) \<in> pp_fclosure G"
    using box_id box_neg by (rule pp_fclosure_Unop)
  have eq: "pp_decided = (\<lambda>P. pp_sem_box P \<union> pp_sem_box (- P))"
    by (rule ext) (simp add: pp_decided_def)
  show ?thesis using inc unfolding eq .
qed

lemma pp_fok_decided: "pp_fok G pp_decided"
  unfolding pp_fok_def
proof
  show "pp_decided \<in> pp_fclosure G"
    by (rule pp_decided_in_fclosure)
next
  show "\<forall>X \<in> pp_pclosure G. pp_decided X \<in> pp_pclosure G"
  proof
    fix X
    assume X: "X \<in> pp_pclosure G"
    have "pp_sem_box X \<in> pp_pclosure G" using X by (rule p_box)
    moreover have "pp_sem_box (- X) \<in> pp_pclosure G"
      using p_compl[OF X] by (rule p_box)
    ultimately show "pp_decided X \<in> pp_pclosure G"
      by (simp add: pp_decided_def pp_pclosure_Un)
  qed
qed

text \<open>
  Fundamentality is local identity with the seed, and is a good level-one value
  whenever the seed is in the closure.
\<close>

lemma pp_fok_fundamental:
  assumes r: "r \<in> pp_qclosure G"
  shows "pp_fok G (\<lambda>P. pp_operator_equal P r)"
  unfolding pp_fok_def
proof
  have "pp_cone_det_prop G r"
    using r by (rule pp_qclosure_cone_det)
  then have cr: "(\<lambda>P. r) \<in> pp_fclosure G" by (rule f_const)
  have "(\<lambda>P. pp_operator_equal ((\<lambda>P. P) P) ((\<lambda>P. r) P))
      \<in> pp_fclosure G"
    using f_id cr by (rule pp_fclosure_operator_equalop)
  then show "(\<lambda>P. pp_operator_equal P r) \<in> pp_fclosure G"
    by simp
next
  show "\<forall>X \<in> pp_pclosure G. pp_operator_equal X r \<in> pp_pclosure G"
    using r pp_qclosure_subset_pclosure
    by (blast intro: pp_pclosure_operator_equal)
qed

subsection \<open>The higher-type valuation\<close>

fun pp_veval ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      (string \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop \<Rightarrow>
      oterm \<Rightarrow> pp_v list \<Rightarrow> pp_v"
  where
  "pp_veval DP DF V r (Var n) env =
     (if n < length env then env ! n else VBad)"
| "pp_veval DP DF V r (Const c ty) env =
     (if ty = (Prop \<rightarrow>\<^sub>o Prop) \<and> c = pp_pure_name then VF pp_decided
      else if ty = (Prop \<rightarrow>\<^sub>o Prop) \<and> c = pp_fun_name
        then VF (\<lambda>P. pp_operator_equal P r)
      else if ty = ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) \<and> c = pp_pure_name
        then VG pp_purity_operator
      else if ty = Prop then VP (V c)
      else VBad)"
| "pp_veval DP DF V r (Neg A) env =
     VP (- unVP (pp_veval DP DF V r A env))"
| "pp_veval DP DF V r (Conj A B) env =
     VP (unVP (pp_veval DP DF V r A env) \<inter>
        unVP (pp_veval DP DF V r B env))"
| "pp_veval DP DF V r (Disj A B) env =
     VP (unVP (pp_veval DP DF V r A env) \<union>
        unVP (pp_veval DP DF V r B env))"
| "pp_veval DP DF V r (Imp A B) env =
     VP (- unVP (pp_veval DP DF V r A env) \<union>
        unVP (pp_veval DP DF V r B env))"
| "pp_veval DP DF V r (Eq ty A B) env =
     VP (pp_v_equal DP DF ty
        (pp_veval DP DF V r A env)
        (pp_veval DP DF V r B env))"
| "pp_veval DP DF V r (Forall ty A) env =
     VP (if ty = Prop
         then \<Inter> ((\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP)
         else if ty = (Prop \<rightarrow>\<^sub>o Prop)
         then \<Inter> ((\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF)
         else {})"
| "pp_veval DP DF V r (Exists ty A) env =
     VP (if ty = Prop
         then \<Union> ((\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP)
         else if ty = (Prop \<rightarrow>\<^sub>o Prop)
         then \<Union> ((\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF)
         else {})"
| "pp_veval DP DF V r (Lam ty A) env = VBad"
| "pp_veval DP DF V r (App f a) env =
     (case (pp_veval DP DF V r f env, pp_veval DP DF V r a env) of
        (VF F, VP X) \<Rightarrow> VP (F X)
      | (VG H, VF F) \<Rightarrow> VP (H F)
      | _ \<Rightarrow> VBad)"

subsection \<open>The induction\<close>

theorem pp_veval_ok:
  assumes DP: "\<And>X. X \<in> DP \<Longrightarrow> X \<in> pp_pclosure G"
    and DF: "\<And>F. F \<in> DF \<Longrightarrow> pp_fok G F"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
    and seed: "r \<in> pp_qclosure G"
  shows "\<And>env. (\<And>v. v \<in> set env \<Longrightarrow> pp_v_ok G v) \<Longrightarrow>
    pp_v_ok G (pp_veval DP DF V r t env)"
proof (induct t)
  case (Var n)
  then show ?case by (simp add: nth_mem)
next
  case (Const c ty)
  show ?case
    using Val seed pp_fok_decided pp_gok_purity
      pp_fok_fundamental pp_qclosure_subset_pclosure
    by simp
next
  case (Neg A)
  then show ?case
    by (simp add: p_compl pp_v_ok_unVP)
next
  case (Conj A B)
  then show ?case
    by (simp add: pp_pclosure_Int pp_v_ok_unVP)
next
  case (Disj A B)
  then show ?case
    by (simp add: pp_pclosure_Un pp_v_ok_unVP)
next
  case (Imp A B)
  then show ?case
    by (simp add: pp_pclosure_Un p_compl pp_v_ok_unVP)
next
  case (Eq ty A B)
  have okA: "pp_v_ok G (pp_veval DP DF V r A env)"
    using Eq.prems by (rule Eq.hyps(1))
  have okB: "pp_v_ok G (pp_veval DP DF V r B env)"
    using Eq.prems by (rule Eq.hyps(2))
  show ?case
    using pp_v_equal_ok[OF okA okB DP DF] by simp
next
  case (Lam ty A)
  show ?case by simp
next
  case (App f a)
  have okf: "pp_v_ok G (pp_veval DP DF V r f env)"
    using App.prems by (rule App.hyps(1))
  have oka: "pp_v_ok G (pp_veval DP DF V r a env)"
    using App.prems by (rule App.hyps(2))
  show ?case
  proof (cases "pp_veval DP DF V r f env")
    case (VP X1)
    then show ?thesis by simp
  next
    case eqf: (VF F)
    show ?thesis
    proof (cases "pp_veval DP DF V r a env")
      case (VP X)
      have "pp_fok G F" using okf eqf by simp
      then have "F X \<in> pp_pclosure G"
        using oka \<open>pp_veval DP DF V r a env = VP X\<close>
        by (simp add: pp_fok_def)
      then show ?thesis
        using eqf \<open>pp_veval DP DF V r a env = VP X\<close> by simp
    next
      case (VF F')
      then show ?thesis using eqf by simp
    next
      case (VG H')
      then show ?thesis using eqf by simp
    next
      case VBad
      then show ?thesis using eqf by simp
    qed
  next
    case eqg: (VG H)
    show ?thesis
    proof (cases "pp_veval DP DF V r a env")
      case (VP X)
      then show ?thesis using eqg by simp
    next
      case (VF F)
      have "pp_gok G H" using okf eqg by simp
      then have "H F \<in> pp_pclosure G"
        using oka \<open>pp_veval DP DF V r a env = VF F\<close>
        by (simp add: pp_gok_def)
      then show ?thesis
        using eqg \<open>pp_veval DP DF V r a env = VF F\<close> by simp
    next
      case (VG H')
      then show ?thesis using eqg by simp
    next
      case VBad
      then show ?thesis using eqg by simp
    qed
  next
    case VBad
    then show ?thesis by simp
  qed
next
  case (Forall ty A)
  show ?case
  proof (cases "ty = Prop")
    case True
    have "\<And>Y. Y \<in> (\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP
        \<Longrightarrow> Y \<in> pp_pclosure G"
    proof -
      fix Y
      assume "Y \<in> (\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP"
      then obtain X where X: "X \<in> DP"
        and Y: "Y = unVP (pp_veval DP DF V r A (VP X # env))" by blast
      have "\<And>v. v \<in> set (VP X # env) \<Longrightarrow> pp_v_ok G v"
        using X DP Forall.prems by auto
      then have "pp_v_ok G (pp_veval DP DF V r A (VP X # env))"
        by (rule Forall.hyps)
      then show "Y \<in> pp_pclosure G" using Y by (simp add: pp_v_ok_unVP)
    qed
    then show ?thesis using True by (simp add: p_Inter)
  next
    case notP: False
    show ?thesis
    proof (cases "ty = (Prop \<rightarrow>\<^sub>o Prop)")
      case True
      have "\<And>Y. Y \<in> (\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF
          \<Longrightarrow> Y \<in> pp_pclosure G"
      proof -
        fix Y
        assume "Y \<in> (\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF"
        then obtain F where F: "F \<in> DF"
          and Y: "Y = unVP (pp_veval DP DF V r A (VF F # env))" by blast
        have "\<And>v. v \<in> set (VF F # env) \<Longrightarrow> pp_v_ok G v"
          using F DF Forall.prems by auto
        then have "pp_v_ok G (pp_veval DP DF V r A (VF F # env))"
          by (rule Forall.hyps)
        then show "Y \<in> pp_pclosure G" using Y by (simp add: pp_v_ok_unVP)
      qed
      then show ?thesis using notP True by (simp add: p_Inter)
    next
      case False
      then show ?thesis using notP pp_pclosure_empty by simp
    qed
  qed
next
  case (Exists ty A)
  show ?case
  proof (cases "ty = Prop")
    case True
    have "\<And>Y. Y \<in> (\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP
        \<Longrightarrow> Y \<in> pp_pclosure G"
    proof -
      fix Y
      assume "Y \<in> (\<lambda>X. unVP (pp_veval DP DF V r A (VP X # env))) ` DP"
      then obtain X where X: "X \<in> DP"
        and Y: "Y = unVP (pp_veval DP DF V r A (VP X # env))" by blast
      have "\<And>v. v \<in> set (VP X # env) \<Longrightarrow> pp_v_ok G v"
        using X DP Exists.prems by auto
      then have "pp_v_ok G (pp_veval DP DF V r A (VP X # env))"
        by (rule Exists.hyps)
      then show "Y \<in> pp_pclosure G" using Y by (simp add: pp_v_ok_unVP)
    qed
    then show ?thesis using True by (simp add: pp_pclosure_Union)
  next
    case notP: False
    show ?thesis
    proof (cases "ty = (Prop \<rightarrow>\<^sub>o Prop)")
      case True
      have "\<And>Y. Y \<in> (\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF
          \<Longrightarrow> Y \<in> pp_pclosure G"
      proof -
        fix Y
        assume "Y \<in> (\<lambda>F. unVP (pp_veval DP DF V r A (VF F # env))) ` DF"
        then obtain F where F: "F \<in> DF"
          and Y: "Y = unVP (pp_veval DP DF V r A (VF F # env))" by blast
        have "\<And>v. v \<in> set (VF F # env) \<Longrightarrow> pp_v_ok G v"
          using F DF Exists.prems by auto
        then have "pp_v_ok G (pp_veval DP DF V r A (VF F # env))"
          by (rule Exists.hyps)
        then show "Y \<in> pp_pclosure G" using Y by (simp add: pp_v_ok_unVP)
      qed
      then show ?thesis using notP True by (simp add: pp_pclosure_Union)
    next
      case False
      then show ?thesis using notP pp_pclosure_empty by simp
    qed
  qed
qed

corollary pp_veval_prop_in_pclosure:
  assumes DP: "\<And>X. X \<in> DP \<Longrightarrow> X \<in> pp_pclosure G"
    and DF: "\<And>F. F \<in> DF \<Longrightarrow> pp_fok G F"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
    and seed: "r \<in> pp_qclosure G"
    and env: "\<And>v. v \<in> set env \<Longrightarrow> pp_v_ok G v"
  shows "unVP (pp_veval DP DF V r t env) \<in> pp_pclosure G"
  using pp_veval_ok[OF DP DF Val seed env] by (rule pp_v_ok_unVP)

subsection \<open>Tying the operator level to the class carrier\<close>

text \<open>
  The level-one domain of the universe is Bacon's local function domain, which is the
  carrier of the type class at \<open>pp_base \<Rightarrow> pp_base\<close>.  So the universe is not an
  alternative to the class; it is the class's carriers at the first two levels, made
  into a single HOL type so that an evaluation function can exist.
\<close>

theorem pp_fclosure_is_class_carrier:
  assumes "F \<in> pp_fclosure G"
  shows "pb_up F \<in> (pp_carrier :: (pp_base \<Rightarrow> pp_base) set)"
  using pp_fclosure_member[OF assms]
  by (simp add: pp_carrier_fun_base_iff)

subsection \<open>The ceiling, and why it is there\<close>

text \<open>
  Covered.  Application at both levels; quantification at \<open>Prop\<close> and at
  \<open>Prop \<rightarrow> Prop\<close>, the type where the pure stock lives; \<open>Pure\<close> at \<open>Prop\<close>, which is
  non-contingency since the invariant propositions are the extremes; and \<open>Pure\<close> at
  \<open>Prop \<rightarrow> Prop\<close>, which is \<open>pp_purity_operator\<close>.  Since a variable bound by a
  \<open>Prop \<rightarrow> Prop\<close> quantifier may be fed to \<open>Pure\<^bsub>Prop \<rightarrow> Prop\<^esub>\<close> and the result fed to
  \<open>Pure\<^bsub>Prop\<^esub>\<close>, iterated \<open>Pure\<close> is inside the fragment, which the propositional bridge
  could not reach.  For all of it, denotations lie in \<open>pp_pclosure G\<close>, so
  \<open>pp_pure_seed_decision_basis\<close> applies.

  Not covered, and there are two quite different reasons, which should not be run
  together.

  First, a design limit rather than a hard one.  \<open>Lam\<close> is left uninterpreted here.
  Certifying an operator built by abstraction requires showing it lies in
  \<open>pp_fclosure\<close>, and the natural induction breaks at \<open>App\<close>: an application whose
  operator and whose argument both vary with the abstracted variable is not covered by
  the operator closure, which has no application rule.  Operators therefore enter only
  through the domain \<open>DF\<close> and through the constants.  The propositional bridge does
  certify abstractions, by \<open>pp_eval_abstract_in_fclosure\<close>, so the two bridges are
  complementary: that one has \<open>Lam\<close> but no higher types, this one has higher types but
  no \<open>Lam\<close>.  Closing the overlap needs an operator closure with an application rule,
  which is a real piece of work and is not done.

  Second, a hard limit.  The target PP instance is
  \<open>Pure\<^bsub>(t \<rightarrow> t) \<rightarrow> Prop\<^esub> (Pure\<^bsub>t \<rightarrow> t\<^esub>)\<close>, whose outer constant lives at
  \<open>((Prop \<rightarrow> Prop) \<rightarrow> Prop) \<rightarrow> Prop\<close>, one level above this universe.  That particular
  level is a mechanical extension --- one more constructor and one more group of
  clauses.  Adding \emph{all} levels is not, and cannot be done this way: a HOL
  datatype has values at only finitely many type levels, while the object language has
  terms at unboundedly many.

  So the remaining gap is now precise.  Any fixed instance of the question can be
  reached by extending the universe far enough.  A statement quantifying over all
  object types cannot be, and would need either a set-theoretic model of the type
  hierarchy or a class-indexed family of evaluation functions in place of a single
  one.  The type class supplies the type-indexed coherence side of that already; what
  it cannot supply, and what no HOL type can, is the single evaluation function such a
  statement would have to quantify over.
\<close>

end
