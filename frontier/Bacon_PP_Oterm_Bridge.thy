theory Bacon_PP_Oterm_Bridge
  imports Bacon_PP_Cone_Determined
begin

section \<open>Bridging the semantic closures to the \<open>oterm\<close> syntax\<close>

text \<open>
  Everything so far has been an induction over \emph{semantic} generating operations.
  This theory connects those inductions to the project's deep-embedded syntax, by
  giving \<open>oterm\<close> an M-set valuation and proving that denotations land in the
  closures.

  The valuation interprets the fragment the arguments need: variables, propositional
  constants, the Boolean connectives, object-language identity, and quantification at
  \<open>Prop\<close>.  The modality needs no clause of its own, since \<open>Bacon_Modal\<close> defines
  \<open>\<box>A\<close> as \<open>Eq Prop A ObjTrue\<close> and the identity clause already delivers it.
  Abstraction and application are given the value \<open>{}\<close>: this is a deliberate
  under-interpretation, not a claim about them, and it is harmless for the theorems
  below because \<open>{}\<close> lies in every closure.

  Two inductions are carried out over \<open>oterm\<close>.  The first says a denotation is in the
  propositional closure.  The second, which is the one the \<open>Pure\<close> results need, says
  that abstracting a de Bruijn position out of a denotation yields an operator in the
  function closure --- hence cone-determined, hence eligible for the \<open>p_pure\<close> rule.
  Both are unconditional on the term, precisely because the uninterpreted constructs
  default into the closure.
\<close>

subsection \<open>Closure under the remaining set operations\<close>

lemma pp_qclosure_UNIV: "UNIV \<in> pp_qclosure G"
proof -
  have "\<Inter> {} \<in> pp_qclosure G"
    by (rule q_Inter) simp
  then show ?thesis by simp
qed

lemma pp_qclosure_empty: "{} \<in> pp_qclosure G"
proof -
  have "- UNIV \<in> pp_qclosure G"
    using pp_qclosure_UNIV by (rule q_compl)
  then show ?thesis by simp
qed

lemma pp_qclosure_Union:
  assumes S: "\<And>X. X \<in> S \<Longrightarrow> X \<in> pp_qclosure G"
  shows "\<Union> S \<in> pp_qclosure G"
proof -
  have "\<And>Y. Y \<in> uminus ` S \<Longrightarrow> Y \<in> pp_qclosure G"
    using S q_compl by blast
  then have "\<Inter> (uminus ` S) \<in> pp_qclosure G"
    by (rule q_Inter)
  then have "- (\<Inter> (uminus ` S)) \<in> pp_qclosure G"
    by (rule q_compl)
  moreover have "- (\<Inter> (uminus ` S)) = \<Union> S"
    by auto
  ultimately show ?thesis by simp
qed

subsection \<open>The valuation\<close>

fun pp_eval ::
    "pp_sem_prop set \<Rightarrow> (string \<Rightarrow> pp_sem_prop) \<Rightarrow>
      oterm \<Rightarrow> pp_sem_prop list \<Rightarrow> pp_sem_prop"
  where
  "pp_eval Dom V (Var n) env =
     (if n < length env then env ! n else {})"
| "pp_eval Dom V (Const c ty) env = V c"
| "pp_eval Dom V (Neg A) env = - pp_eval Dom V A env"
| "pp_eval Dom V (Conj A B) env =
     pp_eval Dom V A env \<inter> pp_eval Dom V B env"
| "pp_eval Dom V (Disj A B) env =
     pp_eval Dom V A env \<union> pp_eval Dom V B env"
| "pp_eval Dom V (Imp A B) env =
     - pp_eval Dom V A env \<union> pp_eval Dom V B env"
| "pp_eval Dom V (Eq ty A B) env =
     pp_operator_equal (pp_eval Dom V A env) (pp_eval Dom V B env)"
| "pp_eval Dom V (Forall ty A) env =
     \<Inter> ((\<lambda>X. pp_eval Dom V A (X # env)) ` Dom)"
| "pp_eval Dom V (Exists ty A) env =
     \<Union> ((\<lambda>X. pp_eval Dom V A (X # env)) ` Dom)"
| "pp_eval Dom V (Lam ty A) env = {}"
| "pp_eval Dom V (App f a) env = {}"

text \<open>
  The modality is not a primitive of the syntax, and needs no clause: it is identity
  with \<open>ObjTrue\<close>, and the valuation computes it correctly.
\<close>

lemma pp_eval_ObjTrue:
  assumes "Dom \<noteq> {}"
  shows "pp_eval Dom V ObjTrue env = UNIV"
proof -
  have "pp_eval Dom V ObjTrue env =
      \<Inter> ((\<lambda>X. - X \<union> X) ` Dom)"
    by (simp add: ObjTrue_def)
  also have "... = UNIV"
    using assms by auto
  finally show ?thesis .
qed

theorem pp_eval_ObjBox:
  assumes "Dom \<noteq> {}"
  shows "pp_eval Dom V (\<box>\<^sub>o A) env =
    pp_sem_box (pp_eval Dom V A env)"
proof -
  have "pp_eval Dom V (\<box>\<^sub>o A) env =
      pp_operator_equal (pp_eval Dom V A env) UNIV"
    by (simp add: ObjBox_def pp_eval_ObjTrue[OF assms])
  also have "... = pp_sem_box (pp_eval Dom V A env)"
    by (auto simp: pp_operator_equal_def pp_sem_box_def)
  finally show ?thesis .
qed

subsection \<open>Denotations lie in the propositional closure\<close>

theorem pp_eval_in_qclosure:
  assumes Dom: "\<And>X. X \<in> Dom \<Longrightarrow> X \<in> pp_qclosure G"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
  shows "\<And>env. (\<And>X. X \<in> set env \<Longrightarrow> X \<in> pp_qclosure G) \<Longrightarrow>
    pp_eval Dom V t env \<in> pp_qclosure G"
proof (induct t)
  case (Var n)
  then show ?case
    using pp_qclosure_empty by (simp add: nth_mem)
next
  case (Const c ty)
  then show ?case by (simp add: Val)
next
  case (App f a)
  then show ?case by (simp add: pp_qclosure_empty)
next
  case (Lam ty A)
  then show ?case by (simp add: pp_qclosure_empty)
next
  case (Eq ty A B)
  then show ?case
    by (simp add: pp_qclosure_operator_equal)
next
  case (Neg A)
  then show ?case by (simp add: q_compl)
next
  case (Conj A B)
  then show ?case by (simp add: pp_qclosure_Int)
next
  case (Disj A B)
  then show ?case by (simp add: pp_qclosure_Un)
next
  case (Imp A B)
  then show ?case by (simp add: pp_qclosure_Un q_compl)
next
  case (Forall ty A)
  have "\<And>Y. Y \<in> (\<lambda>X. pp_eval Dom V A (X # env)) ` Dom \<Longrightarrow>
      Y \<in> pp_qclosure G"
  proof -
    fix Y
    assume "Y \<in> (\<lambda>X. pp_eval Dom V A (X # env)) ` Dom"
    then obtain X where X: "X \<in> Dom"
      and Y: "Y = pp_eval Dom V A (X # env)" by blast
    have "\<And>Z. Z \<in> set (X # env) \<Longrightarrow> Z \<in> pp_qclosure G"
      using X Dom Forall.prems by auto
    then have "pp_eval Dom V A (X # env) \<in> pp_qclosure G"
      by (rule Forall.hyps)
    then show "Y \<in> pp_qclosure G" using Y by simp
  qed
  then show ?case by (simp add: q_Inter)
next
  case (Exists ty A)
  have "\<And>Y. Y \<in> (\<lambda>X. pp_eval Dom V A (X # env)) ` Dom \<Longrightarrow>
      Y \<in> pp_qclosure G"
  proof -
    fix Y
    assume "Y \<in> (\<lambda>X. pp_eval Dom V A (X # env)) ` Dom"
    then obtain X where X: "X \<in> Dom"
      and Y: "Y = pp_eval Dom V A (X # env)" by blast
    have "\<And>Z. Z \<in> set (X # env) \<Longrightarrow> Z \<in> pp_qclosure G"
      using X Dom Exists.prems by auto
    then have "pp_eval Dom V A (X # env) \<in> pp_qclosure G"
      by (rule Exists.hyps)
    then show "Y \<in> pp_qclosure G" using Y by simp
  qed
  then show ?case by (simp add: pp_qclosure_Union)
qed

subsection \<open>Closure of the operator closure under the logical shapes\<close>

lemma pp_fclosure_Intop:
  assumes F: "F \<in> pp_fclosure G" and H: "H \<in> pp_fclosure G"
  shows "(\<lambda>P. F P \<inter> H P) \<in> pp_fclosure G"
proof -
  have "\<And>K. K \<in> {F, H} \<Longrightarrow> K \<in> pp_fclosure G"
    using F H by blast
  then have "(\<lambda>P. \<Inter> ((\<lambda>K. K P) ` {F, H})) \<in> pp_fclosure G"
    by (rule f_Inter)
  moreover have "(\<lambda>P. \<Inter> ((\<lambda>K. K P) ` {F, H})) =
      (\<lambda>P. F P \<inter> H P)"
    by auto
  ultimately show ?thesis by simp
qed

lemma pp_fclosure_Unop:
  assumes F: "F \<in> pp_fclosure G" and H: "H \<in> pp_fclosure G"
  shows "(\<lambda>P. F P \<union> H P) \<in> pp_fclosure G"
proof -
  have "(\<lambda>P. - F P) \<in> pp_fclosure G" using F by (rule f_compl)
  moreover have "(\<lambda>P. - H P) \<in> pp_fclosure G" using H by (rule f_compl)
  ultimately have "(\<lambda>P. (- F P) \<inter> (- H P)) \<in> pp_fclosure G"
    by (rule pp_fclosure_Intop)
  then have "(\<lambda>P. - ((- F P) \<inter> (- H P))) \<in> pp_fclosure G"
    by (rule f_compl)
  moreover have "(\<lambda>P. - ((- F P) \<inter> (- H P))) =
      (\<lambda>P. F P \<union> H P)"
    by auto
  ultimately show ?thesis by simp
qed

lemma pp_fclosure_Unionop:
  assumes S: "\<And>K. K \<in> S \<Longrightarrow> K \<in> pp_fclosure G"
  shows "(\<lambda>P. \<Union> ((\<lambda>K. K P) ` S)) \<in> pp_fclosure G"
proof -
  have "\<And>K. K \<in> (\<lambda>K. \<lambda>P. - K P) ` S \<Longrightarrow> K \<in> pp_fclosure G"
    using S f_compl by blast
  then have "(\<lambda>P. \<Inter> ((\<lambda>K. K P) ` ((\<lambda>K. \<lambda>P. - K P) ` S)))
      \<in> pp_fclosure G"
    by (rule f_Inter)
  then have "(\<lambda>P. - (\<Inter> ((\<lambda>K. K P) ` ((\<lambda>K. \<lambda>P. - K P) ` S))))
      \<in> pp_fclosure G"
    by (rule f_compl)
  moreover have
      "(\<lambda>P. - (\<Inter> ((\<lambda>K. K P) ` ((\<lambda>K. \<lambda>P. - K P) ` S)))) =
       (\<lambda>P. \<Union> ((\<lambda>K. K P) ` S))"
    by (rule ext) (auto simp: image_image)
  ultimately show ?thesis by simp
qed

lemma pp_fclosure_operator_equalop:
  assumes F: "F \<in> pp_fclosure G" and H: "H \<in> pp_fclosure G"
  shows "(\<lambda>P. pp_operator_equal (F P) (H P)) \<in> pp_fclosure G"
proof -
  have inter: "(\<lambda>P. F P \<inter> H P) \<in> pp_fclosure G"
    using F H by (rule pp_fclosure_Intop)
  have "(\<lambda>P. (- F P) \<inter> (- H P)) \<in> pp_fclosure G"
    using f_compl[OF F] f_compl[OF H] by (rule pp_fclosure_Intop)
  with inter have
      "(\<lambda>P. (F P \<inter> H P) \<union> ((- F P) \<inter> (- H P))) \<in> pp_fclosure G"
    by (rule pp_fclosure_Unop)
  then have "(\<lambda>P. pp_sem_box
      ((F P \<inter> H P) \<union> ((- F P) \<inter> (- H P)))) \<in> pp_fclosure G"
    by (rule f_box)
  moreover have "(\<lambda>P. pp_sem_box
      ((F P \<inter> H P) \<union> ((- F P) \<inter> (- H P)))) =
      (\<lambda>P. pp_operator_equal (F P) (H P))"
    by (simp add: pp_operator_equal_is_boxed_biconditional)
  ultimately show ?thesis by simp
qed

subsection \<open>Abstracting a de Bruijn position yields a closure operator\<close>

theorem pp_eval_abstract_in_fclosure:
  assumes Dom: "\<And>X. X \<in> Dom \<Longrightarrow> X \<in> pp_qclosure G"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
  shows "\<And>e1 e2. (\<And>X. X \<in> set e1 \<Longrightarrow> X \<in> pp_qclosure G) \<Longrightarrow>
    (\<And>X. X \<in> set e2 \<Longrightarrow> X \<in> pp_qclosure G) \<Longrightarrow>
    (\<lambda>P. pp_eval Dom V t (e1 @ P # e2)) \<in> pp_fclosure G"
proof (induct t)
  case (Var n)
  show ?case
  proof (cases "n < length e1")
    case True
    have "(\<lambda>P. pp_eval Dom V (Var n) (e1 @ P # e2)) = (\<lambda>P. e1 ! n)"
      using True by (simp add: nth_append)
    moreover have "pp_cone_det_prop G (e1 ! n)"
      using True Var.prems(1) nth_mem
      by (blast intro: pp_qclosure_cone_det)
    ultimately show ?thesis by (simp add: f_const)
  next
    case notlt: False
    show ?thesis
    proof (cases "n = length e1")
      case True
      have "(\<lambda>P. pp_eval Dom V (Var n) (e1 @ P # e2)) = (\<lambda>P. P)"
        using True by (simp add: nth_append)
      then show ?thesis by (simp add: f_id)
    next
      case False
      with notlt have gt: "Suc (length e1) \<le> n" by simp
      show ?thesis
      proof (cases "n - Suc (length e1) < length e2")
        case True
        have split: "n = Suc (length e1) + (n - Suc (length e1))"
          using gt by simp
        then have lt: "n < Suc (length e1 + length e2)"
          using True by simp
        have "(\<lambda>P. pp_eval Dom V (Var n) (e1 @ P # e2)) =
            (\<lambda>P. e2 ! (n - Suc (length e1)))"
          using gt lt by (simp add: nth_append nth_Cons')
        moreover have
            "pp_cone_det_prop G (e2 ! (n - Suc (length e1)))"
          using True Var.prems(2) nth_mem
          by (blast intro: pp_qclosure_cone_det)
        ultimately show ?thesis by (simp add: f_const)
      next
        case False
        have "Suc (length e1) + length e2 \<le> n"
          using False gt by simp
        then have "\<not> n < Suc (length e1 + length e2)" by simp
        then have "(\<lambda>P. pp_eval Dom V (Var n) (e1 @ P # e2)) =
            (\<lambda>P. {})"
          by simp
        moreover have "pp_cone_det_prop G {}"
          using pp_qclosure_empty by (rule pp_qclosure_cone_det)
        ultimately show ?thesis by (simp add: f_const)
      qed
    qed
  qed
next
  case (Const c ty)
  have "pp_cone_det_prop G (V c)"
    using Val by (rule pp_qclosure_cone_det)
  then show ?case by (simp add: f_const)
next
  case (App f a)
  have "pp_cone_det_prop G {}"
    using pp_qclosure_empty by (rule pp_qclosure_cone_det)
  then show ?case by (simp add: f_const)
next
  case (Lam ty A)
  have "pp_cone_det_prop G {}"
    using pp_qclosure_empty by (rule pp_qclosure_cone_det)
  then show ?case by (simp add: f_const)
next
  case (Neg A)
  then show ?case by (simp add: f_compl)
next
  case (Conj A B)
  then show ?case by (simp add: pp_fclosure_Intop)
next
  case (Disj A B)
  then show ?case by (simp add: pp_fclosure_Unop)
next
  case (Imp A B)
  from Imp have "(\<lambda>P. - pp_eval Dom V A (e1 @ P # e2)) \<in> pp_fclosure G"
    by (simp add: f_compl)
  moreover from Imp have
      "(\<lambda>P. pp_eval Dom V B (e1 @ P # e2)) \<in> pp_fclosure G"
    by simp
  ultimately show ?case
    by (simp add: pp_fclosure_Unop)
next
  case (Eq ty A B)
  then show ?case by (simp add: pp_fclosure_operator_equalop)
next
  case (Forall ty A)
  have "\<And>K. K \<in> (\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom
      \<Longrightarrow> K \<in> pp_fclosure G"
  proof -
    fix K
    assume "K \<in> (\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom"
    then obtain X where X: "X \<in> Dom"
      and K: "K = (\<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2))"
      by blast
    have p1: "\<And>Z. Z \<in> set (X # e1) \<Longrightarrow> Z \<in> pp_qclosure G"
      using X Dom Forall.prems(1) by auto
    have "(\<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2))
        \<in> pp_fclosure G"
      by (rule Forall.hyps[OF p1 Forall.prems(2)])
    then show "K \<in> pp_fclosure G" using K by simp
  qed
  then have "(\<lambda>P. \<Inter> ((\<lambda>K. K P) `
      ((\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom)))
      \<in> pp_fclosure G"
    by (rule f_Inter)
  moreover have "(\<lambda>P. \<Inter> ((\<lambda>K. K P) `
      ((\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom))) =
      (\<lambda>P. pp_eval Dom V (Forall ty A) (e1 @ P # e2))"
    by (rule ext) (simp add: image_image)
  ultimately show ?case by simp
next
  case (Exists ty A)
  have "\<And>K. K \<in> (\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom
      \<Longrightarrow> K \<in> pp_fclosure G"
  proof -
    fix K
    assume "K \<in> (\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom"
    then obtain X where X: "X \<in> Dom"
      and K: "K = (\<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2))"
      by blast
    have p1: "\<And>Z. Z \<in> set (X # e1) \<Longrightarrow> Z \<in> pp_qclosure G"
      using X Dom Exists.prems(1) by auto
    have "(\<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2))
        \<in> pp_fclosure G"
      by (rule Exists.hyps[OF p1 Exists.prems(2)])
    then show "K \<in> pp_fclosure G" using K by simp
  qed
  then have "(\<lambda>P. \<Union> ((\<lambda>K. K P) `
      ((\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom)))
      \<in> pp_fclosure G"
    by (rule pp_fclosure_Unionop)
  moreover have "(\<lambda>P. \<Union> ((\<lambda>K. K P) `
      ((\<lambda>X. \<lambda>P. pp_eval Dom V A ((X # e1) @ P # e2)) ` Dom))) =
      (\<lambda>P. pp_eval Dom V (Exists ty A) (e1 @ P # e2))"
    by (rule ext) (simp add: image_image)
  ultimately show ?case by simp
qed

subsection \<open>The bridge\<close>

text \<open>
  Abstracting the outermost variable gives an operator of the function closure, hence
  cone-determined, hence one whose purity value the \<open>p_pure\<close> rule accepts.  So a
  \<open>Pure\<close> applied to a lambda over the interpreted fragment lands in the propositional
  closure with no hypothesis assumed.
\<close>

corollary pp_eval_abstract_cone_determined:
  assumes Dom: "\<And>X. X \<in> Dom \<Longrightarrow> X \<in> pp_qclosure G"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
    and env: "\<And>X. X \<in> set env \<Longrightarrow> X \<in> pp_qclosure G"
  shows "pp_cone_determined G
    (\<lambda>P. pp_eval Dom V M (P # env))"
proof -
  have "(\<lambda>P. pp_eval Dom V M ([] @ P # env)) \<in> pp_fclosure G"
    using Dom Val by (rule pp_eval_abstract_in_fclosure) (use env in auto)
  then show ?thesis
    by (simp add: pp_fclosure_cone_determined)
qed

theorem pp_eval_purity_in_pclosure:
  assumes Dom: "\<And>X. X \<in> Dom \<Longrightarrow> X \<in> pp_qclosure G"
    and Val: "\<And>c. V c \<in> pp_qclosure G"
    and env: "\<And>X. X \<in> set env \<Longrightarrow> X \<in> pp_qclosure G"
  shows "pp_purity_operator (\<lambda>P. pp_eval Dom V M (P # env))
    \<in> pp_pclosure G"
  using pp_eval_abstract_cone_determined[OF Dom Val env]
  by (rule p_pure)

subsection \<open>What the bridge covers, and what it does not\<close>

text \<open>
  Covered.  For the fragment of \<open>oterm\<close> the valuation interprets --- variables,
  propositional constants, the Boolean connectives, object-language identity, the
  modality by way of \<open>pp_eval_ObjBox\<close>, and quantification at \<open>Prop\<close> --- denotations
  lie in \<open>pp_qclosure G\<close> whenever the domain, the constant valuation and the
  environment do, and abstracting any de Bruijn position yields an operator of
  \<open>pp_fclosure G\<close>.  Applying \<open>Pure\<close> to such an abstraction lands in
  \<open>pp_pclosure G\<close> with nothing assumed.  Combined with
  \<open>pp_pure_seed_decision_basis\<close>, the seed is a decision basis for the denotations of
  these terms.

  Not covered.  Abstraction and application are given the value \<open>{}\<close>, so the bridge
  says nothing about terms whose meaning depends on them --- in particular nothing
  about quantification at higher types, and nothing about iterated \<open>Pure\<close>, which is
  what the target PP instance itself involves.  Interpreting those needs a value
  universe for the higher domains, which is the same obstacle the fixed-term theorem
  of \<open>Bacon_PP_TypeCoherence\<close> works around by using a type class.  So the bridge is
  real but partial: it converts the standing gap from ``no connection to the syntax at
  all'' into ``no connection above the propositional fragment''.
\<close>

end
