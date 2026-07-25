theory Bacon_PP_Modal_Five
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Diagonal"
    "Higher_Order_Metaphysics_PP.Bacon_PP_Generic_Witness"
begin

section \<open>The 5 principle is valid in every model\<close>

text \<open>
  Step two ended by naming a single question as the highest-value open one: does the
  background prove a 5 or B principle?  It cuts both ways --- a 5 principle would let
  \<open>\<diamond> Pure (K R)\<close> plus persistence deliver \<open>\<box> Pure (K R)\<close> and fire Recombination, and it
  would also disqualify the word-action structure, whose \<open>\<box>\<close> is S4 but not S5.

  This theory settles the semantic half, and the answer is not the expected one.  It
  needs no extra hypotheses at all: 5 is valid in \emph{every} applicative structure,
  by two of the locale's own axioms.

  The reason is structural rather than modal.  In this semantics \<open>\<box>A\<close> abbreviates
  \<open>Eq Prop A ObjTrue\<close>, and the evaluation clause for \<open>Eq\<close> is

  \begin{center}
  \<open>eval \<rho> (Eq \<sigma> M N) = truth_den (eq_den \<sigma> (eval \<rho> M) (eval \<rho> N))\<close>,
  \end{center}

  so an identity proposition always denotes in the two-element image of \<open>truth_den\<close>.
  \<open>Neg\<close> does the same.  So \<open>\<not> \<box>A\<close> denotes \<open>truth_den True\<close> exactly when it is true, and
  \<open>eq_den_refl\<close> then makes \<open>\<box> (\<not> \<box>A)\<close> true.  There is no room in the locale for a
  proposition that is neither \<open>truth_den True\<close> nor \<open>truth_den False\<close> to be the value of
  a \<open>\<box>\<close>.  The modal fragment of this semantics is therefore not merely S4-with-extras;
  it collapses \<open>\<box>\<close> onto a two-valued predicate.
\<close>

definition modal_5 :: "oterm \<Rightarrow> oterm" where
  "modal_5 A = Imp (Neg (\<box>\<^sub>o A)) (\<box>\<^sub>o (Neg (\<box>\<^sub>o A)))"

lemma typed_modal_5:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> modal_5 A : Prop"
  using assms
  by (auto simp: modal_5_def intro: typed_ObjBox has_type.Neg)

subsection \<open>Identity and negation are two-valued\<close>

lemma (in applicative_structure) eval_ObjTrue:
  "eval \<rho> ObjTrue = truth_den True"
proof -
  have "eval \<rho> ObjTrue =
      truth_den (\<forall>x \<in> D Prop.
        holds (eval (extend_env x \<rho>) (Imp (Var 0) (Var 0))))"
    by (simp add: ObjTrue_def)
  moreover have
    "(\<forall>x \<in> D Prop.
        holds (eval (extend_env x \<rho>) (Imp (Var 0) (Var 0))))"
    by simp
  ultimately show ?thesis by simp
qed

lemma (in applicative_structure) eval_Neg_two_valued:
  "eval \<rho> (Neg A) = truth_den (\<not> holds (eval \<rho> A))"
  by simp

subsection \<open>The result\<close>

theorem (in applicative_structure) modal_5_valid:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "valid_in_context \<Gamma> (modal_5 A)"
  unfolding valid_in_context_def
proof
  show "\<Gamma> \<turnstile> modal_5 A : Prop"
    using A_type by (rule typed_modal_5)
next
  show "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (modal_5 A))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have "holds (eval \<rho> (Neg (\<box>\<^sub>o A))) \<longrightarrow>
        holds (eval \<rho> (\<box>\<^sub>o (Neg (\<box>\<^sub>o A))))"
    proof
      assume h: "holds (eval \<rho> (Neg (\<box>\<^sub>o A)))"
      have val: "eval \<rho> (Neg (\<box>\<^sub>o A)) = truth_den True"
        using h by simp
      have "eq_den Prop (truth_den True) (truth_den True)"
        by (rule eq_den_refl) (rule truth_den_type)
      then have "holds
          (truth_den (eq_den Prop (eval \<rho> (Neg (\<box>\<^sub>o A)))
            (eval \<rho> ObjTrue)))"
        unfolding val eval_ObjTrue by simp
      then show "holds (eval \<rho> (\<box>\<^sub>o (Neg (\<box>\<^sub>o A))))"
        by (simp add: ObjBox_def)
    qed
    then show "holds (eval \<rho> (modal_5 A))"
      by (simp add: modal_5_def)
  qed
qed

subsection \<open>The word-action \<open>\<box>\<close> is not two-valued\<close>

text \<open>
  The consequence below turns on \<open>pp_sem_box\<close> taking a value other than \<open>{}\<close> and
  \<open>UNIV\<close>.  That is checked here rather than asserted, so the negative conclusion is
  machine-backed.
\<close>

theorem pp_sem_box_not_two_valued:
  "pp_sem_box {w. w \<noteq> []} \<noteq> {} \<and> pp_sem_box {w. w \<noteq> []} \<noteq> UNIV"
proof -
  have box_eq: "pp_sem_box {w. w \<noteq> []} = {i. i \<noteq> []}"
  proof (rule set_eqI)
    fix i :: pp_word
    show "(i \<in> pp_sem_box {w. w \<noteq> []}) = (i \<in> {i. i \<noteq> []})"
    proof
      assume "i \<in> pp_sem_box {w. w \<noteq> []}"
      then have "pp_view i {w. w \<noteq> []} = UNIV"
        by (simp add: pp_sem_box_def)
      then have "[] \<in> pp_view i {w. w \<noteq> []}" by simp
      then show "i \<in> {i. i \<noteq> []}"
        by (simp add: pp_view_def)
    next
      assume "i \<in> {i. i \<noteq> []}"
      then have ne: "i \<noteq> []" by simp
      have "pp_view i {w. w \<noteq> []} = UNIV"
        using ne by (auto simp: pp_view_def)
      then show "i \<in> pp_sem_box {w. w \<noteq> []}"
        by (simp add: pp_sem_box_def)
    qed
  qed
  have "[] \<notin> {i :: pp_word. i \<noteq> []}" by simp
  moreover have "[0] \<in> {i :: pp_word. i \<noteq> []}" by simp
  ultimately show ?thesis
    unfolding box_eq by blast
qed

text \<open>
  \<^bold>\<open>Consequences, stated carefully.\<close>

  \<^item> \<^emph>\<open>For the refutation.\<close>  Codex's objection to the step from \<open>\<diamond> Pure (K R)\<close> to
    \<open>\<box> Pure (K R)\<close> was that a reflexive transitive branching frame can have the
    proposition false at the root and persistently true on one branch.  The theorem
    above shows no such frame is a model of this semantics.  That does \emph{not} by
    itself give a proof of 5 in CEV --- validity in all models yields provability only
    through a completeness theorem, and whether the repository's completeness results
    apply to this schema is not settled here.  It does mean the refutation cannot be
    blocked by exhibiting an S4 countermodel, which was the only concrete objection on
    the table.

  \<^item> \<^emph>\<open>Against the word-action programme.\<close>  This is the sharper consequence, and it is
    negative for the project's main semantic route.  In the word action
    \<open>pp_sem_box X = {i. pp_view i X = UNIV}\<close> is in general neither \<open>{}\<close> nor \<open>UNIV\<close>, so
    \<open>\<box>\<close> there is genuinely three-or-more-valued.  Any structure in which \<open>pp_sem_box\<close>
    interprets \<open>ObjBox\<close> therefore cannot be an \<open>applicative_structure\<close>, because the
    \<open>Eq\<close> clause forces \<open>ObjBox\<close>-values into the image of \<open>truth_den\<close>.  So obligation
    item 2 of the checklist (\<open>base_sound\<close>) is not a routine verification for the word
    action --- \<^bold>\<open>it fails\<close>, for a reason visible in the locale rather than in any
    detail of the construction.

  \<^item> \<^emph>\<open>What survives.\<close>  The word-action results retain their status as results about a
    concrete M-set: the invariance analysis, the generic witness theorems, the
    decision-basis and attainment results are all untouched as mathematics.  What they
    lose is the claim to bear directly on Goodman's question by way of \<open>base_sound\<close>.
    They bear on it only if the intended reading of \<open>\<box>\<close> is \emph{not} \<open>Eq Prop A ObjTrue\<close>
    --- that is, only for a background weaker than the one at issue.

  \<^item> \<^emph>\<open>Why this was not visible earlier.\<close>  The consensus review flagged the modelhood
    obligation as ``a real risk'' but rated it a verification task.  It is not: the
    obstruction is one line of the evaluation function.  This is the correct kind of
    thing for a refutation-directed step to turn up, even though what it refutes is
    the project's own route rather than the target claim.
\<close>

end
