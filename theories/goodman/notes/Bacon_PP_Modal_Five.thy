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

subsection \<open>The 5 pattern itself fails in the word action\<close>

text \<open>
  Sharper than two-valuedness: the word-action \<open>\<box>\<close> refutes the 5 \emph{pattern}
  directly.  \<open>pp_sem_box X\<close> is up-closed under left extension, so its complement is
  down-closed, and boxing a down-closed proper subset gives \<open>{}\<close>.
\<close>

theorem pp_sem_box_refutes_five_pattern:
  "\<not> (- pp_sem_box {w. w \<noteq> []}
        \<subseteq> pp_sem_box (- pp_sem_box {w. w \<noteq> []}))"
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
      then show "i \<in> {i. i \<noteq> []}" by (simp add: pp_view_def)
    next
      assume "i \<in> {i. i \<noteq> []}"
      then have "pp_view i {w. w \<noteq> []} = UNIV"
        by (auto simp: pp_view_def)
      then show "i \<in> pp_sem_box {w. w \<noteq> []}"
        by (simp add: pp_sem_box_def)
    qed
  qed
  have compl: "- pp_sem_box {w. w \<noteq> []} = {[]}"
    unfolding box_eq by auto
  have "pp_sem_box {[] :: pp_word} = {}"
  proof (rule set_eqI, simp)
    fix i :: pp_word
    have "[0] @ i \<noteq> []" by simp
    then have "\<not> pp_view i {[] :: pp_word} = UNIV"
      by (auto simp: pp_view_def)
    then show "i \<notin> pp_sem_box {[] :: pp_word}"
      by (simp add: pp_sem_box_def)
  qed
  then show ?thesis
    unfolding compl by simp
qed

text \<open>
  \<^bold>\<open>Consequences, stated carefully.\<close>

  \<^item> \<^emph>\<open>Does CEV \emph{prove} 5?  The completeness results do not settle it.\<close>  Three
    facts, checked by reading the sources.  (i) \<open>CEV_completeness_from_countermodels\<close>
    has exactly the right shape, \<open>valid_in_context \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A\<close>, but it is
    conditional on \<open>CEV_countermodel_property\<close>, which is \emph{defined and never
    proved} anywhere in the development --- it is a hypothesis, not a theorem.
    (ii) The two unconditional biconditionals, \<open>CEV_clean_canonical_valid_iff_proves\<close>
    and \<open>CEV_clean_Henkin_valid_iff_proves\<close>, are \emph{syntactic}: ``valid'' there
    means membership in every clean canonical world or Henkin theory, i.e. in every
    maximal consistent set of formulas.  They relate provability to
    maximal-consistent-set membership and cannot import a model-theoretic validity
    fact.  (iii) Nothing in \<open>Bacon_Intended_Quotient\<close> or \<open>Bacon_Supported_Canonical\<close>
    builds an \<open>applicative_structure\<close> out of a Henkin theory.  So the link
    ``valid in every applicative structure \<Longrightarrow> CEV-provable'' is precisely what is
    missing, and the question stays open.

  \<^item> \<^emph>\<open>Nor does the \<open>modal_4\<close> proof extend.\<close>  \<open>CEV_modal_4\<close> comes from
    \<open>CEV_eq_truth_of_eq\<close>, which substitutes identicals into \<open>F = \<lambda>x. (M = x) = \<top>\<close>
    starting from the reflexive instance.  Substitution of identicals needs a
    \emph{positive} identity premise; 5 supplies a negative one.  The route does not
    generalise, which is weak evidence that 5 is \emph{not} CEV-provable and that this
    semantics is incomplete --- validating more than CEV proves.

  \<^item> \<^emph>\<open>For the refutation.\<close>  Codex's objection to the step from \<open>\<diamond> Pure (K R)\<close> to
    \<open>\<box> Pure (K R)\<close> was that a reflexive transitive branching frame can have the
    proposition false at the root and persistently true on one branch.  No such frame
    is an \<open>applicative_structure\<close>.  But since CEV is not known to be complete for that
    class, this does \emph{not} license the step inside CEV\textsuperscript{+}.  The
    correct summary is narrower than it first appears: the objection survives as an
    objection about \emph{derivability}, and is refuted only as an objection about
    \emph{applicative-structure modelhood}.

  \<^item> \<^emph>\<open>What this does \emph{not} show about the word action.\<close>  A correction to the
    first version of this theory.  \<open>base_sound\<close> is a hypothesis of the
    \<open>henkin_action_model\<close> locale of \<open>Bacon_PP_Axiom_Soundness\<close>, and that locale has
    clauses for \<open>Neg\<close>, \<open>Imp\<close>, \<open>Forall\<close>, \<open>Exists\<close> and \<open>shift\<close> but \<^bold>\<open>no \<open>Eq\<close> clause\<close>.
    It therefore does not force two-valued identity, and the argument above does
    \emph{not} show \<open>base_sound\<close> fails.  What is shown is only that the word action is
    not an \<open>applicative_structure\<close> with \<open>pp_sem_box\<close> interpreting \<open>ObjBox\<close>.

  \<^item> \<^emph>\<open>The correct conditional.\<close>  \<open>pp_sem_box_refutes_five_pattern\<close> shows the word
    action refutes the 5 pattern outright: \<open>pp_sem_box\<close>-images are up-closed under left
    extension, so complements are down-closed, and boxing a down-closed proper subset
    gives \<open>{}\<close>.  Hence \<^bold>\<open>if CEV proves 5, then \<open>base_sound\<close> fails for the word action\<close>
    --- and if CEV does not, the word action survives this test.  One question decides
    both the refutation branch and the model programme, and it is still the right next
    thing to settle; but it must be settled by finding a derivation or a Henkin-theory
    countermodel, not by the completeness theorems.
\<close>

end
