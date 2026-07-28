theory Bacon_PP_Definable_Purity
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Purity_Operator"
begin

section \<open>Fix 2: the definability reading of purity\<close>

text \<open>
  The audit found the repository using the \emph{invariance} reading of \<open>Pure\<close>:

  \begin{center}
  \<open>pp_purity_operator F = {i. pp_fun_invariant (pp_fun_view i F)}\<close>.
  \end{center}

  Goodman's \<open>\<section>2\<close> says instead that in Bacon's appendix model \<open>Pure\<^sub>\<sigma>\<close> is interpreted as
  applying, at each substitution, to \emph{the denotations of closed terms with no
  non-logical constants}.  His M2 is titled ``the invariance reading of purity is not
  an option'': identifying purity with invariance contradicts QSS given a fundamental
  proposition, and ``the live question is only ever which invariants are \emph{certified}
  pure''.  His M1 says PP \emph{fails} at \<open>t \<rightarrow> t\<close> in this model.

  So the repository's \<open>pp_purity_of_pure_holds_in_word_action\<close> --- which correctly
  proves \<open>pp_second_order_invariant pp_purity_operator\<close> --- does not show that PP holds
  in the word action, and the surrounding claim that it does is false.  This theory
  supplies the corrected reading and proves the structural fact that makes M2 true.

  The logical stock is carried as a parameter \<open>L\<close> rather than defined, because pinning
  it down means giving a denotation function from closed \<open>oterm\<close>s to operators --- the
  bridge problem.  Everything below is uniform in \<open>L\<close>, so nothing waits on that.
\<close>

subsection \<open>The corrected reading\<close>

definition pp_definable_purity ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_definable_purity L F = {i. pp_fun_view i F \<in> L}"

text \<open>
  \<open>L\<close> is the stock of operators denoted by closed constant-free terms.  Read: \<open>F\<close> counts
  as pure at substitution \<open>i\<close> exactly when the way \<open>F\<close> looks from \<open>i\<close> is logically
  denotable --- Goodman's ``applying, at each substitution, to the denotations of
  closed terms with no non-logical constants''.
\<close>

subsection \<open>Definability implies invariance, but not conversely\<close>

text \<open>
  A closed constant-free term denotes an invariant operator, so any faithful \<open>L\<close> is a
  set of invariants.  Under that hypothesis the corrected reading is \emph{included in}
  the old one.
\<close>

theorem pp_definable_purity_subset_invariance:
  assumes L_inv: "L \<subseteq> {F. pp_fun_invariant F}"
  shows "pp_definable_purity L F \<subseteq> pp_purity_operator F"
proof
  fix i assume "i \<in> pp_definable_purity L F"
  then have "pp_fun_view i F \<in> L"
    unfolding pp_definable_purity_def by simp
  then have "pp_fun_invariant (pp_fun_view i F)"
    using L_inv by blast
  then show "i \<in> pp_purity_operator F"
    unfolding pp_purity_operator_def by simp
qed

text \<open>
  The converse fails as soon as the stock is a \emph{proper} subset of the invariants,
  and that is M2's point.  The invariant operators are exactly the classifiers
  (\<open>pp_fun_invariant_is_classifier\<close>, \<open>pp_classifier_is_function_space_invariant\<close>) and
  \<open>pp_classifier\<close> is injective, so they are in bijection with \emph{sets} of
  propositions --- vastly more numerous than the closed terms, of which there are only
  countably many.  Hence no faithful \<open>L\<close> exhausts the invariants, and the two readings
  must come apart.
\<close>

theorem pp_readings_differ_of_proper_stock:
  assumes proper: "L \<subset> {F. pp_fun_invariant F}"
  shows "\<exists>F i. i \<in> pp_purity_operator F \<and>
    i \<notin> pp_definable_purity L F"
proof -
  obtain F where F_inv: "pp_fun_invariant F" and F_out: "F \<notin> L"
    using proper by blast
  have view: "pp_fun_view [] F = F"
    using F_inv unfolding pp_fun_invariant_def by simp
  have "[] \<in> pp_purity_operator F"
    unfolding pp_purity_operator_def using view F_inv by simp
  moreover have "[] \<notin> pp_definable_purity L F"
    unfolding pp_definable_purity_def using view F_out by simp
  ultimately show ?thesis by blast
qed

text \<open>
  \<^bold>\<open>The counting fact behind the properness hypothesis.\<close>  \<open>pp_classifier\<close> injects the
  powerset of the propositions into the invariant operators, so the invariants are
  strictly more numerous than the propositions, while the closed constant-free terms
  are countable.  The injection is already in the repository
  (\<open>pp_classifier_injective\<close>); it is restated here so the argument is visible at the
  point of use.
\<close>

theorem pp_invariant_operators_outnumber_propositions:
  "inj pp_classifier \<and>
    (\<forall>S. pp_fun_invariant (pp_classifier S))"
proof
  show "inj pp_classifier"
    by (rule pp_classifier_injective)
  show "\<forall>S. pp_fun_invariant (pp_classifier S)"
    using pp_classifier_is_function_space_invariant by blast
qed

subsection \<open>What this does to the PP claim\<close>

text \<open>
  \<^bold>\<open>Withdrawn.\<close>  \<open>pp_purity_of_pure_holds_in_word_action\<close> proves
  \<open>pp_second_order_invariant pp_purity_operator\<close>.  That is true and remains true.  The
  claim attached to it in \<open>Bacon_PP_Purity_Operator\<close> --- ``hence the target PP instance
  is true in the full word-action M-set'' --- presupposes that purity \emph{is}
  invariance, which M2 denies and which \<open>pp_readings_differ_of_proper_stock\<close> shows is
  untenable for any countable stock.  Goodman's M1 settles the matter in the opposite
  direction: PP \emph{fails} at \<open>t \<rightarrow> t\<close> in this model, necessarily so, because the model
  verifies Purity of Fun, QSS and a fundamental proposition, and Bacon's footnote-59
  argument then excludes PP.

  \<^bold>\<open>What survives.\<close>  Everything the repository proves about invariance survives as
  mathematics about invariance: the classifier characterisation, the orbit analysis,
  the generic-witness theorems, the decision-basis and attainment results.  What does
  not survive is the reading of any of it as a claim about \<open>Pure\<close>.  In the corrected
  setting those results describe the \emph{ambient} invariant structure, inside which
  the real question --- Goodman's ``which invariants are certified pure'' --- is posed
  but not yet answered.

  \<^bold>\<open>Corroboration that only the reading was wrong.\<close>  M1 computes \<open>Pure\<^sub>t\<close> at the bottom
  type as the non-contingency operator \<open>\<lambda>p. (\<box>p \<or> \<box>\<not>p)\<close>, and the repository's
  \<open>pp_purity_of_meet\<close> independently gives
  \<open>pp_purity_operator (\<lambda>P. b \<inter> P) = pp_decided b\<close> with \<open>pp_decided X = \<box>X \<union> \<box>(-X)\<close> ---
  the same operator.  The model formalization is faithful; only the interpretation of
  the constant \<open>Pure\<close> was not.
\<close>

end
