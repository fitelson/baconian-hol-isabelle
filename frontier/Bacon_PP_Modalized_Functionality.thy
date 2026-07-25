theory Bacon_PP_Modalized_Functionality
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Diagonal"
begin

section \<open>Fix 1: Modalized Functionality\<close>

text \<open>
  The audit against \<open>\<section>2\<close> of Goodman's notes found that \<open>T\<^sub>0\<close> contains

  \begin{center}
  \<open>\<box> \<forall>x (X x = Y x) \<longrightarrow> X = Y\<close>
  \end{center}

  and the repository does not.  \emph{Plain} Functionality \<open>\<forall>x (X x = Y x) \<longrightarrow> X = Y\<close> is
  \emph{not} part of \<open>T\<^sub>0\<close> (it is true in Bacon's models but not in the theory), so the
  \<open>\<box>\<close> is essential and must not be dropped.

  Why this matters, in one line: MF is the identity-\emph{introduction} principle, and
  it applies under hypotheses.  The repository's \<open>CEV_proves.VectorEquivalence\<close> is
  derivable in \<open>T\<^sub>0\<close> --- Rule of Equivalence on open formulas, then \<open>Gen\<close>, then
  necessitation (available because \<open>\<box>A\<close> abbreviates \<open>A = \<top>\<close>, so the Rule of
  Equivalence turns a theorem \<open>A\<close> into \<open>A = \<top>\<close>), then MF --- but the converse fails,
  because the vector rule is theorem-level only.  \<open>Bacon_Zeta\<close> says as much in its own
  commentary.  So the repository's theory is \emph{strictly weaker} than \<open>T\<^sub>0\<close>, and QSS,
  \<open>fun\<acute>\<close> and hence Goodman's liar are all out of reach in it.

  The axiom sets of \<open>Bacon_PP_Question\<close> are left untouched; the corrected sets are
  defined here so that no existing result silently changes meaning.
\<close>

subsection \<open>The axiom\<close>

definition pp_modalized_functionality :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where
  "pp_modalized_functionality \<sigma> \<tau> =
    Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (Imp
          (\<box>\<^sub>o (Forall \<sigma>
            (Eq \<tau> (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))))
          (Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1) (Var 0))))"

text \<open>
  De Bruijn reading, innermost first: under the three binders \<open>Var 0\<close> is \<open>x\<close>, \<open>Var 1\<close>
  is \<open>Y\<close> and \<open>Var 2\<close> is \<open>X\<close>; in the consequent, which sits under two binders, \<open>Var 1\<close>
  is \<open>X\<close> and \<open>Var 0\<close> is \<open>Y\<close>.
\<close>

lemma typed_pp_modalized_functionality:
  "[] \<turnstile> pp_modalized_functionality \<sigma> \<tau> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_modalized_functionality_def ObjBox_def ObjTrue_def
      lookup_def)

definition pp_modalized_functionality_schema :: "oterm set" where
  "pp_modalized_functionality_schema =
    {A. \<exists>\<sigma> \<tau>. A = pp_modalized_functionality \<sigma> \<tau>}"

lemma pp_modalized_functionality_schema_typed:
  assumes "A \<in> pp_modalized_functionality_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_modalized_functionality
  unfolding pp_modalized_functionality_schema_def by blast

subsection \<open>The corrected axiom sets\<close>

definition pp_T0_recombination_background :: "oterm set" where
  "pp_T0_recombination_background =
    pp_recombination_background_axioms \<union>
    pp_modalized_functionality_schema"

definition pp_T0_recombination_PP_axioms :: "oterm set" where
  "pp_T0_recombination_PP_axioms =
    insert pp_target_PP pp_T0_recombination_background"

definition pp_T0_full_QLN_PP_axioms :: "oterm set" where
  "pp_T0_full_QLN_PP_axioms =
    pp_full_QLN_PP_axioms \<union> pp_modalized_functionality_schema"

lemma pp_T0_recombination_PP_axioms_typed:
  assumes "A \<in> pp_T0_recombination_PP_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms
  unfolding pp_T0_recombination_PP_axioms_def
    pp_T0_recombination_background_def
  using pp_recombination_PP_axioms_typed
    pp_modalized_functionality_schema_typed
  unfolding pp_recombination_PP_axioms_def
  by blast

subsection \<open>Everything already derived still stands, and more\<close>

lemma pp_recombination_PP_axioms_subset_T0:
  "pp_recombination_PP_axioms \<subseteq> pp_T0_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def
    pp_T0_recombination_PP_axioms_def
    pp_T0_recombination_background_def
  by blast

lemma pp_full_QLN_PP_axioms_subset_T0:
  "pp_full_QLN_PP_axioms \<subseteq> pp_T0_full_QLN_PP_axioms"
  unfolding pp_T0_full_QLN_PP_axioms_def by blast

theorem CEV_axiom_proves_transfer_to_T0:
  assumes "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; pp_T0_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms pp_recombination_PP_axioms_subset_T0
  by (rule CEV_axiom_proves_mono)

theorem CEV_axiom_proves_transfer_to_T0_full_QLN:
  assumes "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; pp_T0_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms pp_full_QLN_PP_axioms_subset_T0
  by (rule CEV_axiom_proves_mono)

text \<open>
  So every derivation already in the repository --- in particular the purity of the
  diagonal and positive-diagonal operators and their Recombination instances ---
  survives the strengthening.  What the strengthening buys is the converse direction:
  identity conclusions that were previously unreachable under hypotheses.
\<close>

subsection \<open>The corrected question\<close>

definition pp_T0_recombination_consistency_question :: bool where
  "pp_T0_recombination_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_T0_recombination_PP_axioms"

definition pp_T0_full_QLN_consistency_question :: bool where
  "pp_T0_full_QLN_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_T0_full_QLN_PP_axioms"

theorem pp_T0_negative_answer_iff_derives_false:
  "\<not> pp_T0_recombination_consistency_question \<longleftrightarrow>
    [] ; pp_T0_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  unfolding pp_T0_recombination_consistency_question_def
    CEV_axiom_consistent_def
  by blast

theorem pp_T0_consistency_implies_old:
  assumes "pp_T0_recombination_consistency_question"
  shows "CEV_axiom_consistent [] pp_recombination_PP_axioms"
  using assms
  unfolding pp_T0_recombination_consistency_question_def
    CEV_axiom_consistent_def
  using CEV_axiom_proves_transfer_to_T0 by blast

text \<open>
  \<^bold>\<open>Direction of transfer, stated so it is not misread.\<close>  The corrected question is
  \emph{harder}: consistency of the \<open>T\<^sub>0\<close> set implies consistency of the old set, not
  conversely (\<open>pp_T0_consistency_implies_old\<close>).  Symmetrically, a refutation in the
  old set transfers up to the \<open>T\<^sub>0\<close> set (\<open>CEV_axiom_proves_transfer_to_T0\<close>).  So the
  repository's negative results remain usable, and its positive ones do not.

  This is only half the transfer story.  The audit also left open whether the
  \<open>C_proves\<close> primitive axiom stock --- \<open>BooleanIdentity\<close>, \<open>IdentityIdentity\<close>, and the
  quantifier absorption and distribution axioms --- is \emph{extra} relative to \<open>T\<^sub>0\<close>,
  in which case the repository would be stronger in that respect and even refutations
  would not transfer cleanly.  That question is about Bacon's \<open>H\<close>, not about Isabelle,
  and is not settled here.
\<close>

end
