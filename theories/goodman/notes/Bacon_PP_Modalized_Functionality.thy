theory Bacon_PP_Modalized_Functionality
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Diagonal"
begin

section \<open>Modalized Functionality --- a target, not a missing axiom\<close>

text \<open>
  \<^bold>\<open>Correction.\<close>  The first version of this theory recorded Modalized Functionality as
  \emph{absent} from the repository's theory and added it as an axiom, on the strength
  of the audit against \<open>\<section>2\<close> of Goodman's notes.  That was wrong, and checking
  Bacon--Dorr's \emph{Classicism} directly settles it against the audit:

  \<^item> Footnote 18 (p.\ 16) states outright that \<open>C\<close> \emph{includes} Modalized
    Functionality, referring to \<open>\<section>1.5\<close>.
  \<^item> \<open>\<section>1.5\<close> (p.\ 17) exhibits \<^bold>\<open>Intensionality\<close>, \<open>\<box>\<forall>z\<^sub>1\<dots>z\<^sub>n (X z\<^sub>1\<dots>z\<^sub>n \<longleftrightarrow> Y z\<^sub>1\<dots>z\<^sub>n) \<longrightarrow> X = Y\<close>,
    and proves it \emph{is a theorem of Classicism}, from the Logical Equivalence
    instance
    \<open>\<lambda>z\<^sub>1\<dots>z\<^sub>n. (X z\<^sub>1\<dots>z\<^sub>n \<and> \<forall>z\<^sub>1\<dots>z\<^sub>n. (X z\<^sub>1\<dots>z\<^sub>n \<longleftrightarrow> Y z\<^sub>1\<dots>z\<^sub>n))
      = \<lambda>z\<^sub>1\<dots>z\<^sub>n. (Y z\<^sub>1\<dots>z\<^sub>n \<and> \<forall>z\<^sub>1\<dots>z\<^sub>n. (X z\<^sub>1\<dots>z\<^sub>n \<longleftrightarrow> Y z\<^sub>1\<dots>z\<^sub>n))\<close>,
    together with Booleanism and \<open>\<eta>\<close>-conversion.
  \<^item> Intensionality has the \emph{weaker} antecedent (\<open>\<longleftrightarrow>\<close> rather than \<open>=\<close>), so it is
    stronger than Modalized Functionality; \<open>C \<turnstile> Intensionality\<close> therefore gives
    \<open>C \<turnstile> MF\<close>.

  And p.\ 15 supplies the bridge to \emph{this} repository: any H-theory closed under
  Propositional Equivalence together with \<open>\<xi>\<close> or \<open>\<zeta>\<close> is closed under Logical
  Equivalence.  The repository has Propositional Equivalence (\<open>CE_proves.PropEquivalence\<close>)
  and \<open>\<zeta>\<close> (\<open>CEV_proves.VectorEquivalence\<close>, whose \<open>zeta_body\<close> is literally Bacon--Dorr's
  \<open>\<zeta>\<close>-Equivalence).  So repo-CEV contains Classicism, hence proves Intensionality, hence
  proves MF.

  \<^bold>\<open>Consequences.\<close>  Divergence 1 of the audit is \<^bold>\<open>withdrawn\<close>: the repository's theory was
  not weaker than \<open>T\<^sub>0\<close> after all, and the transfer of both refutations \emph{and}
  consistency results is unobstructed.  In particular the explanation I attached to
  step 2's null result --- that Goodman's liar was \emph{inexpressible} because QSS and
  \<open>fun\<acute>\<close> were out of reach --- is also withdrawn.  QSS is reachable.  Step 2 found
  nothing because it searched too small a space.

  What remains below is therefore a \emph{target}, not an axiom: the definition of MF,
  and the axiom sets that would result from adding it, kept only so the derivation has
  something to aim at and so the transfer lemmas are available if MF is ever wanted as
  a primitive.  \<^bold>\<open>Nothing here asserts that the addition is a strengthening.\<close>
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
  \<^bold>\<open>How to read these transfer lemmas now.\<close>  They are formally correct but, given the
  correction above, they carry much less weight than first advertised.  Since \<open>CEV\<close>
  already proves MF, the \<open>T\<^sub>0\<close> sets are expected to be \emph{deductively equivalent} to
  the originals rather than strictly stronger, and \<open>pp_T0_consistency_implies_old\<close>
  should turn out to have a converse.  Establishing that converse is exactly the
  content of the derivation targeted next.

  \<^bold>\<open>The remaining task, stated precisely.\<close>  Prove, in repo-\<open>CEV\<close>:

  \begin{center}
  \<open>\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o (Forall \<sigma> (App X (Var 0) \<longleftrightarrow>\<^sub>o App Y (Var 0)))) (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) X Y)\<close>
  \end{center}

  --- unary Intensionality --- following the \<open>\<section>1.5\<close> route: instantiate \<open>\<zeta>\<close>-Equivalence at
  \<open>F := \<lambda>z. (X z \<and> \<forall>w. (X w \<longleftrightarrow> Y w))\<close> and \<open>G := \<lambda>z. (Y z \<and> \<forall>w. (X w \<longleftrightarrow> Y w))\<close>, whose
  pointwise biconditional \emph{is} an H-theorem; then use \<open>\<box>A = (A = \<top>)\<close> to rewrite
  the shared conjunct to \<open>\<top>\<close>, discharge it by the Boolean identity for \<open>A \<and> \<top>\<close>, and
  finish with \<open>\<eta>\<close>.  \<open>pp_modalized_functionality\<close> then follows because \<open>X z = Y z\<close> implies
  \<open>X z \<longleftrightarrow> Y z\<close> by \<open>Ref\<close> and \<open>LL\<close>.  This is a real derivation, not a rewording, and it is
  not attempted here.
\<close>

end
