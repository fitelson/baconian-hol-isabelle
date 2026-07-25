theory Bacon_PP_Five_Countermodel
  imports Bacon_PP_Modal_Five
begin

section \<open>Reducing the 5 question to a single consistency statement\<close>

text \<open>
  The previous theory established that the completeness results cannot decide whether
  CEV proves 5, and that a countermodel, if there is one, must be a clean Henkin
  theory rather than an applicative structure.  This theory builds that countermodel
  \emph{down to one clearly stated residue}.

  The shape of the argument.  \<open>\<box>X\<close> is \<open>Eq Prop X ObjTrue\<close>, an identity, so if \<open>\<box>X \<in> S\<close>
  then \<open>\<box>X\<close> lies in \<open>CEV_identity_diagram \<Gamma> S\<close> and is inherited by any Henkin theory
  extending that diagram.  Hence 5 fails at \<open>S\<close> as soon as some such extension makes
  \<open>\<box>A\<close> true while \<open>S\<close> does not --- ``not necessary here, necessary at a successor'',
  the failure of euclideanness.  Everything reduces to whether

  \begin{center}
  \<open>insert (\<box>A) (CEV_identity_diagram \<Gamma> S)\<close>
  \end{center}

  is consistent.  That is not an incidental technical hypothesis: by
  \<open>CEV_identity_diagram_derivable_implies_box_derivable\<close>, its \emph{failure} is
  equivalent to \<open>\<box> (\<not> \<box>A) \<in> S\<close>, which is exactly 5 holding at \<open>S\<close>.  So the reduction
  below is tight --- it loses nothing.
\<close>

subsection \<open>The reduction\<close>

theorem CEV_not_proves_modal_5_of_consistent_supported_diagram:
  assumes world: "CEV_supported_world K C \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and A_supported: "CEV_supported_term C A"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
    and consistent: "CEV_consistent \<Gamma>
      (insert (\<box>\<^sub>o A) (CEV_supported_identity_diagram C \<Gamma> S))"
  shows "\<not> \<Gamma> \<turnstile>\<^sub>CEV modal_5 A"
proof -
  let ?B = "insert (\<box>\<^sub>o A) (CEV_supported_identity_diagram C \<Gamma> S)"
  have henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and inf_out: "infinite (UNIV - C)"
    using world unfolding CEV_supported_world_def by blast+
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
    using A_type by (rule typed_ObjBox)
  have negbox_type: "\<Gamma> \<turnstile> Neg (\<box>\<^sub>o A) : Prop"
    using box_type by (rule has_type.Neg)

  text \<open>The base is typed: the diagram sits inside the typed theory \<open>S\<close>.\<close>
  have diagram_sub: "CEV_supported_identity_diagram C \<Gamma> S \<subseteq> S"
    by (auto simp: CEV_supported_identity_diagram_def)
  have S_typed: "typed_theory \<Gamma> S"
    using henkin
    unfolding CEV_clean_Henkin_theory_def CEV_locally_maximal_consistent_def
    by blast
  have typed_B: "typed_theory \<Gamma> ?B"
    unfolding typed_theory_def
  proof (intro ballI)
    fix X assume "X \<in> ?B"
    then show "\<Gamma> \<turnstile> X : Prop"
    proof
      assume "X = \<box>\<^sub>o A"
      then show ?thesis using box_type by simp
    next
      assume "X \<in> CEV_supported_identity_diagram C \<Gamma> S"
      then have "X \<in> S" using diagram_sub by blast
      then show ?thesis
        using S_typed unfolding typed_theory_def by blast
    qed
  qed

  text \<open>
    The support restriction is what makes a reserve of fresh constants available.
    For the \emph{full} identity diagram no reserve exists at all: reflexive
    identities \<open>Eq Prop (Const c Prop) (Const c Prop)\<close> for every \<open>c\<close> are theorems and
    so lie in every clean Henkin theory, whence
    \<open>CEV_identity_diagram_consts_UNIV\<close>.  Restricting to \<open>C\<close>-supported terms leaves
    \<open>UNIV - C\<close> infinite and untouched.
  \<close>
  have consts_B: "consts_of_set ?B \<subseteq> C"
  proof -
    have "consts_of (\<box>\<^sub>o A) \<subseteq> C"
      using A_supported unfolding CEV_supported_term_def by simp
    then show ?thesis
      using CEV_supported_identity_diagram_consts[of C \<Gamma> S]
      by (auto simp: consts_of_set_insert)
  qed
  have D_disjoint: "(UNIV - C) \<inter> consts_of_set ?B = {}"
    using consts_B by blast

  text \<open>So the base extends to a clean Henkin theory \<open>T\<close>, a successor of \<open>S\<close>.\<close>
  obtain T where T_henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and B_sub: "?B \<subseteq> T"
    using typed_B consistent inf_out D_disjoint
    by (rule CEV_clean_Henkin_extension_from_block)
  have box_in_T: "\<box>\<^sub>o A \<in> T" using B_sub by blast

  text \<open>\<open>T\<close> makes \<open>A\<close> necessary, so it does not contain \<open>\<not> \<box>A\<close>.\<close>
  have negbox_not_T: "Neg (\<box>\<^sub>o A) \<notin> T"
  proof
    assume neg_in: "Neg (\<box>\<^sub>o A) \<in> T"
    have "\<box>\<^sub>o A \<notin> T"
      using T_henkin box_type neg_in
      by (rule CEV_clean_Henkin_formula_absent_of_neg_in)
    then show False using box_in_T by blast
  qed

  text \<open>
    Hence \<open>\<box> (\<not> \<box>A) \<notin> S\<close>: were it in \<open>S\<close> it would be an identity of \<open>S\<close>, hence in the
    diagram, hence in \<open>T\<close>, and modal \<open>T\<close> would extract \<open>\<not> \<box>A\<close> in \<open>T\<close>.
  \<close>
  have box_negbox_not_S: "\<box>\<^sub>o (Neg (\<box>\<^sub>o A)) \<notin> S"
  proof
    assume in_S: "\<box>\<^sub>o (Neg (\<box>\<^sub>o A)) \<in> S"
    have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
    have negbox_supported: "CEV_supported_term C (Neg (\<box>\<^sub>o A))"
      using A_supported unfolding CEV_supported_term_def by simp
    have true_supported: "CEV_supported_term C ObjTrue"
      unfolding CEV_supported_term_def by simp
    have "Eq Prop (Neg (\<box>\<^sub>o A)) ObjTrue
        \<in> CEV_supported_identity_diagram C \<Gamma> S"
      unfolding CEV_supported_identity_diagram_def
      using negbox_type true_type negbox_supported true_supported in_S
      by (auto simp: ObjBox_def)
    then have in_T: "Eq Prop (Neg (\<box>\<^sub>o A)) ObjTrue \<in> T"
      using B_sub by blast
    have boxneg_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg (\<box>\<^sub>o A)) : Prop"
      using negbox_type by (rule typed_ObjBox)
    have in_T': "\<box>\<^sub>o (Neg (\<box>\<^sub>o A)) \<in> T"
      using in_T by (simp add: ObjBox_def)
    have d_box: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o (Neg (\<box>\<^sub>o A))"
      using in_T' boxneg_type by (rule CEV_set_derivable.Assumption)
    have d_T_ax: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s modal_T (Neg (\<box>\<^sub>o A))"
      using CEV_modal_T[OF negbox_type]
      by (rule CEV_set_derivable.Theorem)
    have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg (\<box>\<^sub>o A)"
      using d_box d_T_ax unfolding modal_T_def
      by (rule CEV_set_derivable.Derive_MP)
    then have "Neg (\<box>\<^sub>o A) \<in> T"
      using T_henkin by (rule CEV_clean_Henkin_closed_under_set_derivable
          [rotated])
    then show False using negbox_not_T by blast
  qed

  text \<open>And \<open>\<not> \<box>A \<in> S\<close>, by negation completeness.\<close>
  have negbox_in_S: "Neg (\<box>\<^sub>o A) \<in> S"
  proof -
    have "CEV_negation_complete \<Gamma> S"
      using henkin
      unfolding CEV_clean_Henkin_theory_def CEV_locally_maximal_consistent_def
      by blast
    then have "\<box>\<^sub>o A \<in> S \<or> Neg (\<box>\<^sub>o A) \<in> S"
      unfolding CEV_negation_complete_def using box_type by blast
    then show ?thesis using box_absent by blast
  qed

  text \<open>So 5 itself is absent from \<open>S\<close>, and completeness converts that into
    unprovability.\<close>
  have five_not_S: "modal_5 A \<notin> S"
  proof
    assume five_in: "modal_5 A \<in> S"
    have d_five: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s modal_5 A"
      using five_in typed_modal_5[OF A_type]
      by (rule CEV_set_derivable.Assumption)
    have d_neg: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Neg (\<box>\<^sub>o A)"
      using negbox_in_S negbox_type
      by (rule CEV_set_derivable.Assumption)
    have "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o (Neg (\<box>\<^sub>o A))"
      using d_neg d_five unfolding modal_5_def
      by (rule CEV_set_derivable.Derive_MP)
    then have "\<box>\<^sub>o (Neg (\<box>\<^sub>o A)) \<in> S"
      using henkin by (rule CEV_clean_Henkin_closed_under_set_derivable
          [rotated])
    then show False using box_negbox_not_S by blast
  qed
  show ?thesis
  proof
    assume "\<Gamma> \<turnstile>\<^sub>CEV modal_5 A"
    then have "CEV_clean_Henkin_valid_in_context \<Gamma> (modal_5 A)"
      by (simp add: CEV_clean_Henkin_valid_iff_proves)
    then have "modal_5 A \<in> S"
      using henkin unfolding CEV_clean_Henkin_valid_in_context_def by blast
    then show False using five_not_S by blast
  qed
qed

subsection \<open>The hypotheses are satisfiable\<close>

text \<open>
  A reduction whose premises cannot all be met proves nothing.  The first version of
  this theory had exactly that defect --- it used the full identity diagram and
  demanded \<open>CEV_fresh_extendible_base\<close> of it, which \<open>CEV_identity_diagram_consts_UNIV\<close>
  makes impossible.  So the supported version is discharged here up to the consistency
  condition, using a constant as the witness.
\<close>

lemma CEV_not_proves_box_const:
  "\<not> [] \<turnstile>\<^sub>CEV \<box>\<^sub>o (Const c Prop)"
proof
  assume d: "[] \<turnstile>\<^sub>CEV \<box>\<^sub>o (Const c Prop)"
  have false_type: "[] \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  have "[] \<turnstile>\<^sub>CEV subst_const c Prop ObjFalse (\<box>\<^sub>o (Const c Prop))"
    using d false_type by (rule CEV_proves_subst_const)
  moreover have
    "subst_const c Prop ObjFalse (\<box>\<^sub>o (Const c Prop)) = \<box>\<^sub>o ObjFalse"
    by (simp add: ObjBox_def ObjTrue_def)
  ultimately have "[] \<turnstile>\<^sub>CEV \<box>\<^sub>o ObjFalse" by simp
  then show False using CEV_not_proves_box_ObjFalse by blast
qed

theorem modal_5_reduction_premises_satisfiable:
  obtains K C S where
    "CEV_supported_world K C [] S"
    and "[] \<turnstile> Const c Prop : Prop"
    and "CEV_supported_term C (Const c Prop)"
    and "\<box>\<^sub>o (Const c Prop) \<notin> S"
proof -
  have box_type: "[] \<turnstile> \<box>\<^sub>o (Const c Prop) : Prop"
    by (rule typed_ObjBox) auto
  obtain K C S where finK: "finite K" and neK: "K \<noteq> {}"
    and consts_sub: "consts_of (\<box>\<^sub>o (Const c Prop)) \<subseteq> K"
    and world: "CEV_supported_world K C [] S"
    and absent: "\<box>\<^sub>o (Const c Prop) \<notin> S"
    using box_type CEV_not_proves_box_const
    by (rule CEV_supported_counterworld)
  have KC: "K \<subseteq> C"
    using world unfolding CEV_supported_world_def by blast
  have "CEV_supported_term C (Const c Prop)"
    using consts_sub KC unfolding CEV_supported_term_def by auto
  then show ?thesis
    using that[OF world _ _ absent] by auto
qed

subsection \<open>The residue, and why it is exactly the right residue\<close>

text \<open>
  \<^bold>\<open>What is now proved.\<close>  A countermodel to 5 exists as soon as there is a clean
  Henkin theory \<open>S\<close> and a proposition \<open>A\<close> with \<open>\<box>A \<notin> S\<close> such that the diagram of \<open>S\<close>
  together with \<open>\<box>A\<close> is consistent (and the base has a fresh-constant reserve, which is
  routine).  Every modal step is discharged; nothing about 5 remains except that one
  consistency claim.

  \<^bold>\<open>Why the residue is tight.\<close>  By
  \<open>CEV_identity_diagram_derivable_implies_box_derivable\<close>, inconsistency of
  \<open>insert (\<box>A) (CEV_identity_diagram \<Gamma> S)\<close> means \<open>CEV_identity_diagram \<Gamma> S \<turnstile> \<not> \<box>A\<close>,
  which yields \<open>\<box> (\<not> \<box>A) \<in> S\<close> --- i.e. 5 holding at \<open>S\<close> for \<open>A\<close>.  So the hypothesis is
  not merely sufficient but necessary: the reduction has not thrown anything away, and
  the 5 question \emph{is} this consistency question.

  \<^bold>\<open>Why the obvious discharge cannot work.\<close>  The natural idea is genericity: take \<open>A\<close>
  to be a constant \<open>c\<close> that the diagram says nothing about, so that substituting
  \<open>ObjTrue\<close> for \<open>c\<close> sends a derivation of \<open>\<not> \<box>c\<close> to a derivation of \<open>\<not> \<box>ObjTrue\<close>,
  which is refutable.  The substitution principle this needs \emph{does} exist ---
  \<open>CEV_proves_subst_const\<close> and \<open>CEV_set_derivable_subst_const_clean\<close>.  What fails is
  the freshness, and it fails structurally:

  \<^item> For the \emph{full} diagram no constant is ever fresh.  Reflexive identities
    \<open>Eq Prop (Const c Prop) (Const c Prop)\<close> are theorems, hence lie in every clean
    Henkin theory, hence in its diagram; so \<open>CEV_identity_diagram_consts_UNIV\<close> holds
    and \<open>CEV_fresh_extendible_base\<close> of that diagram is outright unsatisfiable.

  \<^item> For the \emph{supported} diagram at \<open>C\<close> the reserve \<open>UNIV - C\<close> is infinite, which is
    why the theorem above is not vacuous.  But the two requirements on \<open>c\<close> now pull
    apart irreconcilably.  Step \<open>box_negbox_not_S\<close> needs \<open>\<box> (\<not> \<box>c)\<close> to lie in the
    \<open>C\<close>-supported diagram, which forces \<open>c \<in> C\<close>.  Genericity needs \<open>c\<close> fresh for that
    same diagram, which forces \<open>c \<notin> C\<close>.  Shrinking the support to some \<open>C' \<subseteq> C\<close> with
    \<open>c \<notin> C'\<close> restores freshness but removes \<open>\<box> (\<not> \<box>c)\<close> from the diagram, breaking the
    inheritance step.  \<^bold>\<open>The diagram must mention \<open>c\<close> to transmit the modal fact, and
    must not mention \<open>c\<close> to be generic in it.\<close>

  So the genericity route is not merely unfinished, it is closed.  Deciding the residue
  needs a different idea --- e.g. a direct analysis of which boxed formulas a supported
  diagram can derive, or an entirely syntactic proof-theoretic argument about CEV.

  \<^bold>\<open>Honest status.\<close>  The countermodel is not built.  What is built is a lossless
  reduction whose premises are proved satisfiable, together with a proof that the
  obvious way of finishing cannot work.  The conditional consequence from the previous
  theory stands unchanged: if CEV proves 5 then \<open>base_sound\<close> fails for the word action,
  and if not, the word action survives.  Neither disjunct is established here.
\<close>

end
