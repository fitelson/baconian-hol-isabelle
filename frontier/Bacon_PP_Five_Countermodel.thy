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

theorem CEV_not_proves_modal_5_of_consistent_diagram:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
    and reserve: "CEV_fresh_extendible_base
      (insert (\<box>\<^sub>o A) (CEV_identity_diagram \<Gamma> S))"
    and consistent: "CEV_consistent \<Gamma>
      (insert (\<box>\<^sub>o A) (CEV_identity_diagram \<Gamma> S))"
  shows "\<not> \<Gamma> \<turnstile>\<^sub>CEV modal_5 A"
proof -
  let ?B = "insert (\<box>\<^sub>o A) (CEV_identity_diagram \<Gamma> S)"
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
    using A_type by (rule typed_ObjBox)
  have negbox_type: "\<Gamma> \<turnstile> Neg (\<box>\<^sub>o A) : Prop"
    using box_type by (rule has_type.Neg)

  text \<open>The base is typed: the diagram sits inside the typed theory \<open>S\<close>.\<close>
  have diagram_sub: "CEV_identity_diagram \<Gamma> S \<subseteq> S"
    by (auto simp: CEV_identity_diagram_iff)
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
      assume "X \<in> CEV_identity_diagram \<Gamma> S"
      then have "X \<in> S" using diagram_sub by blast
      then show ?thesis
        using S_typed unfolding typed_theory_def by blast
    qed
  qed

  text \<open>So the base extends to a clean Henkin theory \<open>T\<close>, a successor of \<open>S\<close>.\<close>
  obtain T where T_henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and B_sub: "?B \<subseteq> T"
    using reserve typed_B consistent
    by (rule CEV_clean_Henkin_extension_from_fresh_extendible_base)
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
    have "Eq Prop (Neg (\<box>\<^sub>o A)) ObjTrue \<in> CEV_identity_diagram \<Gamma> S"
      unfolding CEV_identity_diagram_iff
      using negbox_type true_type in_S
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

  \<^bold>\<open>What blocks the last step, precisely.\<close>  The natural discharge is genericity: take
  \<open>A\<close> to be a constant \<open>c\<close> not occurring in the diagram; then the diagram says nothing
  about \<open>c\<close>, and substituting \<open>ObjTrue\<close> for \<open>c\<close> would send a derivation of \<open>\<not> \<box>c\<close> to a
  derivation of \<open>\<not> \<box>ObjTrue\<close>, which is refutable.  This needs a lemma stating that
  \<^bold>\<open>CEV-derivability is preserved when a well-typed closed term is substituted for a
  constant\<close>.  The repository does not have it.  \<open>Bacon_Substitution\<close> is about
  \emph{variables}; the constant apparatus (\<open>consts_of\<close>, \<open>fresh_const_for\<close>) supplies
  freshness bookkeeping and Henkin witnesses but no substitution principle for
  constants.  The relevant lemma would be, in outline,

  \begin{center}
  \<open>\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV (A[N/c])\<close>
  \end{center}

  proved by induction over the CEV rules, with the vector-equivalence rule the only
  interesting case.  That is a self-contained and unglamorous piece of work, and it is
  now the \emph{only} thing between the development and a decision on 5.

  \<^bold>\<open>Honest status.\<close>  The countermodel is not built.  What is built is a reduction that
  is provably lossless, plus an exact identification of the missing lemma.  The
  conditional consequence from the previous theory therefore stands unchanged: if CEV
  proves 5 then \<open>base_sound\<close> fails for the word action, and if not, the word action
  survives.  Neither disjunct is established here.
\<close>

end
