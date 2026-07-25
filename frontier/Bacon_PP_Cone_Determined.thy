theory Bacon_PP_Cone_Determined
  imports Bacon_PP_Pure_Decision_Basis
begin

section \<open>The induction for cone-determinedness\<close>

text \<open>
  \<open>pp_cone_determined\<close> was introduced as the semantic surrogate for ``definable from
  the generators'', and used with the standing caveat that the induction showing every
  definable function has the property had not been carried out.  This theory carries
  it out, over the generating operations, in exactly the style the rest of the
  development uses for propositions.

  The pattern is the one that already worked twice.  Cone-determinedness is a
  statement about how a value's local view varies with the world, and every logical
  operation computes the local view of its result from the local views of its
  arguments: complement commutes with the view, so does the modality, so does
  arbitrary intersection, and so --- by the equivariance already proved --- does
  \<open>Pure\<close>.  Nothing in the logical vocabulary can look at the world except through the
  generators, so two worlds agreeing on the generators agree on everything built from
  them.

  Both levels are treated.  Propositions get \<open>pp_cone_det_prop\<close> and the closure
  \<open>pp_qclosure\<close> already defined; unary operators get \<open>pp_cone_determined\<close> and a new
  closure \<open>pp_fclosure\<close> whose rules are the identity, cone-determined constants,
  complement, the modality and arbitrary intersection --- between them the Boolean
  connectives, propositional identity and quantification at every type.

  The payoff is that the side condition of the \<open>p_pure\<close> rule is discharged rather
  than assumed: every operator in \<open>pp_fclosure G\<close> is cone-determined by \<open>G\<close>, so its
  purity value may be added to the propositional closure.  What remains unformalized
  is narrower than before, and is recorded at the end.
\<close>

subsection \<open>Cone-determinedness for propositions\<close>

definition pp_cone_det_prop ::
    "pp_sem_prop set \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_cone_det_prop G X \<longleftrightarrow>
    (\<forall>i i'. (\<forall>g \<in> G. pp_view i g = pp_view i' g) \<longrightarrow>
      pp_view i X = pp_view i' X)"

lemma pp_cone_det_propI:
  assumes "\<And>i i'. (\<forall>g \<in> G. pp_view i g = pp_view i' g) \<Longrightarrow>
    pp_view i X = pp_view i' X"
  shows "pp_cone_det_prop G X"
  using assms unfolding pp_cone_det_prop_def by blast

lemma pp_cone_det_propD:
  assumes "pp_cone_det_prop G X"
    and "\<forall>g \<in> G. pp_view i g = pp_view i' g"
  shows "pp_view i X = pp_view i' X"
  using assms unfolding pp_cone_det_prop_def by blast

theorem pp_qclosure_cone_det:
  assumes X: "X \<in> pp_qclosure G"
  shows "pp_cone_det_prop G X"
  using X
proof (induct rule: pp_qclosure.induct)
  case (q_base X)
  show ?case
    by (rule pp_cone_det_propI) (use q_base in blast)
next
  case (q_compl X)
  show ?case
  proof (rule pp_cone_det_propI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have "pp_view i X = pp_view i' X"
      using q_compl agree by (blast dest: pp_cone_det_propD)
    then show "pp_view i (- X) = pp_view i' (- X)"
      by (simp add: pp_view_Compl_local)
  qed
next
  case (q_box X)
  show ?case
  proof (rule pp_cone_det_propI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have "pp_view i X = pp_view i' X"
      using q_box agree by (blast dest: pp_cone_det_propD)
    then show "pp_view i (pp_sem_box X) =
        pp_view i' (pp_sem_box X)"
      by (simp add: pp_sem_box_equivariant)
  qed
next
  case (q_Inter S)
  show ?case
  proof (rule pp_cone_det_propI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have pointwise: "pp_view i Y = pp_view i' Y" if "Y \<in> S" for Y
      using q_Inter that agree by (blast dest: pp_cone_det_propD)
    have "(pp_view i) ` S = (pp_view i') ` S"
      using pointwise by force
    then show "pp_view i (\<Inter> S) = pp_view i' (\<Inter> S)"
      by (simp add: pp_view_Inter)
  qed
qed

subsection \<open>Purity values are cone-determined\<close>

text \<open>
  This is where the equivariance of the purity operator does the work: the local view
  of a purity value is the purity value of the local view of the function.
\<close>

theorem pp_cone_determined_purity:
  assumes det: "pp_cone_determined G F"
  shows "pp_cone_det_prop G (pp_purity_operator F)"
proof (rule pp_cone_det_propI)
  fix i i'
  assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
  have "pp_fun_view i F = pp_fun_view i' F"
    using det agree unfolding pp_cone_determined_def by blast
  then show "pp_view i (pp_purity_operator F) =
      pp_view i' (pp_purity_operator F)"
    by (simp add: pp_purity_operator_equivariant)
qed

subsection \<open>The closure of unary operators\<close>

inductive_set pp_fclosure ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  for G :: "pp_sem_prop set" where
    f_id: "(\<lambda>P. P) \<in> pp_fclosure G"
  | f_const: "pp_cone_det_prop G X \<Longrightarrow>
      (\<lambda>P. X) \<in> pp_fclosure G"
  | f_compl: "F \<in> pp_fclosure G \<Longrightarrow>
      (\<lambda>P. - F P) \<in> pp_fclosure G"
  | f_box: "F \<in> pp_fclosure G \<Longrightarrow>
      (\<lambda>P. pp_sem_box (F P)) \<in> pp_fclosure G"
  | f_Inter: "(\<And>F. F \<in> S \<Longrightarrow> F \<in> pp_fclosure G) \<Longrightarrow>
      (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S)) \<in> pp_fclosure G"

subsection \<open>How the action computes on the closure\<close>

lemma pp_fun_view_id:
  "pp_fun_view i (\<lambda>P. P) = (\<lambda>P. P)"
  by (rule ext) (simp add: pp_fun_view_apply)

lemma pp_fun_view_const:
  "pp_fun_view i (\<lambda>P. X) = (\<lambda>P. pp_view i X)"
  by (rule ext) (simp add: pp_fun_view_apply)

lemma pp_fun_view_compl:
  "pp_fun_view i (\<lambda>P. - F P) =
    (\<lambda>P. - pp_fun_view i F P)"
  by (rule ext)
    (simp add: pp_fun_view_apply pp_view_Compl_local)

lemma pp_fun_view_boxop:
  "pp_fun_view i (\<lambda>P. pp_sem_box (F P)) =
    (\<lambda>P. pp_sem_box (pp_fun_view i F P))"
  by (rule ext)
    (simp add: pp_fun_view_apply pp_sem_box_equivariant)

lemma pp_fun_view_Interop:
  "pp_fun_view i (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S)) =
    (\<lambda>P. \<Inter> ((\<lambda>F. pp_fun_view i F P) ` S))"
proof (rule ext)
  fix P
  have "pp_fun_view i (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S)) P =
      pp_view i (\<Inter> ((\<lambda>F. F (pp_lift i P)) ` S))"
    by (simp add: pp_fun_view_apply)
  also have "... =
      \<Inter> ((pp_view i) ` ((\<lambda>F. F (pp_lift i P)) ` S))"
    by (rule pp_view_Inter)
  also have "... =
      \<Inter> ((\<lambda>F. pp_view i (F (pp_lift i P))) ` S)"
    by (simp add: image_image)
  also have "... = \<Inter> ((\<lambda>F. pp_fun_view i F P) ` S)"
    by (simp add: pp_fun_view_apply)
  finally show "pp_fun_view i (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S)) P =
      \<Inter> ((\<lambda>F. pp_fun_view i F P) ` S)" .
qed

subsection \<open>The induction\<close>

theorem pp_fclosure_cone_determined:
  assumes F: "F \<in> pp_fclosure G"
  shows "pp_cone_determined G F"
  using F
proof (induct rule: pp_fclosure.induct)
  case f_id
  show ?case
    unfolding pp_cone_determined_def
    by (simp add: pp_fun_view_id)
next
  case (f_const X)
  show ?case
    unfolding pp_cone_determined_def
  proof (intro allI impI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have "pp_view i X = pp_view i' X"
      using f_const agree by (blast dest: pp_cone_det_propD)
    then show "pp_fun_view i (\<lambda>P. X) = pp_fun_view i' (\<lambda>P. X)"
      by (simp add: pp_fun_view_const)
  qed
next
  case (f_compl F)
  show ?case
    unfolding pp_cone_determined_def
  proof (intro allI impI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have "pp_fun_view i F = pp_fun_view i' F"
      using f_compl agree unfolding pp_cone_determined_def by blast
    then show "pp_fun_view i (\<lambda>P. - F P) =
        pp_fun_view i' (\<lambda>P. - F P)"
      by (simp add: pp_fun_view_compl)
  qed
next
  case (f_box F)
  show ?case
    unfolding pp_cone_determined_def
  proof (intro allI impI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have "pp_fun_view i F = pp_fun_view i' F"
      using f_box agree unfolding pp_cone_determined_def by blast
    then show "pp_fun_view i (\<lambda>P. pp_sem_box (F P)) =
        pp_fun_view i' (\<lambda>P. pp_sem_box (F P))"
      by (simp add: pp_fun_view_boxop)
  qed
next
  case (f_Inter S)
  show ?case
    unfolding pp_cone_determined_def
  proof (intro allI impI)
    fix i i'
    assume agree: "\<forall>g \<in> G. pp_view i g = pp_view i' g"
    have pointwise: "pp_fun_view i H = pp_fun_view i' H"
      if "H \<in> S" for H
      using f_Inter that agree
      unfolding pp_cone_determined_def by blast
    have "(\<lambda>P. \<Inter> ((\<lambda>H. pp_fun_view i H P) ` S)) =
        (\<lambda>P. \<Inter> ((\<lambda>H. pp_fun_view i' H P) ` S))"
    proof (rule ext)
      fix P
      have "(\<lambda>H. pp_fun_view i H P) ` S =
          (\<lambda>H. pp_fun_view i' H P) ` S"
        using pointwise by force
      then show "\<Inter> ((\<lambda>H. pp_fun_view i H P) ` S) =
          \<Inter> ((\<lambda>H. pp_fun_view i' H P) ` S)"
        by simp
    qed
    then show "pp_fun_view i (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S)) =
        pp_fun_view i' (\<lambda>P. \<Inter> ((\<lambda>F. F P) ` S))"
      by (simp add: pp_fun_view_Interop)
  qed
qed

subsection \<open>The \<open>p_pure\<close> side condition is discharged\<close>

corollary pp_fclosure_purity_in_pclosure:
  assumes F: "F \<in> pp_fclosure G"
  shows "pp_purity_operator F \<in> pp_pclosure G"
  using pp_fclosure_cone_determined[OF F] by (rule p_pure)

corollary pp_fclosure_purity_cone_det:
  assumes F: "F \<in> pp_fclosure G"
  shows "pp_cone_det_prop G (pp_purity_operator F)"
  using pp_fclosure_cone_determined[OF F]
  by (rule pp_cone_determined_purity)

text \<open>
  So the purity value of any operator built from the generators by the logical
  operations may be added to the propositional closure without assuming anything, and
  the decision-basis theorems apply to it.  In particular
  \<open>pp_pure_seed_decision_basis\<close> is no longer conditional on an unproved
  cone-determinedness hypothesis for the operators it quantifies over.
\<close>

subsection \<open>Closure operators are Bacon-local\<close>

text \<open>
  A sanity check that the closure does not stray outside Bacon's function domain.
\<close>

theorem pp_fclosure_member:
  assumes F: "F \<in> pp_fclosure G"
  shows "pp_function_space_member F"
  using F
proof (induct rule: pp_fclosure.induct)
  case f_id
  show ?case by (simp add: pp_function_space_member_def)
next
  case (f_const X)
  show ?case by (simp add: pp_function_space_member_def)
next
  case (f_compl F)
  show ?case
    unfolding pp_function_space_member_def
  proof (intro allI impI)
    fix j P Q
    assume "pp_view j P = pp_view j Q"
    then have "pp_view j (F P) = pp_view j (F Q)"
      using f_compl unfolding pp_function_space_member_def by blast
    then show "pp_view j (- F P) = pp_view j (- F Q)"
      by (simp add: pp_view_Compl_local)
  qed
next
  case (f_box F)
  show ?case
    unfolding pp_function_space_member_def
  proof (intro allI impI)
    fix j P Q
    assume "pp_view j P = pp_view j Q"
    then have "pp_view j (F P) = pp_view j (F Q)"
      using f_box unfolding pp_function_space_member_def by blast
    then show "pp_view j (pp_sem_box (F P)) =
        pp_view j (pp_sem_box (F Q))"
      by (simp add: pp_sem_box_equivariant)
  qed
next
  case (f_Inter S)
  show ?case
    unfolding pp_function_space_member_def
  proof (intro allI impI)
    fix j P Q
    assume views: "pp_view j P = pp_view j Q"
    have pointwise: "pp_view j (H P) = pp_view j (H Q)"
      if "H \<in> S" for H
      using f_Inter that views
      unfolding pp_function_space_member_def by blast
    have "(\<lambda>H. pp_view j (H P)) ` S =
        (\<lambda>H. pp_view j (H Q)) ` S"
      using pointwise by force
    then show "pp_view j (\<Inter> ((\<lambda>F. F P) ` S)) =
        pp_view j (\<Inter> ((\<lambda>F. F Q) ` S))"
      by (simp add: pp_view_Inter image_image)
  qed
qed

subsection \<open>What is now closed, and what is not\<close>

text \<open>
  Closed.  The induction for cone-determinedness is done, over the generating
  operations, at both levels: propositions in \<open>pp_qclosure\<close> and operators in
  \<open>pp_fclosure\<close>.  Since propositional identity is a boxed biconditional and both
  quantifiers are intersections up to complement, the operator closure covers the
  Boolean connectives, identity and quantification at every type.  The \<open>p_pure\<close> side
  condition is therefore discharged for every operator so built, and the
  decision-basis results stand without it as an assumption.

  Not closed, and the statement of it is now much narrower than the caveat it
  replaces.  Two things remain.

  First, operators in which the argument occurs \emph{inside} a \<open>Pure\<close>, such as
  \<open>\<lambda>P. Pure (\<lambda>Q. P \<and> Q)\<close>, are not generated by \<open>pp_fclosure\<close>.  That particular one
  is harmless --- by \<open>pp_purity_of_meet\<close> it is \<open>\<lambda>P. \<box>P \<or> \<box>\<not>P\<close>, whose local views
  do not depend on the world at all --- but the general case needs a closure at the
  next type up, and is not treated here.

  Second, the connection to the project's deep-embedded syntax is still not made.
  What is formalized is an induction over semantic generating operations, which is the
  content the surrogate needs; identifying those operations with the denotations of
  \<open>oterm\<close> constructors is the remaining bridge, and it is the same bridge the
  fixed-term theorem of \<open>Bacon_PP_TypeCoherence\<close> needs.  These are now the only two
  gaps of this kind left in the development, and they are the same gap.
\<close>

end
