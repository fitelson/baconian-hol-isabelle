theory Bacon_PP_Pure_Decision_Basis
  imports
    Bacon_PP_Decision_Basis
    "Higher_Order_Metaphysics_PP.Bacon_PP_Purity_Operator"
begin

section \<open>Closing the last route: \<open>Pure\<close> does not break the decision basis\<close>

text \<open>
  The decision-basis theorem covers the Boolean connectives, the modality,
  propositional identity and quantification at every type, and leaves \<open>Pure\<close> as the
  only way a realization of the non-contingency counterexample could still get in.
  This theory closes that route too.

  Two things are proved.  First an identity worth seeing on its own: applying \<open>Pure\<close>
  to the operator that conjoins with \<open>b\<close> gives exactly \emph{non-contingency of}
  \<open>b\<close>,

  \begin{center}
  \<open>Pure (\<lambda>P. b \<and> P) = \<box>b \<or> \<box>\<not>b\<close>.
  \end{center}

  So the body of the counterexample is not an arbitrary choice at all: it is what
  \<open>Pure\<close> computes.  That is the strongest reason to expect \<open>Pure\<close> to be the route in.

  Second, and decisively, it is not.  If a world decides every generator, then every
  function definable from those generators has an invariant local view there --- the
  cone above such a world is uniform for the generators, so nothing in it can vary ---
  and hence the world lies inside the purity value, which is necessitated and so
  decided there.  Adding \<open>Pure\<close> to the closure therefore preserves the decision
  basis, and the counterexample is unrealizable in the full logical closure of a seed.

  The semantic surrogate for ``definable from the generators'' is
  \<open>pp_cone_determined\<close>: the local view of \<open>F\<close> at a world depends only on the local
  views of the generators there.  Every term-definable function has this property; the
  proof of that is the object-language term induction and is not formalized here.
\<close>

subsection \<open>Purity of a conjunction operator is non-contingency\<close>

lemma pp_fun_view_meet:
  "pp_fun_view i (\<lambda>P. b \<inter> P) = (\<lambda>P. pp_view i b \<inter> P)"
proof (rule ext)
  fix P
  have "pp_fun_view i (\<lambda>P. b \<inter> P) P =
      pp_view i (b \<inter> pp_lift i P)"
    by (simp add: pp_fun_view_apply)
  also have "... = pp_view i b \<inter> pp_view i (pp_lift i P)"
    by (rule pp_view_Int_local)
  also have "... = pp_view i b \<inter> P"
    by simp
  finally show "pp_fun_view i (\<lambda>P. b \<inter> P) P = pp_view i b \<inter> P" .
qed

lemma pp_meet_invariant_iff:
  "pp_fun_invariant (\<lambda>P. c \<inter> P) \<longleftrightarrow>
    pp_invariant_proposition c"
proof
  assume inv: "pp_fun_invariant (\<lambda>P. c \<inter> P)"
  show "pp_invariant_proposition c"
    unfolding pp_invariant_proposition_def
  proof
    fix k
    have "pp_fun_view k (\<lambda>P. c \<inter> P) = (\<lambda>P. c \<inter> P)"
      using inv unfolding pp_fun_invariant_def by blast
    then have "(\<lambda>P. pp_view k c \<inter> P) = (\<lambda>P. c \<inter> P)"
      by (simp add: pp_fun_view_meet)
    then have "pp_view k c \<inter> UNIV = c \<inter> UNIV"
      by (rule fun_cong)
    then show "pp_view k c = c" by simp
  qed
next
  assume inv: "pp_invariant_proposition c"
  show "pp_fun_invariant (\<lambda>P. c \<inter> P)"
    unfolding pp_fun_invariant_def
  proof
    fix k
    have "pp_view k c = c"
      using inv unfolding pp_invariant_proposition_def by blast
    then show "pp_fun_view k (\<lambda>P. c \<inter> P) = (\<lambda>P. c \<inter> P)"
      by (simp add: pp_fun_view_meet)
  qed
qed

theorem pp_purity_of_meet:
  "pp_purity_operator (\<lambda>P. b \<inter> P) = pp_decided b"
proof (rule set_eqI)
  fix i
  have "i \<in> pp_purity_operator (\<lambda>P. b \<inter> P) \<longleftrightarrow>
      pp_fun_invariant (pp_fun_view i (\<lambda>P. b \<inter> P))"
    by (simp add: pp_purity_operator_membership)
  also have "... \<longleftrightarrow>
      pp_fun_invariant (\<lambda>P. pp_view i b \<inter> P)"
    by (simp add: pp_fun_view_meet)
  also have "... \<longleftrightarrow> pp_invariant_proposition (pp_view i b)"
    by (rule pp_meet_invariant_iff)
  also have "... \<longleftrightarrow>
      (pp_view i b = {} \<or> pp_view i b = UNIV)"
    by (auto simp: pp_invariant_proposition_iff_extreme)
  also have "... \<longleftrightarrow> i \<in> pp_decided b"
    by (auto simp: pp_decided_iff)
  finally show "i \<in> pp_purity_operator (\<lambda>P. b \<inter> P) \<longleftrightarrow>
      i \<in> pp_decided b" .
qed

text \<open>
  So \<open>Pure\<close> really does compute the body of the counterexample.  If anything could
  realize it, this is what one would expect to do it.
\<close>

subsection \<open>Functions determined by the generators\<close>

lemma pp_fun_invariant_view_iff:
  "pp_fun_invariant (pp_fun_view i F) \<longleftrightarrow>
    (\<forall>k. pp_fun_view (k @ i) F = pp_fun_view i F)"
  by (auto simp: pp_fun_invariant_def pp_fun_view_compose)

definition pp_cone_determined ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool"
  where
  "pp_cone_determined G F \<longleftrightarrow>
    (\<forall>i i'. (\<forall>g \<in> G. pp_view i g = pp_view i' g) \<longrightarrow>
      pp_fun_view i F = pp_fun_view i' F)"

text \<open>
  The key step.  A world that decides every generator sees a cone on which the
  generators are constant, so a function determined by them cannot vary there, and its
  local view is invariant --- that is, the world lies inside the purity value.
\<close>

theorem pp_decided_generators_give_purity:
  assumes det: "pp_cone_determined G F"
    and decides: "\<And>g. g \<in> G \<Longrightarrow> i \<in> pp_decided g"
  shows "i \<in> pp_purity_operator F"
proof -
  have same: "pp_view (k @ i) g = pp_view i g" if g: "g \<in> G" for k g
  proof -
    have compose: "pp_view (k @ i) g = pp_view k (pp_view i g)"
      by (simp add: pp_view_compose)
    have "pp_view i g = {} \<or> pp_view i g = UNIV"
      using decides[OF g] by (auto simp: pp_decided_iff)
    then show ?thesis using compose by auto
  qed
  have "pp_fun_view (k @ i) F = pp_fun_view i F" for k
    using det same unfolding pp_cone_determined_def by blast
  then show ?thesis
    by (simp add: pp_purity_operator_membership
        pp_fun_invariant_view_iff)
qed

corollary pp_decided_generators_decide_purity:
  assumes det: "pp_cone_determined G F"
    and decides: "\<And>g. g \<in> G \<Longrightarrow> i \<in> pp_decided g"
  shows "i \<in> pp_decided (pp_purity_operator F)"
proof -
  have inside: "i \<in> pp_purity_operator F"
    using det decides by (rule pp_decided_generators_give_purity)
  have "pp_purity_operator F =
      pp_sem_box (pp_purity_operator F)"
    by (rule pp_purity_operator_necessitated)
  then have "i \<in> pp_sem_box (pp_purity_operator F)"
    using inside by simp
  then have "pp_view i (pp_purity_operator F) = UNIV"
    by (simp add: pp_sem_box_def)
  then show ?thesis by (simp add: pp_decided_iff)
qed

subsection \<open>The closure with \<open>Pure\<close>\<close>

inductive_set pp_pclosure :: "pp_sem_prop set \<Rightarrow> pp_sem_prop set"
  for G :: "pp_sem_prop set" where
    p_base: "X \<in> G \<Longrightarrow> X \<in> pp_pclosure G"
  | p_compl: "X \<in> pp_pclosure G \<Longrightarrow> - X \<in> pp_pclosure G"
  | p_box: "X \<in> pp_pclosure G \<Longrightarrow>
      pp_sem_box X \<in> pp_pclosure G"
  | p_Inter: "(\<And>X. X \<in> S \<Longrightarrow> X \<in> pp_pclosure G) \<Longrightarrow>
      \<Inter> S \<in> pp_pclosure G"
  | p_pure: "pp_cone_determined G F \<Longrightarrow>
      pp_purity_operator F \<in> pp_pclosure G"

theorem pp_decided_pclosure:
  assumes X: "X \<in> pp_pclosure G"
    and decides: "\<And>g. g \<in> G \<Longrightarrow> i \<in> pp_decided g"
  shows "i \<in> pp_decided X"
  using X
proof (induct rule: pp_pclosure.induct)
  case (p_base X)
  then show ?case by (rule decides)
next
  case (p_compl X)
  then show ?case by simp
next
  case (p_box X)
  then show ?case by (simp add: pp_decided_box)
next
  case (p_Inter S)
  then have "\<And>Y. Y \<in> S \<Longrightarrow> i \<in> pp_decided Y" by blast
  then show ?case by (rule pp_decided_Inter)
next
  case (p_pure F)
  then show ?case
    using decides by (rule pp_decided_generators_decide_purity)
qed

subsection \<open>The full decision basis\<close>

theorem pp_pclosure_finite_decision_basis:
  assumes G_fin: "finite G"
    and G_sub: "G \<subseteq> D"
    and D_sub: "D \<subseteq> pp_pclosure G"
  shows "\<exists>S. S \<subseteq> D \<and> finite S \<and>
    (\<forall>i. (\<forall>X \<in> S. i \<in> pp_decided X) \<longrightarrow>
         (\<forall>X \<in> D. i \<in> pp_decided X))"
proof (intro exI[of _ G] conjI)
  show "G \<subseteq> D" by (rule G_sub)
next
  show "finite G" by (rule G_fin)
next
  show "\<forall>i. (\<forall>X \<in> G. i \<in> pp_decided X) \<longrightarrow>
      (\<forall>X \<in> D. i \<in> pp_decided X)"
  proof (intro allI impI ballI)
    fix i X
    assume decides: "\<forall>X \<in> G. i \<in> pp_decided X"
      and X: "X \<in> D"
    have "X \<in> pp_pclosure G" using X D_sub by blast
    then show "i \<in> pp_decided X"
      using decides by (blast intro: pp_decided_pclosure)
  qed
qed

theorem pp_pure_seed_decision_basis:
  assumes gen: "D \<subseteq> pp_pclosure {r}"
  shows "\<forall>X \<in> D. pp_decided r \<subseteq> pp_decided X"
proof (intro ballI subsetI)
  fix X i
  assume X: "X \<in> D" and i: "i \<in> pp_decided r"
  have "X \<in> pp_pclosure {r}" using X gen by blast
  moreover have "\<And>g. g \<in> {r} \<Longrightarrow> i \<in> pp_decided g"
    using i by simp
  ultimately show "i \<in> pp_decided X"
    by (rule pp_decided_pclosure)
qed

corollary pp_pure_seed_domain_attains_decided:
  assumes seed: "r \<in> D"
    and gen: "D \<subseteq> pp_pclosure {r}"
  shows "pp_finitely_attained D pp_decided"
proof -
  have basis: "\<forall>X \<in> D. pp_decided r \<subseteq> pp_decided X"
    using gen by (rule pp_pure_seed_decision_basis)
  have "pp_forall_over {r} pp_decided \<subseteq>
      pp_forall_over D pp_decided"
  proof
    fix i
    assume "i \<in> pp_forall_over {r} pp_decided"
    then have i: "i \<in> pp_decided r"
      by (simp add: pp_forall_over_iff)
    show "i \<in> pp_forall_over D pp_decided"
      unfolding pp_forall_over_iff
    proof (intro ballI)
      fix X
      assume "X \<in> D"
      then show "i \<in> pp_decided X" using basis i by blast
    qed
  qed
  then show ?thesis
    unfolding pp_finitely_attained_def using seed by blast
qed

subsection \<open>Verdict\<close>

text \<open>
  The non-contingency counterexample cannot be realized inside the logical closure of a
  seed, and \<open>Pure\<close> does not change that.  The seed alone remains a decision basis, so
  the domain attains and persistence holds.

  This is worth stating carefully, because \<open>pp_purity_of_meet\<close> shows \<open>Pure\<close> really
  does compute the counterexample's body.  What defeats the realization is not that
  \<open>Pure\<close> cannot reach non-contingency, but that it can only reach the non-contingency
  of things determined by the generators --- and at a world where the generators are
  decided, everything so determined is invariant, hence pure, hence decided.  The
  operator that would be needed, one becoming invariant exactly below some finite
  depth, requires a depth predicate as a parameter, which is the very thing the
  construction cannot supply.

  Scope.  \<open>pp_cone_determined\<close> is the semantic surrogate for ``definable from the
  generators''.  The claim that every term-definable function is cone-determined is
  the object-language term induction and is not formalized here; it is the same
  standing gap as elsewhere in this development.  Subject to that, the route through
  \<open>Pure\<close> is closed, and with it the last route this line of argument had left.
\<close>

end
