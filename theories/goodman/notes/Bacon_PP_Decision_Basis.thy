theory Bacon_PP_Decision_Basis
  imports Bacon_PP_Decided_Realization
begin

section \<open>A finite decision basis for the seed-generated logical domain\<close>

text \<open>
  The previous theory shows that a domain generated from a seed by the Boolean
  connectives, the modality and propositional identity always attains, and leaves the
  quantifiers uncontrolled.  The suspicion was that quantification is where the
  induction breaks, because a bound variable ranges over propositions that need not be
  decided wherever the seed is.

  That suspicion is unfounded, and the reason is simple once seen.  A universally
  quantified denotation is just an intersection,
  \<open>pp_forall_over D f = \<Inter>(f ` D)\<close>, and the \emph{value} of the body at each element
  of the domain is itself a domain element.  What has to be decided is not the bound
  variable but the body's value, and decidedness is preserved by arbitrary
  intersections: an intersection of sets each of which is \<open>{}\<close> or \<open>UNIV\<close> is again
  \<open>{}\<close> or \<open>UNIV\<close>.  Existential quantification follows, being a complement of an
  intersection of complements.

  So decidedness at a world is preserved by complement, by the modality, and by
  arbitrary intersections --- which between them cover the Boolean connectives,
  propositional identity, and quantification at every type.  The consequence is the
  target theorem: a domain generated from finitely many propositions by all of these
  has a finite decision basis, and a domain generated from a single seed has the
  one-element basis \<open>{r}\<close>.

  The scope limit is \<open>Pure\<close>, and it is recorded at the end: purity values need not be
  decided where the seed is, so this covers the Pure-free logical fragment.  That is
  precisely the fragment the base-definability discussion concerns.
\<close>

subsection \<open>Decidedness is preserved by arbitrary intersections\<close>

lemma pp_view_Inter:
  "pp_view i (\<Inter> S) = \<Inter> ((pp_view i) ` S)"
  by (auto simp: pp_view_def)

theorem pp_decided_Inter:
  assumes decides: "\<And>X. X \<in> S \<Longrightarrow> i \<in> pp_decided X"
  shows "i \<in> pp_decided (\<Inter> S)"
proof (cases "\<exists>X \<in> S. pp_view i X = {}")
  case True
  then obtain X where X: "X \<in> S" and empty: "pp_view i X = {}"
    by blast
  have "pp_view i (\<Inter> S) \<subseteq> pp_view i X"
    using X by (auto simp: pp_view_Inter)
  then have "pp_view i (\<Inter> S) = {}"
    using empty by blast
  then show ?thesis by (simp add: pp_decided_iff)
next
  case False
  have all_top: "pp_view i X = UNIV" if "X \<in> S" for X
    using decides[OF that] False that by (auto simp: pp_decided_iff)
  have "pp_view i (\<Inter> S) = UNIV"
    unfolding pp_view_Inter using all_top by auto
  then show ?thesis by (simp add: pp_decided_iff)
qed

subsection \<open>The logical closure\<close>

text \<open>
  Complement, the modality and arbitrary intersection.  Binary intersection and union
  are special cases, propositional identity is a boxed biconditional, and both
  quantifiers are intersections up to complement, so this closure contains the whole
  Pure-free logical fragment over its generators.
\<close>

inductive_set pp_qclosure :: "pp_sem_prop set \<Rightarrow> pp_sem_prop set"
  for G :: "pp_sem_prop set" where
    q_base: "X \<in> G \<Longrightarrow> X \<in> pp_qclosure G"
  | q_compl: "X \<in> pp_qclosure G \<Longrightarrow> - X \<in> pp_qclosure G"
  | q_box: "X \<in> pp_qclosure G \<Longrightarrow>
      pp_sem_box X \<in> pp_qclosure G"
  | q_Inter: "(\<And>X. X \<in> S \<Longrightarrow> X \<in> pp_qclosure G) \<Longrightarrow>
      \<Inter> S \<in> pp_qclosure G"

theorem pp_decided_qclosure:
  assumes X: "X \<in> pp_qclosure G"
    and decides: "\<And>g. g \<in> G \<Longrightarrow> i \<in> pp_decided g"
  shows "i \<in> pp_decided X"
  using X
proof (induct rule: pp_qclosure.induct)
  case (q_base X)
  then show ?case by (rule decides)
next
  case (q_compl X)
  then show ?case by simp
next
  case (q_box X)
  then show ?case by (simp add: pp_decided_box)
next
  case (q_Inter S)
  then have "\<And>Y. Y \<in> S \<Longrightarrow> i \<in> pp_decided Y" by blast
  then show ?case by (rule pp_decided_Inter)
qed

subsection \<open>The closure really does contain the logical operations\<close>

lemma pp_qclosure_Int:
  assumes X: "X \<in> pp_qclosure G" and Y: "Y \<in> pp_qclosure G"
  shows "X \<inter> Y \<in> pp_qclosure G"
proof -
  have "\<And>Z. Z \<in> {X, Y} \<Longrightarrow> Z \<in> pp_qclosure G"
    using X Y by blast
  then have "\<Inter> {X, Y} \<in> pp_qclosure G" by (rule q_Inter)
  moreover have "\<Inter> {X, Y} = X \<inter> Y" by simp
  ultimately show ?thesis by simp
qed

lemma pp_qclosure_Un:
  assumes X: "X \<in> pp_qclosure G" and Y: "Y \<in> pp_qclosure G"
  shows "X \<union> Y \<in> pp_qclosure G"
proof -
  have "- X \<inter> - Y \<in> pp_qclosure G"
    using q_compl[OF X] q_compl[OF Y] by (rule pp_qclosure_Int)
  then have compl: "- (- X \<inter> - Y) \<in> pp_qclosure G"
    by (rule q_compl)
  have eq: "- (- X \<inter> - Y) = X \<union> Y" by auto
  show ?thesis using compl unfolding eq .
qed

theorem pp_qclosure_operator_equal:
  assumes A: "A \<in> pp_qclosure G" and B: "B \<in> pp_qclosure G"
  shows "pp_operator_equal A B \<in> pp_qclosure G"
proof -
  have "A \<inter> B \<in> pp_qclosure G"
    using A B by (rule pp_qclosure_Int)
  moreover have "- A \<inter> - B \<in> pp_qclosure G"
    using q_compl[OF A] q_compl[OF B] by (rule pp_qclosure_Int)
  ultimately have "(A \<inter> B) \<union> (- A \<inter> - B) \<in> pp_qclosure G"
    by (rule pp_qclosure_Un)
  then have "pp_sem_box ((A \<inter> B) \<union> (- A \<inter> - B))
      \<in> pp_qclosure G"
    by (rule q_box)
  then show ?thesis
    by (simp add: pp_operator_equal_is_boxed_biconditional)
qed

lemma pp_forall_over_as_Inter:
  "pp_forall_over D f = \<Inter> (f ` D)"
  by (auto simp: pp_forall_over_iff)

theorem pp_qclosure_forall:
  assumes body: "\<And>X. X \<in> D \<Longrightarrow> f X \<in> pp_qclosure G"
  shows "pp_forall_over D f \<in> pp_qclosure G"
proof -
  have "\<And>Z. Z \<in> f ` D \<Longrightarrow> Z \<in> pp_qclosure G"
    using body by blast
  then have "\<Inter> (f ` D) \<in> pp_qclosure G" by (rule q_Inter)
  then show ?thesis by (simp add: pp_forall_over_as_Inter)
qed

lemma pp_exists_over_as_Compl:
  "pp_exists_over D f = - (\<Inter> ((\<lambda>X. - f X) ` D))"
  by (auto simp: pp_exists_over_iff)

theorem pp_qclosure_exists:
  assumes body: "\<And>X. X \<in> D \<Longrightarrow> f X \<in> pp_qclosure G"
  shows "pp_exists_over D f \<in> pp_qclosure G"
proof -
  have "\<And>Z. Z \<in> (\<lambda>X. - f X) ` D \<Longrightarrow> Z \<in> pp_qclosure G"
    using body q_compl by blast
  then have "\<Inter> ((\<lambda>X. - f X) ` D) \<in> pp_qclosure G"
    by (rule q_Inter)
  then have "- (\<Inter> ((\<lambda>X. - f X) ` D)) \<in> pp_qclosure G"
    by (rule q_compl)
  then show ?thesis by (simp add: pp_exists_over_as_Compl)
qed

subsection \<open>The finite decision basis\<close>

theorem pp_qclosure_finite_decision_basis:
  assumes G_fin: "finite G"
    and G_sub: "G \<subseteq> D"
    and D_sub: "D \<subseteq> pp_qclosure G"
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
    have "X \<in> pp_qclosure G" using X D_sub by blast
    then show "i \<in> pp_decided X"
      using decides by (blast intro: pp_decided_qclosure)
  qed
qed

text \<open>
  For a single seed the basis is the seed itself, and the statement becomes an
  inclusion of deciding sets.  This is the strong form that was expected to fail at
  the quantifiers.
\<close>

theorem pp_seed_decision_basis:
  assumes gen: "D \<subseteq> pp_qclosure {r}"
  shows "\<forall>X \<in> D. pp_decided r \<subseteq> pp_decided X"
proof (intro ballI subsetI)
  fix X i
  assume X: "X \<in> D" and i: "i \<in> pp_decided r"
  have "X \<in> pp_qclosure {r}" using X gen by blast
  moreover have "\<And>g. g \<in> {r} \<Longrightarrow> i \<in> pp_decided g"
    using i by simp
  ultimately show "i \<in> pp_decided X"
    by (rule pp_decided_qclosure)
qed

corollary pp_seed_domain_attains_decided:
  assumes seed: "r \<in> D"
    and gen: "D \<subseteq> pp_qclosure {r}"
  shows "pp_finitely_attained D pp_decided"
proof -
  have basis: "\<forall>X \<in> D. pp_decided r \<subseteq> pp_decided X"
    using gen by (rule pp_seed_decision_basis)
  have "pp_forall_over {r} pp_decided \<subseteq> pp_forall_over D pp_decided"
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
      then show "i \<in> pp_decided X"
        using basis i by blast
    qed
  qed
  then show ?thesis
    unfolding pp_finitely_attained_def
    using seed by blast
qed

subsection \<open>Consequence for the counterexample\<close>

text \<open>
  The non-contingency counterexample cannot be realized inside the Pure-free logical
  closure of a seed, at any type.  Quantification does not help, because it is
  intersection and intersection preserves decidedness.
\<close>

corollary pp_counterexample_not_realizable_over_seed:
  assumes seed: "r \<in> D"
    and gen: "D \<subseteq> pp_qclosure {r}"
  shows "\<not> \<not> pp_finitely_attained D pp_decided"
  using pp_seed_domain_attains_decided[OF seed gen] by simp

text \<open>
  Contrapositive, in the form to reach for when testing a proposed realization: if a
  domain fails to attain, it is not contained in the logical closure of any finite set
  of its members.
\<close>

theorem pp_non_attaining_domain_not_finitely_generated:
  assumes fails: "\<not> pp_finitely_attained D pp_decided"
    and G_fin: "finite G"
    and G_sub: "G \<subseteq> D"
  shows "\<not> D \<subseteq> pp_qclosure G"
proof
  assume gen: "D \<subseteq> pp_qclosure G"
  obtain S where S: "S \<subseteq> D" "finite S"
    and basis: "\<forall>i. (\<forall>X \<in> S. i \<in> pp_decided X) \<longrightarrow>
      (\<forall>X \<in> D. i \<in> pp_decided X)"
    using pp_qclosure_finite_decision_basis[OF G_fin G_sub gen] by blast
  have "pp_forall_over S pp_decided \<subseteq> pp_forall_over D pp_decided"
    using basis by (auto simp: pp_forall_over_iff)
  then have "pp_finitely_attained D pp_decided"
    unfolding pp_finitely_attained_def using S by blast
  then show False using fails by simp
qed

subsection \<open>Scope: \<open>Pure\<close> is not covered, and why\<close>

text \<open>
  The closure above covers the Boolean connectives, the modality, propositional
  identity and quantification at every type.  It does not cover \<open>Pure\<close>, and the
  omission is not an oversight.

  A purity value \<open>pp_purity_operator F\<close> is necessitated --- it is its own box --- so
  its views are upward closed, but upward closed is not the same as \<open>{}\<close> or \<open>UNIV\<close>.
  Concretely, a local function whose views are invariant at every world of positive
  depth but not at the root has a purity value that is undecided at the root, however
  the seed behaves there.  So decidedness is not preserved by \<open>Pure\<close>, and the
  induction of \<open>pp_decided_qclosure\<close> has no case for it.

  What this leaves is a clean division.  Inside the Pure-free logical fragment
  generated by a seed, the non-contingency counterexample is dead: the seed alone is a
  decision basis, so the domain attains and persistence holds.  Any realization must
  therefore run through \<open>Pure\<close> itself.  That is a much narrower target than the one
  this line of argument started with, and it is worth noting that it puts the burden
  back on the very predicate whose consistency is at issue.
\<close>

end
