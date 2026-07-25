theory Bacon_PP_Seed_Nontriviality
  imports Bacon_PP_Diagonal_Reduction
begin

section \<open>The seed cannot be drawn from the seed-free term model\<close>

text \<open>
  The cheapest way to make the quantifier domains seed-independent would be to take
  the seed from inside a domain that was already closed before the seed was
  introduced.  Build the term model \<open>D\<^sub>0\<close> over the seed-free language --- logical
  constants and \<open>Pure\<close>, no \<open>Fun\<close> and no name for the fundamental proposition.  That
  model is countable and manifestly seed-independent.  If a fundamental proposition
  could be found inside \<open>D\<^sub>0\<close> at type \<open>Prop\<close>, then adjoining it would enlarge
  nothing, the domains would stay fixed, the family set would be a single countable
  set, and the envelope hypothesis of \<open>Bacon_PP_Stock_Requirements\<close> would hold
  outright.

  This theory shows that route is closed.  A closed seed-free term has no free
  parameter, so its denotation is invariant; and \<open>pp_invariant_proposition_iff_extreme\<close>
  says the only invariant propositions are \<open>{}\<close> and \<open>UNIV\<close>.  An invariant
  proposition has a one-point orbit, and a one-point orbit is trapped inside a proper
  classifier index --- indeed inside a \emph{Pure-free definable} one, since the two
  relevant classifiers are exactly \<open>\<box>\<close> and \<open>\<box>\<circ>\<not>\<close>.  So Recombination fails at any
  such seed.

  The moral is that the fundamental proposition must be genuinely contingent, and in
  particular must lie outside every seed-free domain.  Seed-independence of the
  quantifier domains therefore cannot be bought this way; it has to be bought, if at
  all, by keeping the seed out of the range of the quantifiers, which is a different
  and much more delicate proposal.
\<close>

subsection \<open>The two extreme classifiers are the modal operators\<close>

theorem pp_box_is_classifier_UNIV:
  "pp_sem_box = pp_classifier {UNIV}"
proof (rule ext)
  fix P
  show "pp_sem_box P = pp_classifier {UNIV} P"
    by (auto simp: pp_sem_box_def pp_classifier_def)
qed

theorem pp_box_neg_is_classifier_empty:
  "(\<lambda>P. pp_sem_box (- P)) = pp_classifier {{}}"
proof (rule ext)
  fix P
  have "pp_sem_box (- P) = {i. pp_view i (- P) = UNIV}"
    by (simp add: pp_sem_box_def)
  also have "... = {i. pp_view i P = {}}"
    by (auto simp: pp_view_def)
  also have "... = pp_classifier {{}} P"
    by (simp add: pp_classifier_def)
  finally show "pp_sem_box (- P) = pp_classifier {{}} P" .
qed

subsection \<open>An invariant seed has a one-point orbit\<close>

lemma pp_invariant_orbit_singleton:
  assumes "pp_invariant_proposition r"
  shows "pp_orbit r = {r}"
proof (rule set_eqI)
  fix P
  have views: "pp_view i r = r" for i
    using assms unfolding pp_invariant_proposition_def by blast
  show "P \<in> pp_orbit r \<longleftrightarrow> P \<in> {r}"
    unfolding pp_orbit_def using views by auto
qed

lemma pp_sem_prop_not_singleton:
  "{r :: pp_sem_prop} \<noteq> UNIV"
proof
  assume "{r} = UNIV"
  then have "({} :: pp_sem_prop) \<in> {r}" and "(UNIV :: pp_sem_prop) \<in> {r}"
    by auto
  then have "({} :: pp_sem_prop) = UNIV"
    by simp
  moreover have "([] :: pp_word) \<in> (UNIV :: pp_sem_prop)"
    by simp
  ultimately show False by auto
qed

subsection \<open>Recombination fails at an invariant seed\<close>

theorem pp_invariant_seed_fails_recombination:
  assumes invariant: "pp_invariant_proposition r"
  shows "\<not> pp_root_unary_recombination (pp_orbit r) r"
proof -
  have orbit: "pp_orbit r = {r}"
    using invariant by (rule pp_invariant_orbit_singleton)
  have proper: "pp_orbit r \<noteq> UNIV"
    using orbit pp_sem_prop_not_singleton by simp
  have "pp_orbit r \<subseteq> pp_orbit r" by simp
  then show ?thesis
    using proper by (simp add: pp_root_unary_recombination_iff)
qed

text \<open>
  Sharper: the offending classifier index is not merely some proper set, it is one of
  the two whose classifiers are \<open>\<box>\<close> and \<open>\<box>\<circ>\<not>\<close>.  Those are Pure-free definable, so
  they are in any stock closed under the logical constants, and the failure cannot be
  dodged by trimming the stock.
\<close>

theorem pp_extreme_seed_fails_definable_recombination:
  assumes invariant: "pp_invariant_proposition r"
  shows "(r = UNIV \<longrightarrow>
            \<not> pp_root_unary_recombination {UNIV} r) \<and>
         (r = {} \<longrightarrow>
            \<not> pp_root_unary_recombination {{}} r)"
proof (intro conjI impI)
  assume r: "r = UNIV"
  have "pp_orbit r = {UNIV}"
    using invariant r by (simp add: pp_invariant_orbit_singleton)
  then have "pp_orbit r \<subseteq> {UNIV}" by simp
  moreover have "{UNIV :: pp_sem_prop} \<noteq> UNIV"
    by (rule pp_sem_prop_not_singleton)
  ultimately show "\<not> pp_root_unary_recombination {UNIV} r"
    by (simp add: pp_root_unary_recombination_iff)
next
  assume r: "r = {}"
  have "pp_orbit r = {{}}"
    using invariant r by (simp add: pp_invariant_orbit_singleton)
  then have "pp_orbit r \<subseteq> {{}}" by simp
  moreover have "{{} :: pp_sem_prop} \<noteq> UNIV"
    by (rule pp_sem_prop_not_singleton)
  ultimately show "\<not> pp_root_unary_recombination {{}} r"
    by (simp add: pp_root_unary_recombination_iff)
qed

corollary pp_seed_must_be_contingent:
  assumes "pp_root_unary_recombination (pp_orbit r) r"
  shows "\<not> pp_invariant_proposition r"
  using assms pp_invariant_seed_fails_recombination by blast

corollary pp_seed_not_extreme:
  assumes "pp_root_unary_recombination (pp_orbit r) r"
  shows "r \<noteq> {} \<and> r \<noteq> UNIV"
  using assms pp_seed_must_be_contingent
  by (auto simp: pp_invariant_proposition_iff_extreme)

subsection \<open>Consequence for the uniformity question\<close>

text \<open>
  Every closed term of the seed-free language denotes, at type \<open>Prop\<close>, an invariant
  proposition, because it has no free parameter for the action to move.  Combining that
  with \<open>pp_invariant_proposition_iff_extreme\<close>, the seed-free term model has only
  \<open>{}\<close> and \<open>UNIV\<close> at type \<open>Prop\<close>, and by the theorem above neither can serve as the
  fundamental proposition.  So the domains cannot be frozen by choosing the seed from
  inside them.

  The statement below records the operative half of that argument in checked form: any
  seed lying in a set of invariant propositions fails Recombination.  The other half,
  that closed seed-free terms denote invariant propositions, is the object-language
  term induction and is not formalized here.
\<close>

theorem pp_no_seed_inside_an_invariant_domain:
  assumes domain_invariant:
      "\<And>P. P \<in> D \<Longrightarrow> pp_invariant_proposition P"
    and seed: "r \<in> D"
  shows "\<not> pp_root_unary_recombination (pp_orbit r) r"
  using domain_invariant[OF seed]
  by (rule pp_invariant_seed_fails_recombination)

end
