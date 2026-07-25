theory Bacon_PP_Parity
  imports Bacon_PP_Generic_Witness
begin

section \<open>Invariant-value fibres and a parity family\<close>

text \<open>
  The semantic decomposition below is deliberately independent of any
  definability claim.  Its hypotheses make explicit two conditions that are
  essential: the family is equivariant, and the candidate stock contains only
  invariant operators.
\<close>

definition pp_equivariant_family ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_equivariant_family Y \<longleftrightarrow>
    (\<forall>i b. pp_view i (Y b) = Y (pp_view i b))"

definition pp_operator_equal ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_operator_equal A B =
    {i. pp_view i A = pp_view i B}"

definition pp_orbit_constant ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_orbit_constant Y X =
    {b. \<forall>j. Y (pp_view j b) = X}"

lemma pp_operator_equal_UNIV_iff:
  "pp_operator_equal A B = UNIV \<longleftrightarrow>
    (\<forall>i. pp_view i A = pp_view i B)"
  by (auto simp: pp_operator_equal_def)

theorem pp_orbit_constant_root_box_equal:
  assumes Y_equivariant: "pp_equivariant_family Y"
    and X_invariant: "pp_invariant_proposition X"
  shows "b \<in> pp_orbit_constant Y X \<longleftrightarrow>
    pp_root_true
      (pp_sem_box (pp_operator_equal (Y b) X))"
proof -
  have Y_action:
    "pp_view i (Y b) = Y (pp_view i b)" for i b
    using Y_equivariant
    unfolding pp_equivariant_family_def by blast
  have X_action:
    "pp_view i X = X" for i
    using X_invariant
    unfolding pp_invariant_proposition_def by blast
  have "pp_root_true
      (pp_sem_box (pp_operator_equal (Y b) X)) \<longleftrightarrow>
      pp_operator_equal (Y b) X = UNIV"
    by (simp add: pp_root_true_def pp_sem_box_def)
  also have "... \<longleftrightarrow>
      (\<forall>i. pp_view i (Y b) = pp_view i X)"
    by (rule pp_operator_equal_UNIV_iff)
  also have "... \<longleftrightarrow>
      (\<forall>i. Y (pp_view i b) = X)"
    using Y_action X_action by simp
  also have "... \<longleftrightarrow> b \<in> pp_orbit_constant Y X"
    by (simp add: pp_orbit_constant_def)
  finally show ?thesis
    by blast
qed

theorem pp_invariant_stock_membership_union:
  assumes Y_equivariant: "pp_equivariant_family Y"
    and stock_invariant:
      "\<And>X. X \<in> Stock \<Longrightarrow> pp_invariant_proposition X"
  shows "{b. Y b \<in> Stock} =
    (\<Union>X \<in> Stock. pp_orbit_constant Y X)"
proof
  show "{b. Y b \<in> Stock} \<subseteq>
      (\<Union>X \<in> Stock. pp_orbit_constant Y X)"
  proof
    fix b
    assume b_mem: "b \<in> {b. Y b \<in> Stock}"
    then have Yb_mem: "Y b \<in> Stock"
      by simp
    have Yb_invariant: "pp_invariant_proposition (Y b)"
      using Yb_mem by (rule stock_invariant)
    have action: "Y (pp_view j b) = Y b" for j
    proof -
      have "pp_view j (Y b) = Y (pp_view j b)"
        using Y_equivariant
        unfolding pp_equivariant_family_def by blast
      moreover have "pp_view j (Y b) = Y b"
        using Yb_invariant
        unfolding pp_invariant_proposition_def by blast
      ultimately show ?thesis
        by simp
    qed
    have "b \<in> pp_orbit_constant Y (Y b)"
      using action by (simp add: pp_orbit_constant_def)
    with Yb_mem show
      "b \<in> (\<Union>X \<in> Stock. pp_orbit_constant Y X)"
      by blast
  qed
next
  show "(\<Union>X \<in> Stock. pp_orbit_constant Y X) \<subseteq>
      {b. Y b \<in> Stock}"
  proof
    fix b
    assume "b \<in> (\<Union>X \<in> Stock. pp_orbit_constant Y X)"
    then obtain X where
      X_mem: "X \<in> Stock"
      and constant_view: "b \<in> pp_orbit_constant Y X"
      by blast
    have all_views:
      "\<forall>j. Y (pp_view j b) = X"
      using constant_view
      by (simp add: pp_orbit_constant_def)
    have "Y b = X"
      using all_views[rule_format, of "[]"] by simp
    with X_mem show "b \<in> {b. Y b \<in> Stock}"
      by simp
  qed
qed

lemma pp_orbit_constant_disjoint:
  assumes "X \<noteq> X'"
  shows "pp_orbit_constant Y X \<inter>
    pp_orbit_constant Y X' = {}"
proof -
  have "\<not> (b \<in> pp_orbit_constant Y X \<and>
      b \<in> pp_orbit_constant Y X')" for b
  proof
    assume both:
      "b \<in> pp_orbit_constant Y X \<and>
       b \<in> pp_orbit_constant Y X'"
    then have "Y b = X" and "Y b = X'"
      unfolding pp_orbit_constant_def
      by (auto dest!: spec[where x = "[]"])
    then show False
      using assms by simp
  qed
  then show ?thesis
    by blast
qed

subsection \<open>The parity regression certificate\<close>

definition pp_parity :: "nat set \<Rightarrow> pp_sem_prop" where
  "pp_parity E =
    {w. even (length (filter (\<lambda>k. k \<in> E) w))}"

lemma pp_parity_view:
  "pp_view i (pp_parity E) =
    (if even (length (filter (\<lambda>k. k \<in> E) i))
     then pp_parity E
     else - pp_parity E)"
  by (auto simp: pp_view_def pp_parity_def even_add)

theorem pp_parity_orbit_two:
  "pp_orbit (pp_parity E) \<subseteq>
    {pp_parity E, - pp_parity E}"
  by (auto simp: pp_orbit_def pp_parity_view)

theorem pp_parity_inj:
  "inj pp_parity"
proof (rule injI)
  fix E F
  assume equality: "pp_parity E = pp_parity F"
  show "E = F"
  proof (rule set_eqI)
    fix k
    have "([k] \<in> pp_parity E) = ([k] \<in> pp_parity F)"
      using equality by simp
    then show "k \<in> E \<longleftrightarrow> k \<in> F"
      by (simp add: pp_parity_def split: if_splits)
  qed
qed

corollary pp_parity_family_has_two_point_orbits:
  "\<exists>f :: nat set \<Rightarrow> pp_sem_prop.
    inj f \<and> (\<forall>E. pp_orbit (f E) \<subseteq> {f E, - f E})"
  using pp_parity_inj pp_parity_orbit_two
  by (intro exI[of _ pp_parity]) simp

text \<open>
  Thus there are as many propositions with at most two views as there are
  subsets of the natural numbers.  In particular, invariance of a value cannot
  by itself entail Pure-free definability.  Any remaining closure argument must
  use a separate fact about which invariant values belong to the proposed
  countable pure stock.
\<close>

end
