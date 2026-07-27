theory Bacon_PP_Goodman_M6
  imports Bacon_PP_Goodman_M5
begin

section \<open>Goodman M6: supervenience without independence\<close>

text \<open>
  The first construction separates any two worlds by a fun-prime proposition.
  A fresh one-letter branch carries a copy of the necessitated-QSS witness,
  while one of the two worlds is added as a marker.  Freshness ensures that
  the marker does not alter the copied view and that the other world remains
  outside the proposition.
\<close>

lemma pp_M6_fresh_letter:
  obtains n :: nat where "n \<notin> set i \<union> set j"
proof -
  let ?n = "Suc (Max (insert 0 (set i \<union> set j)))"
  have fresh: "?n \<notin> set i \<union> set j"
  proof
    assume member: "?n \<in> set i \<union> set j"
    have "?n \<le> Max (insert 0 (set i \<union> set j))"
      by (rule Max_ge) (use member in auto)
    then show False by simp
  qed
  show thesis
    using fresh by (rule that)
qed

lemma pp_M6_fresh_branch_view:
  assumes fresh: "n \<notin> set i"
  shows
    "pp_view [n] (pp_lift [n] r \<union> {i}) = r"
proof -
  have singleton_empty: "pp_view [n] {i} = {}"
  proof (rule set_eqI)
    fix w
    show "w \<in> pp_view [n] {i} \<longleftrightarrow> w \<in> {}"
      using fresh
      by (auto simp: pp_view_def)
  qed
  have
      "pp_view [n] (pp_lift [n] r \<union> {i}) =
       pp_view [n] (pp_lift [n] r) \<union> pp_view [n] {i}"
    by (auto simp: pp_view_def)
  also have "... = r"
    using singleton_empty by simp
  finally show ?thesis .
qed

lemma pp_M6_fresh_branch_membership:
  assumes fresh: "n \<notin> set j"
    and distinct: "i \<noteq> j"
  shows
    "i \<in> pp_lift [n] r \<union> {i}"
    "j \<notin> pp_lift [n] r \<union> {i}"
  using assms
  by (auto simp: pp_lift_def)

theorem pp_M6_fun_prime_separates_distinct_substitutions:
  assumes qss:
      "pp_stock_necessitated_QSS Stock r"
    and pure_member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and pure_invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
    and distinct: "i \<noteq> j"
  shows
    "\<exists>p.
      pp_stock_fun_prime Stock p \<and>
      pp_view i p \<noteq> pp_view j p"
proof -
  obtain n :: nat where fresh:
      "n \<notin> set i \<union> set j"
    using pp_M6_fresh_letter[of i j] .
  have fresh_i: "n \<notin> set i"
    and fresh_j: "n \<notin> set j"
    using fresh by auto
  let ?p = "pp_lift [n] r \<union> {i}"
  have view: "pp_view [n] ?p = r"
    by (rule pp_M6_fresh_branch_view[OF fresh_i])
  have r_free: "pp_stock_fun_prime Stock r"
  proof -
    have "pp_stock_fun_prime Stock (pp_view [] r)"
      using qss
      unfolding pp_stock_necessitated_QSS_def by blast
    then show ?thesis by simp
  qed
  have p_free: "pp_stock_fun_prime Stock ?p"
  proof (rule pp_M4_fun_prime_preimage[
      OF _ pure_member pure_invariant])
    show "pp_stock_fun_prime Stock (pp_view [n] ?p)"
      using r_free view by simp
  qed
  have i_in: "i \<in> ?p"
    by simp
  have j_out: "j \<notin> ?p"
    by (rule pp_M6_fresh_branch_membership(2)[
          OF fresh_j distinct])
  have views_distinct:
      "pp_view i ?p \<noteq> pp_view j ?p"
  proof
    assume equality: "pp_view i ?p = pp_view j ?p"
    have "[] \<in> pp_view i ?p"
      using i_in by (simp add: pp_view_membership_at_root)
    then have "[] \<in> pp_view j ?p"
      using equality by simp
    then show False
      using j_out by (simp add: pp_view_membership_at_root)
  qed
  show ?thesis
    using p_free views_distinct by blast
qed

text \<open>
  The first independence failure is already witnessed by the orbit diagonal:
  no fixed proposition can be sent to every proposition, even before several
  simultaneous assignments are considered.
\<close>

corollary pp_M6_single_proposition_independence_fails:
  "\<exists>q. \<forall>i. pp_view i p \<noteq> q"
proof (rule exI[of _ "pp_M2_orbit_diagonal p"], intro allI)
  fix i
  show "pp_view i p \<noteq> pp_M2_orbit_diagonal p"
    using pp_M2_orbit_diagonal_differs[of p i]
    by (simp add: neq_commute)
qed

subsection \<open>A substitution-preserved strict relation\<close>

lemma pp_M6_two_branch_views:
  "pp_view [0] (pp_lift [0] r \<union> pp_lift [1] r) = r"
  "pp_view [1] (pp_lift [0] r \<union> pp_lift [1] r) = r"
  by (auto simp: pp_view_def pp_lift_def append_singleton_eq_iff)

lemma pp_M6_view_mono:
  assumes "p \<subseteq> q"
  shows "pp_view i p \<subseteq> pp_view i q"
  using assms by (auto simp: pp_view_def)

theorem pp_M6_fun_prime_strict_pair:
  assumes qss:
      "pp_stock_necessitated_QSS Stock r"
    and pure_member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and pure_invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
    and identity: "(\<lambda>P :: pp_sem_prop. P) \<in> Stock"
    and zero: "(\<lambda>P :: pp_sem_prop. {}) \<in> Stock"
    and one: "(\<lambda>P :: pp_sem_prop. UNIV) \<in> Stock"
  defines "p \<equiv> pp_lift [0] r"
    and "q \<equiv> pp_lift [0] r \<union> pp_lift [1] r"
  shows
    "pp_stock_fun_prime Stock p
      \<and> pp_stock_fun_prime Stock q
      \<and> p \<subset> q
      \<and> q \<notin> pp_M4_pure_orbit Stock p
      \<and> (\<forall>i. pp_view i p \<subseteq> pp_view i q)"
proof -
  have r_free: "pp_stock_fun_prime Stock r"
  proof -
    have "pp_stock_fun_prime Stock (pp_view [] r)"
      using qss
      unfolding pp_stock_necessitated_QSS_def by blast
    then show ?thesis by simp
  qed
  have r_nonempty: "r \<noteq> {}"
    using r_free identity zero
    by (rule pp_M4_fun_prime_not_empty)
  have r_nonuniversal: "r \<noteq> UNIV"
    using r_free identity one
    by (rule pp_M4_fun_prime_not_UNIV)
  have view_p0: "pp_view [0] p = r"
    unfolding p_def by simp
  have view_p1: "pp_view [1] p = {}"
    unfolding p_def
    using pp_M4_view_lift_other_branch[of 0 r] by simp
  have view_q0: "pp_view [0] q = r"
    and view_q1: "pp_view [1] q = r"
    unfolding q_def
    using pp_M6_two_branch_views[of r] by blast+
  have p_free: "pp_stock_fun_prime Stock p"
    using r_free view_p0 pure_member pure_invariant
    by (metis pp_M4_fun_prime_preimage)
  have q_free: "pp_stock_fun_prime Stock q"
    using r_free view_q0 pure_member pure_invariant
    by (metis pp_M4_fun_prime_preimage)
  have p_subset: "p \<subseteq> q"
    unfolding p_def q_def by blast
  have proper: "p \<subset> q"
  proof -
    obtain w where w_r: "w \<in> r"
      using r_nonempty by blast
    have "w @ [1] \<in> q"
      unfolding q_def pp_lift_def using w_r by blast
    moreover have "w @ [1] \<notin> p"
      unfolding p_def pp_lift_def
      by (auto simp: append_singleton_eq_iff)
    ultimately show ?thesis
      using p_subset by blast
  qed
  have not_orbit: "q \<notin> pp_M4_pure_orbit Stock p"
  proof
    assume orbit: "q \<in> pp_M4_pure_orbit Stock p"
    then obtain Z where
        Z_stock: "Z \<in> Stock"
      and qZ: "q = Z p"
      unfolding pp_M4_pure_orbit_def
        pp_M4_reversible_in_stock_def
      by blast
    have Z_equivariant: "pp_equivariant_operator Z"
      using pure_member[OF Z_stock] pure_invariant[OF Z_stock]
      by (simp add: pp_fun_invariant_iff_equivariant)
    have "r = Z {}"
    proof -
      have "r = pp_view [1] q"
        using view_q1 by simp
      also have "... = pp_view [1] (Z p)"
        using qZ by simp
      also have "... = Z (pp_view [1] p)"
        using Z_equivariant
        unfolding pp_equivariant_operator_def by blast
      also have "... = Z {}"
        using view_p1 by simp
      finally show ?thesis .
    qed
    moreover have "Z {} = {} \<or> Z {} = UNIV"
      using pure_member[OF Z_stock] pure_invariant[OF Z_stock]
      by (rule pp_M4_invariant_maps_extreme_to_extreme) simp
    ultimately show False
      using r_nonempty r_nonuniversal by blast
  qed
  have preserved:
      "\<forall>i. pp_view i p \<subseteq> pp_view i q"
    using p_subset pp_M6_view_mono by blast
  show ?thesis
    using p_free q_free proper not_orbit preserved by blast
qed

corollary pp_M6_joint_assignment_blocked_by_inclusion:
  assumes relation: "\<forall>i. pp_view i p \<subseteq> pp_view i q"
    and target_breaks: "\<not> A \<subseteq> B"
  shows "\<not> (\<exists>i. pp_view i p = A \<and> pp_view i q = B)"
  using relation target_breaks by blast

text \<open>
  Thus the two halves of M6 coexist exactly as Goodman claims.  Fun-prime
  propositions separate worlds, so their complete role-profile determines a
  world.  They are not freely recombinable: a one-coordinate target can miss
  an orbit, and even two fun-prime propositions from different pure-invertible
  classes can stand in a strict inclusion relation preserved by every
  substitution.
\<close>

end
