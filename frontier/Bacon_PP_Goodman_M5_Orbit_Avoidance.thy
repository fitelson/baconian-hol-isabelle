theory Bacon_PP_Goodman_M5_Orbit_Avoidance
  imports Bacon_PP_Goodman_M5
begin

section \<open>Repairing Goodman's M5 orbit-avoidance argument\<close>

text \<open>
  The singleton pairs indexed by worlds in Goodman's prose form only a
  countable family, so countability of the orbit does not by itself select an
  avoiding pair.  We instead diagonalize directly against every view of the
  proposed fundamental proposition.  Membership above a non-root word depends
  only on its final symbol; consequently every proper view is extreme, which
  gives the no-echo property needed by the transposition construction.
\<close>

definition pp_M5_diagonal_selector ::
    "pp_sem_prop \<Rightarrow> nat set" where
  "pp_M5_diagonal_selector R =
    insert 0 {n + 2 | n. [n + 2] \<notin> pp_view (from_nat n) R}"

definition pp_M5_diagonal_s ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M5_diagonal_s R =
    {w. w \<noteq> [] \<and> last w \<in> pp_M5_diagonal_selector R}"

definition pp_M5_diagonal_s' ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M5_diagonal_s' R = insert [] (pp_M5_diagonal_s R)"

definition pp_M5_diagonal_pair ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_M5_diagonal_pair R =
    {pp_M5_diagonal_s R, pp_M5_diagonal_s' R}"

lemma pp_M5_diagonal_selector_zero[simp]:
  "0 \<in> pp_M5_diagonal_selector R"
  by (simp add: pp_M5_diagonal_selector_def)

lemma pp_M5_diagonal_selector_one[simp]:
  "1 \<notin> pp_M5_diagonal_selector R"
  by (auto simp: pp_M5_diagonal_selector_def)

lemma pp_M5_diagonal_singleton:
  "[n + 2] \<in> pp_M5_diagonal_s R
    \<longleftrightarrow> [n + 2] \<notin> pp_view (from_nat n) R"
  by (auto simp: pp_M5_diagonal_s_def pp_M5_diagonal_selector_def)

lemma pp_M5_diagonal_s_false[simp]:
  "[] \<notin> pp_M5_diagonal_s R"
  by (simp add: pp_M5_diagonal_s_def)

lemma pp_M5_diagonal_s'_true[simp]:
  "[] \<in> pp_M5_diagonal_s' R"
  by (simp add: pp_M5_diagonal_s'_def)

lemma pp_M5_diagonal_s_distinct[simp]:
  "pp_M5_diagonal_s R \<noteq> pp_M5_diagonal_s' R"
  using pp_M5_diagonal_s_false[of R]
    pp_M5_diagonal_s'_true[of R] by blast

lemma pp_M5_diagonal_s'_distinct[simp]:
  "pp_M5_diagonal_s' R \<noteq> pp_M5_diagonal_s R"
  using pp_M5_diagonal_s_distinct[of R] by blast

lemma pp_M5_diagonal_s_nonempty:
  "pp_M5_diagonal_s R \<noteq> {}"
proof
  assume "pp_M5_diagonal_s R = {}"
  moreover have "[0] \<in> pp_M5_diagonal_s R"
    by (simp add: pp_M5_diagonal_s_def)
  ultimately show False by simp
qed

lemma pp_M5_diagonal_s_not_UNIV:
  "pp_M5_diagonal_s R \<noteq> UNIV"
  using pp_M5_diagonal_s_false[of R] by blast

lemma pp_M5_diagonal_s'_nonempty:
  "pp_M5_diagonal_s' R \<noteq> {}"
  using pp_M5_diagonal_s'_true[of R] by blast

lemma pp_M5_diagonal_s'_not_UNIV:
  "pp_M5_diagonal_s' R \<noteq> UNIV"
proof
  assume "pp_M5_diagonal_s' R = UNIV"
  moreover have "[1] \<notin> pp_M5_diagonal_s' R"
    using pp_M5_diagonal_selector_one[of R]
    by (simp add: pp_M5_diagonal_s'_def pp_M5_diagonal_s_def)
  ultimately show False by simp
qed

lemma pp_M5_diagonal_s_avoids_view:
  "pp_M5_diagonal_s R \<noteq> pp_view i R"
proof -
  let ?n = "to_nat i"
  have n: "(from_nat ?n :: pp_word) = i"
    by simp
  have
      "[?n + 2] \<in> pp_M5_diagonal_s R
        \<longleftrightarrow> [?n + 2] \<notin> pp_view i R"
    using pp_M5_diagonal_singleton[of ?n R] n by simp
  then show ?thesis by blast
qed

lemma pp_M5_diagonal_s'_avoids_view:
  "pp_M5_diagonal_s' R \<noteq> pp_view i R"
proof -
  let ?n = "to_nat i"
  have n: "(from_nat ?n :: pp_word) = i"
    by simp
  have
      "[?n + 2] \<in> pp_M5_diagonal_s' R
        \<longleftrightarrow> [?n + 2] \<notin> pp_view i R"
    using pp_M5_diagonal_singleton[of ?n R] n
    by (simp add: pp_M5_diagonal_s'_def)
  then show ?thesis by blast
qed

theorem pp_M5_diagonal_pair_avoids_orbit:
  "pp_M5_diagonal_pair R \<inter> pp_orbit R = {}"
  unfolding pp_M5_diagonal_pair_def pp_orbit_def
  using pp_M5_diagonal_s_avoids_view[of R]
    pp_M5_diagonal_s'_avoids_view[of R]
  by blast

lemma pp_M5_diagonal_s_view:
  assumes "i \<noteq> []"
  shows "pp_view i (pp_M5_diagonal_s R) =
    (if last i \<in> pp_M5_diagonal_selector R then UNIV else {})"
proof (rule set_eqI)
  fix j
  have nonempty: "j @ i \<noteq> []"
    using assms by auto
  have last_eq: "last (j @ i) = last i"
    using assms by (simp add: last_append)
  show
    "j \<in> pp_view i (pp_M5_diagonal_s R)
      \<longleftrightarrow>
     j \<in> (if last i \<in> pp_M5_diagonal_selector R then UNIV else {})"
    using nonempty last_eq
    by (simp add: pp_view_def pp_M5_diagonal_s_def)
qed

lemma pp_M5_diagonal_s'_view:
  assumes "i \<noteq> []"
  shows "pp_view i (pp_M5_diagonal_s' R) =
    pp_view i (pp_M5_diagonal_s R)"
proof (rule set_eqI)
  fix j
  have nonempty: "j @ i \<noteq> []"
    using assms by auto
  show
    "j \<in> pp_view i (pp_M5_diagonal_s' R)
      \<longleftrightarrow> j \<in> pp_view i (pp_M5_diagonal_s R)"
    using assms
    by (auto simp: pp_view_def pp_M5_diagonal_s'_def)
qed

lemma pp_M5_diagonal_no_echo:
  assumes "Q \<in> pp_M5_diagonal_pair R"
    and "i \<noteq> []"
  shows "pp_view i Q \<notin> pp_M5_diagonal_pair R"
proof -
  have s_view:
      "pp_view i (pp_M5_diagonal_s R) =
        (if last i \<in> pp_M5_diagonal_selector R then UNIV else {})"
    using assms(2) by (rule pp_M5_diagonal_s_view)
  have s'_view:
      "pp_view i (pp_M5_diagonal_s' R) =
        (if last i \<in> pp_M5_diagonal_selector R then UNIV else {})"
    using assms(2) s_view pp_M5_diagonal_s'_view by metis
  have pair_cases:
      "Q = pp_M5_diagonal_s R \<or> Q = pp_M5_diagonal_s' R"
    using assms(1)
    unfolding pp_M5_diagonal_pair_def by auto
  have extreme:
      "pp_view i Q = {} \<or> pp_view i Q = UNIV"
    using pair_cases s_view s'_view
    by (cases "last i \<in> pp_M5_diagonal_selector R"; auto)
  show ?thesis
    using extreme
      pp_M5_diagonal_s_nonempty[of R]
      pp_M5_diagonal_s_not_UNIV[of R]
      pp_M5_diagonal_s'_nonempty[of R]
      pp_M5_diagonal_s'_not_UNIV[of R]
    unfolding pp_M5_diagonal_pair_def by blast
qed

definition pp_M5_diagonal_swapped_index ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_M5_diagonal_swapped_index R =
    (pp_M5_true_index - {pp_M5_diagonal_s' R})
      \<union> {pp_M5_diagonal_s R}"

definition pp_M5_diagonal_exotic ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M5_diagonal_exotic R =
    pp_classifier (pp_M5_diagonal_swapped_index R)"

lemma pp_M5_diagonal_flip_rule:
  "i \<in> pp_M5_diagonal_exotic R P
    \<longleftrightarrow>
    (if pp_view i P = pp_M5_diagonal_s R then True
     else if pp_view i P = pp_M5_diagonal_s' R then False
     else i \<in> P)"
proof -
  have root:
      "[] \<in> pp_view i P \<longleftrightarrow> i \<in> P"
    by (rule pp_view_membership_at_root)
  show ?thesis
    unfolding pp_M5_diagonal_exotic_def pp_classifier_def
      pp_M5_diagonal_swapped_index_def pp_M5_true_index_def
    using root by auto
qed

lemma pp_M5_diagonal_exotic_s:
  "pp_M5_diagonal_exotic R (pp_M5_diagonal_s R) =
    pp_M5_diagonal_s' R"
proof (rule set_eqI)
  fix i
  show
    "i \<in> pp_M5_diagonal_exotic R (pp_M5_diagonal_s R)
      \<longleftrightarrow> i \<in> pp_M5_diagonal_s' R"
  proof (cases "i = []")
    case True
    then show ?thesis
      by (simp add: pp_M5_diagonal_flip_rule)
  next
    case False
    have no_echo:
        "pp_view i (pp_M5_diagonal_s R)
          \<notin> pp_M5_diagonal_pair R"
    proof (rule pp_M5_diagonal_no_echo)
      show "pp_M5_diagonal_s R \<in> pp_M5_diagonal_pair R"
        by (simp add: pp_M5_diagonal_pair_def)
      show "i \<noteq> []"
        by (rule False)
    qed
    then show ?thesis
      using False
      by (auto simp: pp_M5_diagonal_flip_rule
          pp_M5_diagonal_pair_def pp_M5_diagonal_s'_def)
  qed
qed

lemma pp_M5_diagonal_exotic_s':
  "pp_M5_diagonal_exotic R (pp_M5_diagonal_s' R) =
    pp_M5_diagonal_s R"
proof (rule set_eqI)
  fix i
  show
    "i \<in> pp_M5_diagonal_exotic R (pp_M5_diagonal_s' R)
      \<longleftrightarrow> i \<in> pp_M5_diagonal_s R"
  proof (cases "i = []")
    case True
    then show ?thesis
      by (simp add: pp_M5_diagonal_flip_rule)
  next
    case False
    have no_echo:
        "pp_view i (pp_M5_diagonal_s' R)
          \<notin> pp_M5_diagonal_pair R"
    proof (rule pp_M5_diagonal_no_echo)
      show "pp_M5_diagonal_s' R \<in> pp_M5_diagonal_pair R"
        by (simp add: pp_M5_diagonal_pair_def)
      show "i \<noteq> []"
        by (rule False)
    qed
    then show ?thesis
      using False
      by (auto simp: pp_M5_diagonal_flip_rule
          pp_M5_diagonal_pair_def pp_M5_diagonal_s'_def)
  qed
qed

lemma pp_M5_diagonal_exotic_fixes_R:
  "pp_M5_diagonal_exotic R R = R"
proof (rule set_eqI)
  fix i
  have not_s:
      "pp_view i R \<noteq> pp_M5_diagonal_s R"
    using pp_M5_diagonal_s_avoids_view[of R i] by blast
  have not_s':
      "pp_view i R \<noteq> pp_M5_diagonal_s' R"
    using pp_M5_diagonal_s'_avoids_view[of R i] by blast
  show "i \<in> pp_M5_diagonal_exotic R R \<longleftrightarrow> i \<in> R"
    using not_s not_s' by (simp add: pp_M5_diagonal_flip_rule)
qed

lemma pp_M5_diagonal_exotic_not_identity:
  "pp_M5_diagonal_exotic R \<noteq> (\<lambda>P. P)"
proof
  assume equality: "pp_M5_diagonal_exotic R = (\<lambda>P. P)"
  have
      "pp_M5_diagonal_exotic R (pp_M5_diagonal_s R) =
        pp_M5_diagonal_s R"
    using equality by simp
  then show False
    using pp_M5_diagonal_exotic_s[of R]
      pp_M5_diagonal_s_distinct[of R] by simp
qed

lemma pp_M5_diagonal_exotic_is_function_space_invariant:
  "pp_function_space_member (pp_M5_diagonal_exotic R)
    \<and> pp_fun_invariant (pp_M5_diagonal_exotic R)"
  unfolding pp_M5_diagonal_exotic_def
  by (rule pp_classifier_is_function_space_invariant)

theorem pp_M5_pre_rebuild_QSS_obstruction:
  assumes exotic_pure: "pp_M5_diagonal_exotic R \<in> Stock"
    and identity_pure: "(\<lambda>P. P) \<in> Stock"
  shows "\<not> pp_stock_fun_prime Stock R"
proof
  assume free: "pp_stock_fun_prime Stock R"
  have equality:
      "pp_M5_diagonal_exotic R = (\<lambda>P. P)"
    using free exotic_pure identity_pure
      pp_M5_diagonal_exotic_fixes_R[of R]
    by (rule pp_stock_fun_primeD)
  show False
    using equality pp_M5_diagonal_exotic_not_identity[of R]
    by contradiction
qed

text \<open>
  This repairs the pre-rebuild portion of M5.  The original fixed pair
  \<open>{[5]}\<close>, \<open>{[],[5]}\<close> remains a correct certificate of an exotic
  involution.  The new pair depends on \<open>R\<close> and is the one that must be used
  for the QSS obstruction: it is constructively disjoint from every view of
  \<open>R\<close>, and its associated invariant classifier fixes \<open>R\<close> while differing
  from identity.
\<close>

end
