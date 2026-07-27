theory Bacon_PP_Goodman_M5
  imports Bacon_PP_Goodman_M4
begin

section \<open>Goodman M5: the exotic invariant involution\<close>

subsection \<open>The swapped truth index\<close>

definition pp_M5_s :: pp_sem_prop where
  "pp_M5_s = {[5]}"

definition pp_M5_s' :: pp_sem_prop where
  "pp_M5_s' = {[], [5]}"

definition pp_M5_pair :: "pp_sem_prop set" where
  "pp_M5_pair = {pp_M5_s, pp_M5_s'}"

definition pp_M5_true_index :: "pp_sem_prop set" where
  "pp_M5_true_index = {P. [] \<in> P}"

definition pp_M5_swapped_index :: "pp_sem_prop set" where
  "pp_M5_swapped_index =
    (pp_M5_true_index - {pp_M5_s'}) \<union> {pp_M5_s}"

definition pp_M5_exotic ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M5_exotic = pp_classifier pp_M5_swapped_index"

lemma pp_M5_s_false[simp]: "[] \<notin> pp_M5_s"
  by (simp add: pp_M5_s_def)

lemma pp_M5_s'_true[simp]: "[] \<in> pp_M5_s'"
  by (simp add: pp_M5_s'_def)

lemma pp_M5_s_distinct[simp]: "pp_M5_s \<noteq> pp_M5_s'"
  by (auto simp: pp_M5_s_def pp_M5_s'_def)

lemma pp_M5_s'_distinct[simp]: "pp_M5_s' \<noteq> pp_M5_s"
  using pp_M5_s_distinct by blast

lemma pp_M5_true_classifier:
  "pp_classifier pp_M5_true_index = (\<lambda>P. P)"
proof (rule ext, rule set_eqI)
  fix P i
  show "i \<in> pp_classifier pp_M5_true_index P
      \<longleftrightarrow> i \<in> (\<lambda>P. P) P"
    by (simp add: pp_classifier_def pp_M5_true_index_def
        pp_view_membership_at_root)
qed

lemma pp_M5_no_echo_s:
  assumes "i \<noteq> []"
  shows "pp_view i pp_M5_s \<notin> pp_M5_pair"
  using assms
  by (auto simp: pp_view_def pp_M5_s_def pp_M5_s'_def
      pp_M5_pair_def)

lemma pp_M5_no_echo_s':
  assumes "i \<noteq> []"
  shows "pp_view i pp_M5_s' \<notin> pp_M5_pair"
  using assms
  by (auto simp: pp_view_def pp_M5_s_def pp_M5_s'_def
      pp_M5_pair_def)

lemma pp_M5_no_echo:
  assumes "Q \<in> pp_M5_pair"
    and "i \<noteq> []"
  shows "pp_view i Q \<notin> pp_M5_pair"
  using assms pp_M5_no_echo_s pp_M5_no_echo_s'
  unfolding pp_M5_pair_def by blast

lemma pp_M5_flip_rule:
  "i \<in> pp_M5_exotic P
    \<longleftrightarrow>
    (if pp_view i P = pp_M5_s then True
     else if pp_view i P = pp_M5_s' then False
     else i \<in> P)"
proof -
  have root:
      "[] \<in> pp_view i P \<longleftrightarrow> i \<in> P"
    by (rule pp_view_membership_at_root)
  show ?thesis
    unfolding pp_M5_exotic_def pp_classifier_def
      pp_M5_swapped_index_def pp_M5_true_index_def
    using root
    by auto
qed

subsection \<open>The transposed pair\<close>

lemma pp_M5_exotic_s:
  "pp_M5_exotic pp_M5_s = pp_M5_s'"
proof (rule set_eqI)
  fix i
  show "i \<in> pp_M5_exotic pp_M5_s
      \<longleftrightarrow> i \<in> pp_M5_s'"
  proof (cases "i = []")
    case True
    then show ?thesis
      by (simp add: pp_M5_flip_rule)
  next
    case False
    then have no_echo:
        "pp_view i pp_M5_s \<notin> pp_M5_pair"
      by (rule pp_M5_no_echo_s)
    then have neither:
        "pp_view i pp_M5_s \<noteq> pp_M5_s"
        "pp_view i pp_M5_s \<noteq> pp_M5_s'"
      unfolding pp_M5_pair_def by blast+
    show ?thesis
      using False neither
      by (simp add: pp_M5_flip_rule pp_M5_s_def pp_M5_s'_def)
  qed
qed

lemma pp_M5_exotic_s':
  "pp_M5_exotic pp_M5_s' = pp_M5_s"
proof (rule set_eqI)
  fix i
  show "i \<in> pp_M5_exotic pp_M5_s'
      \<longleftrightarrow> i \<in> pp_M5_s"
  proof (cases "i = []")
    case True
    then show ?thesis
      by (simp add: pp_M5_flip_rule)
  next
    case False
    then have no_echo:
        "pp_view i pp_M5_s' \<notin> pp_M5_pair"
      by (rule pp_M5_no_echo_s')
    then have neither:
        "pp_view i pp_M5_s' \<noteq> pp_M5_s"
        "pp_view i pp_M5_s' \<noteq> pp_M5_s'"
      unfolding pp_M5_pair_def by blast+
    show ?thesis
      using False neither
      by (simp add: pp_M5_flip_rule pp_M5_s_def pp_M5_s'_def)
  qed
qed

lemma pp_M5_exotic_preserves_pair:
  assumes "Q \<in> pp_M5_pair"
  shows "pp_M5_exotic Q \<in> pp_M5_pair"
  using assms pp_M5_exotic_s pp_M5_exotic_s'
  unfolding pp_M5_pair_def by blast

subsection \<open>No outsider enters the pair\<close>

lemma pp_M5_exotic_equivariant:
  "pp_equivariant_operator pp_M5_exotic"
  unfolding pp_M5_exotic_def
  by (rule pp_classifier_equivariant_operator)

lemma pp_M5_exotic_view:
  "pp_view i (pp_M5_exotic P) =
    pp_M5_exotic (pp_view i P)"
  using pp_M5_exotic_equivariant
  unfolding pp_equivariant_operator_def by blast

lemma pp_M5_preimage_pair_only_at_root:
  assumes image_pair: "pp_M5_exotic P \<in> pp_M5_pair"
    and view_pair: "pp_view i P \<in> pp_M5_pair"
  shows "i = []"
proof (rule ccontr)
  assume "i \<noteq> []"
  have image_view_pair:
      "pp_view i (pp_M5_exotic P) \<in> pp_M5_pair"
  proof -
    have "pp_M5_exotic (pp_view i P) \<in> pp_M5_pair"
      using view_pair by (rule pp_M5_exotic_preserves_pair)
    then show ?thesis
      by (simp add: pp_M5_exotic_view)
  qed
  have "pp_view i (pp_M5_exotic P) \<notin> pp_M5_pair"
    using image_pair \<open>i \<noteq> []\<close>
    by (rule pp_M5_no_echo)
  then show False
    using image_view_pair by contradiction
qed

lemma pp_M5_no_outsider_enters_pair:
  assumes image_pair: "pp_M5_exotic P \<in> pp_M5_pair"
  shows "P \<in> pp_M5_pair"
proof -
  have no_nonroot_pair:
      "\<And>i. i \<noteq> [] \<Longrightarrow> pp_view i P \<notin> pp_M5_pair"
    using image_pair pp_M5_preimage_pair_only_at_root by blast
  show ?thesis
  proof (cases "P \<in> pp_M5_pair")
    case True
    then show ?thesis .
  next
    case False
    have root_neither:
        "P \<noteq> pp_M5_s" "P \<noteq> pp_M5_s'"
      using False unfolding pp_M5_pair_def by blast+
    have unchanged: "pp_M5_exotic P = P"
    proof (rule set_eqI)
      fix i
      show "i \<in> pp_M5_exotic P \<longleftrightarrow> i \<in> P"
      proof (cases "i = []")
        case True
        then show ?thesis
          using root_neither by (simp add: pp_M5_flip_rule)
      next
        case False
        then have "pp_view i P \<notin> pp_M5_pair"
          by (rule no_nonroot_pair)
        then have
            "pp_view i P \<noteq> pp_M5_s"
            "pp_view i P \<noteq> pp_M5_s'"
          unfolding pp_M5_pair_def by blast+
        then show ?thesis
          by (simp add: pp_M5_flip_rule)
      qed
    qed
    show ?thesis
      using image_pair unchanged by simp
  qed
qed

lemma pp_M5_pair_iff_after_exotic:
  "pp_M5_exotic P \<in> pp_M5_pair
    \<longleftrightarrow> P \<in> pp_M5_pair"
  using pp_M5_no_outsider_enters_pair
    pp_M5_exotic_preserves_pair by blast

subsection \<open>Involution and failures of classification\<close>

theorem pp_M5_exotic_involution:
  "pp_M5_exotic (pp_M5_exotic P) = P"
proof (rule set_eqI)
  fix i
  have pair_stable:
      "pp_view i (pp_M5_exotic P) \<in> pp_M5_pair
        \<longleftrightarrow> pp_view i P \<in> pp_M5_pair"
  proof -
    have
        "pp_view i (pp_M5_exotic P) \<in> pp_M5_pair
          \<longleftrightarrow>
         pp_M5_exotic (pp_view i P) \<in> pp_M5_pair"
      by (simp add: pp_M5_exotic_view)
    also have "... \<longleftrightarrow>
        pp_view i P \<in> pp_M5_pair"
      by (rule pp_M5_pair_iff_after_exotic)
    finally show ?thesis .
  qed
  show "i \<in> pp_M5_exotic (pp_M5_exotic P)
      \<longleftrightarrow> i \<in> P"
  proof (cases "pp_view i P = pp_M5_s")
    case True
    then have viewed:
        "pp_view i (pp_M5_exotic P) = pp_M5_s'"
      by (simp add: pp_M5_exotic_view pp_M5_exotic_s)
    have not_root: "[] \<notin> pp_view i P"
      using True by simp
    have "i \<notin> P"
      using not_root
      by (simp add: pp_view_membership_at_root)
    then show ?thesis
      using viewed
      by (simp add: pp_M5_flip_rule)
  next
    case not_s: False
    show ?thesis
    proof (cases "pp_view i P = pp_M5_s'")
      case True
      then have viewed:
          "pp_view i (pp_M5_exotic P) = pp_M5_s"
        by (simp add: pp_M5_exotic_view pp_M5_exotic_s')
      have root_in: "[] \<in> pp_view i P"
        using True by simp
      have "i \<in> P"
        using root_in
        by (simp add: pp_view_membership_at_root)
      then show ?thesis
        using viewed
        by (simp add: pp_M5_flip_rule)
    next
      case not_s': False
      have original_not_pair:
          "pp_view i P \<notin> pp_M5_pair"
        using not_s not_s'
        unfolding pp_M5_pair_def by blast
      have image_not_pair:
          "pp_view i (pp_M5_exotic P) \<notin> pp_M5_pair"
        using pair_stable original_not_pair by blast
      then have image_neither:
          "pp_view i (pp_M5_exotic P) \<noteq> pp_M5_s"
          "pp_view i (pp_M5_exotic P) \<noteq> pp_M5_s'"
        unfolding pp_M5_pair_def by blast+
      have first_unchanged:
          "i \<in> pp_M5_exotic P \<longleftrightarrow> i \<in> P"
        using not_s not_s'
        by (simp add: pp_M5_flip_rule)
      show ?thesis
        using image_neither first_unchanged
        by (simp add: pp_M5_flip_rule)
    qed
  qed
qed

corollary pp_M5_exotic_bijective:
  "bij pp_M5_exotic"
  unfolding bij_def inj_def surj_def
  using pp_M5_exotic_involution
  by metis

corollary pp_M5_exotic_is_function_space_invariant:
  "pp_function_space_member pp_M5_exotic
    \<and> pp_fun_invariant pp_M5_exotic"
  unfolding pp_M5_exotic_def
  by (rule pp_classifier_is_function_space_invariant)

lemma pp_M5_exotic_fixes_top:
  "pp_M5_exotic UNIV = UNIV"
proof (rule set_eqI)
  fix i
  have view_top:
      "pp_view i UNIV = (UNIV :: pp_sem_prop)"
    by (rule set_eqI) (simp add: pp_view_def)
  have top_not_s:
      "(UNIV :: pp_sem_prop) \<noteq> pp_M5_s"
    using pp_M5_s_false by blast
  have top_not_s':
      "(UNIV :: pp_sem_prop) \<noteq> pp_M5_s'"
  proof
    assume equality:
        "(UNIV :: pp_sem_prop) = pp_M5_s'"
    have
        "([0] \<in> (UNIV :: pp_sem_prop)) =
         ([0] \<in> pp_M5_s')"
      using equality
      by (rule arg_cong[where f="\<lambda>X. [0] \<in> X"])
    then show False
      by (simp add: pp_M5_s'_def)
  qed
  have "pp_view i UNIV \<notin> pp_M5_pair"
    using view_top top_not_s top_not_s'
    unfolding pp_M5_pair_def by blast
  then show "i \<in> pp_M5_exotic UNIV \<longleftrightarrow> i \<in> UNIV"
    by (simp add: pp_M5_flip_rule pp_M5_pair_def)
qed

lemma pp_M5_exotic_fixes_bottom:
  "pp_M5_exotic {} = {}"
proof (rule set_eqI)
  fix i
  have view_bottom:
      "pp_view i {} = ({} :: pp_sem_prop)"
    by (rule set_eqI) (simp add: pp_view_def)
  have bottom_not_s:
      "({} :: pp_sem_prop) \<noteq> pp_M5_s"
    by (simp add: pp_M5_s_def)
  have bottom_not_s':
      "({} :: pp_sem_prop) \<noteq> pp_M5_s'"
    using pp_M5_s'_true by blast
  have "pp_view i {} \<notin> pp_M5_pair"
    using view_bottom bottom_not_s bottom_not_s'
    unfolding pp_M5_pair_def by blast
  then show "i \<in> pp_M5_exotic {} \<longleftrightarrow> i \<in> {}"
    by (simp add: pp_M5_flip_rule pp_M5_pair_def)
qed

definition pp_M5_truth_preserving ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_M5_truth_preserving F \<longleftrightarrow>
    (\<forall>P. ([] \<in> F P) = ([] \<in> P))"

definition pp_M5_truth_flipping ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_M5_truth_flipping F \<longleftrightarrow>
    (\<forall>P. ([] \<in> F P) = ([] \<notin> P))"

theorem pp_M5_exotic_not_truth_uniform:
  "\<not> pp_M5_truth_preserving pp_M5_exotic
    \<and> \<not> pp_M5_truth_flipping pp_M5_exotic"
proof
  show "\<not> pp_M5_truth_preserving pp_M5_exotic"
  proof
    assume preserving:
        "pp_M5_truth_preserving pp_M5_exotic"
    have
        "([] \<in> pp_M5_exotic pp_M5_s') =
         ([] \<in> pp_M5_s')"
      using preserving
      unfolding pp_M5_truth_preserving_def by blast
    then show False
      by (simp add: pp_M5_exotic_s')
  qed
next
  show "\<not> pp_M5_truth_flipping pp_M5_exotic"
  proof
    assume flipping:
        "pp_M5_truth_flipping pp_M5_exotic"
    have
        "([] \<in> pp_M5_exotic UNIV) =
         ([] \<notin> (UNIV :: pp_sem_prop))"
      using flipping
      unfolding pp_M5_truth_flipping_def by blast
    then show False
      by (simp add: pp_M5_exotic_fixes_top)
  qed
qed

definition pp_M5_biconditional_operator ::
    "pp_sem_prop \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop)" where
  "pp_M5_biconditional_operator A =
    (\<lambda>P. (P \<inter> A) \<union> (- P \<inter> - A))"

lemma pp_M5_biconditional_fixes_top_only_if_top:
  assumes "pp_M5_biconditional_operator A UNIV = UNIV"
  shows "A = UNIV"
  using assms
  by (simp add: pp_M5_biconditional_operator_def)

lemma pp_M5_biconditional_top_is_identity:
  "pp_M5_biconditional_operator UNIV = (\<lambda>P. P)"
  by (rule ext)
    (simp add: pp_M5_biconditional_operator_def)

theorem pp_M5_exotic_not_biconditional:
  "\<not> (\<exists>A. pp_M5_exotic =
    pp_M5_biconditional_operator A)"
proof
  assume "\<exists>A. pp_M5_exotic =
      pp_M5_biconditional_operator A"
  then obtain A where representation:
      "pp_M5_exotic = pp_M5_biconditional_operator A"
    by blast
  have fixes_top:
      "pp_M5_biconditional_operator A UNIV = UNIV"
    using representation pp_M5_exotic_fixes_top by simp
  have "A = UNIV"
    using fixes_top by (rule pp_M5_biconditional_fixes_top_only_if_top)
  then have identity:
      "pp_M5_biconditional_operator A = (\<lambda>P. P)"
    by (simp add: pp_M5_biconditional_top_is_identity)
  have exotic_identity:
      "pp_M5_exotic = (\<lambda>P. P)"
    using representation identity by simp
  have "pp_M5_exotic pp_M5_s' = pp_M5_s'"
    using fun_cong[OF exotic_identity, of pp_M5_s']
    by simp
  moreover have "pp_M5_exotic pp_M5_s' = pp_M5_s"
    by (rule pp_M5_exotic_s')
  ultimately show False
    using pp_M5_s'_distinct by blast
qed

text \<open>
  This verifies the unconditional construction in M5.  The classifier is an
  invariant element of Bacon's unary function domain, swaps \<open>s\<close> and
  \<open>s'\<close>, is its own inverse, fixes truth and falsity, but sends a true
  proposition to a false one.  It is therefore neither truth-preserving nor
  truth-flipping, and fixing truth prevents it from being a nonidentity
  biconditional operator.  The rebuilt-model step is discharged from the
  formal Theorem 10.1 interface in
  \<open>Bacon_PP_ZF_Goodman_M5_Rebuild\<close>.
\<close>

end
