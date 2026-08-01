theory Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model
  imports
    Bacon_PP_ZF_Goodman_M5_Rebuild
    Bacon_PP_ZF_Tree_Range_Term_Basis
begin

section \<open>Goodman M5: a rebuilt model containing an exotic operator\<close>

text \<open>
  This is a secondary Boolean-tree model.  It is useful for testing Goodman's
  rebuilding proposal, but no theorem in this file is evidence that Bacon's
  exact appendix construction has been enlarged in the same way.

  The preceding M5 theory proves Bacon's rebuilding theorem for an arbitrary
  fixed cone-natural unary operator.  Here we discharge those hypotheses
  inside the Boolean-prefix presentation of Bacon's model and rebuild the
  pure stock around the resulting operator.

  The two propositions below are the Boolean-tree counterparts of Goodman's
  displayed pair.  Their transposition is defined by the invariant classifier
  construction, rather than by a metalinguistic case distinction.  This is
  what makes the operator commute with every cone view.
\<close>

definition pp_t_M5_s :: pp_b_prop where
  "pp_t_M5_s = {[True]}"

definition pp_t_M5_s' :: pp_b_prop where
  "pp_t_M5_s' = {[], [True]}"

definition pp_t_M5_pair :: "pp_b_prop set" where
  "pp_t_M5_pair = {pp_t_M5_s, pp_t_M5_s'}"

definition pp_t_M5_true_index :: "pp_b_prop set" where
  "pp_t_M5_true_index = {P. [] \<in> P}"

definition pp_t_M5_swapped_index :: "pp_b_prop set" where
  "pp_t_M5_swapped_index =
    (pp_t_M5_true_index - {pp_t_M5_s'}) \<union> {pp_t_M5_s}"

definition pp_t_M5_classifier ::
    "pp_b_prop set \<Rightarrow> pp_b_operator"
where
  "pp_t_M5_classifier S P = {w. pp_b_view w P \<in> S}"

definition pp_t_M5_exotic :: pp_b_operator where
  "pp_t_M5_exotic = pp_t_M5_classifier pp_t_M5_swapped_index"

lemma pp_t_M5_s_false[simp]:
  "[] \<notin> pp_t_M5_s"
  by (simp add: pp_t_M5_s_def)

lemma pp_t_M5_s'_true[simp]:
  "[] \<in> pp_t_M5_s'"
  by (simp add: pp_t_M5_s'_def)

lemma pp_t_M5_s_distinct[simp]:
  "pp_t_M5_s \<noteq> pp_t_M5_s'"
  using pp_t_M5_s_false pp_t_M5_s'_true by blast

lemma pp_t_M5_s'_distinct[simp]:
  "pp_t_M5_s' \<noteq> pp_t_M5_s"
  using pp_t_M5_s_distinct by blast

lemma pp_t_M5_no_echo_s:
  assumes "w \<noteq> []"
  shows "pp_b_view w pp_t_M5_s \<notin> pp_t_M5_pair"
  using assms
  by (cases w)
    (auto simp: pp_b_view_def pp_t_M5_s_def pp_t_M5_s'_def
      pp_t_M5_pair_def)

lemma pp_t_M5_no_echo_s':
  assumes "w \<noteq> []"
  shows "pp_b_view w pp_t_M5_s' \<notin> pp_t_M5_pair"
  using assms
  by (cases w)
    (auto simp: pp_b_view_def pp_t_M5_s_def pp_t_M5_s'_def
      pp_t_M5_pair_def)

lemma pp_t_M5_no_echo:
  assumes "P \<in> pp_t_M5_pair"
    and "w \<noteq> []"
  shows "pp_b_view w P \<notin> pp_t_M5_pair"
  using assms pp_t_M5_no_echo_s pp_t_M5_no_echo_s'
  unfolding pp_t_M5_pair_def by blast

lemma pp_t_M5_classifier_equivariant:
  "pp_b_equivariant (pp_t_M5_classifier S)"
proof (unfold pp_b_equivariant_def, intro allI)
  fix s P
  show "pp_b_view s (pp_t_M5_classifier S P) =
      pp_t_M5_classifier S (pp_b_view s P)"
    by (rule set_eqI)
      (simp add: pp_b_view_def pp_t_M5_classifier_def append_assoc)
qed

theorem pp_t_M5_exotic_equivariant:
  "pp_b_equivariant pp_t_M5_exotic"
  unfolding pp_t_M5_exotic_def
  by (rule pp_t_M5_classifier_equivariant)

lemma pp_t_M5_flip_rule:
  "w \<in> pp_t_M5_exotic P
    \<longleftrightarrow>
    (if pp_b_view w P = pp_t_M5_s then True
     else if pp_b_view w P = pp_t_M5_s' then False
     else w \<in> P)"
proof -
  have root:
      "[] \<in> pp_b_view w P \<longleftrightarrow> w \<in> P"
    by (rule pp_b_view_membership_root)
  show ?thesis
    unfolding pp_t_M5_exotic_def pp_t_M5_classifier_def
      pp_t_M5_swapped_index_def pp_t_M5_true_index_def
    using root by auto
qed

lemma pp_t_M5_exotic_s:
  "pp_t_M5_exotic pp_t_M5_s = pp_t_M5_s'"
proof (rule set_eqI)
  fix w
  show "w \<in> pp_t_M5_exotic pp_t_M5_s
      \<longleftrightarrow> w \<in> pp_t_M5_s'"
  proof (cases "w = []")
    case True
    then show ?thesis
      by (simp add: pp_t_M5_flip_rule)
  next
    case False
    have no_echo:
        "pp_b_view w pp_t_M5_s \<notin> pp_t_M5_pair"
      using False by (rule pp_t_M5_no_echo_s)
    then show ?thesis
      using False
      by (auto simp: pp_t_M5_flip_rule pp_t_M5_pair_def
          pp_t_M5_s_def pp_t_M5_s'_def)
  qed
qed

lemma pp_t_M5_exotic_s':
  "pp_t_M5_exotic pp_t_M5_s' = pp_t_M5_s"
proof (rule set_eqI)
  fix w
  show "w \<in> pp_t_M5_exotic pp_t_M5_s'
      \<longleftrightarrow> w \<in> pp_t_M5_s"
  proof (cases "w = []")
    case True
    then show ?thesis
      by (simp add: pp_t_M5_flip_rule)
  next
    case False
    have no_echo:
        "pp_b_view w pp_t_M5_s' \<notin> pp_t_M5_pair"
      using False by (rule pp_t_M5_no_echo_s')
    then show ?thesis
      using False
      by (auto simp: pp_t_M5_flip_rule pp_t_M5_pair_def
          pp_t_M5_s_def pp_t_M5_s'_def)
  qed
qed

lemma pp_t_M5_exotic_not_identity:
  "pp_t_M5_exotic \<noteq> id"
proof
  assume "pp_t_M5_exotic = id"
  then have "pp_t_M5_exotic pp_t_M5_s = pp_t_M5_s"
    by simp
  then show False
    using pp_t_M5_exotic_s pp_t_M5_s_distinct by simp
qed

lemma pp_t_M5_exotic_fixes_top:
  "pp_t_M5_exotic UNIV = UNIV"
proof (rule set_eqI)
  fix w
  have view: "pp_b_view w UNIV = UNIV"
    by (auto simp: pp_b_view_def)
  have not_s: "(UNIV :: pp_b_prop) \<noteq> pp_t_M5_s"
    using pp_t_M5_s_false by blast
  have not_s': "(UNIV :: pp_b_prop) \<noteq> pp_t_M5_s'"
    by (auto simp: pp_t_M5_s'_def)
  show "w \<in> pp_t_M5_exotic UNIV \<longleftrightarrow> w \<in> UNIV"
    using view not_s not_s'
    by (simp add: pp_t_M5_flip_rule)
qed

lemma pp_t_M5_exotic_fixes_bottom:
  "pp_t_M5_exotic {} = {}"
proof (rule set_eqI)
  fix w
  have view: "pp_b_view w {} = {}"
    by (auto simp: pp_b_view_def)
  have not_s: "({} :: pp_b_prop) \<noteq> pp_t_M5_s"
    by (auto simp: pp_t_M5_s_def)
  have not_s': "({} :: pp_b_prop) \<noteq> pp_t_M5_s'"
    using pp_t_M5_s'_true by blast
  show "w \<in> pp_t_M5_exotic {} \<longleftrightarrow> w \<in> {}"
    using view not_s not_s'
      by (simp add: pp_t_M5_flip_rule)
qed

lemma pp_t_M5_exotic_preserves_pair:
  assumes "P \<in> pp_t_M5_pair"
  shows "pp_t_M5_exotic P \<in> pp_t_M5_pair"
  using assms pp_t_M5_exotic_s pp_t_M5_exotic_s'
  unfolding pp_t_M5_pair_def by blast

lemma pp_t_M5_exotic_view:
  "pp_b_view w (pp_t_M5_exotic P) =
    pp_t_M5_exotic (pp_b_view w P)"
  using pp_t_M5_exotic_equivariant
  unfolding pp_b_equivariant_def by blast

lemma pp_t_M5_preimage_pair_only_at_root:
  assumes image_pair: "pp_t_M5_exotic P \<in> pp_t_M5_pair"
    and view_pair: "pp_b_view w P \<in> pp_t_M5_pair"
  shows "w = []"
proof (rule ccontr)
  assume "w \<noteq> []"
  have image_view_pair:
      "pp_b_view w (pp_t_M5_exotic P) \<in> pp_t_M5_pair"
  proof -
    have "pp_t_M5_exotic (pp_b_view w P) \<in> pp_t_M5_pair"
      using view_pair by (rule pp_t_M5_exotic_preserves_pair)
    then show ?thesis
      by (simp add: pp_t_M5_exotic_view)
  qed
  have "pp_b_view w (pp_t_M5_exotic P) \<notin> pp_t_M5_pair"
    using image_pair \<open>w \<noteq> []\<close>
    by (rule pp_t_M5_no_echo)
  then show False
    using image_view_pair by contradiction
qed

lemma pp_t_M5_no_outsider_enters_pair:
  assumes image_pair: "pp_t_M5_exotic P \<in> pp_t_M5_pair"
  shows "P \<in> pp_t_M5_pair"
proof -
  have no_nonroot_pair:
      "\<And>w. w \<noteq> [] \<Longrightarrow>
        pp_b_view w P \<notin> pp_t_M5_pair"
    using image_pair pp_t_M5_preimage_pair_only_at_root by blast
  show ?thesis
  proof (cases "P \<in> pp_t_M5_pair")
    case True
    then show ?thesis .
  next
    case False
    have root_neither:
        "P \<noteq> pp_t_M5_s" "P \<noteq> pp_t_M5_s'"
      using False unfolding pp_t_M5_pair_def by blast+
    have unchanged: "pp_t_M5_exotic P = P"
    proof (rule set_eqI)
      fix w
      show "w \<in> pp_t_M5_exotic P \<longleftrightarrow> w \<in> P"
      proof (cases "w = []")
        case True
        then show ?thesis
          using root_neither by (simp add: pp_t_M5_flip_rule)
      next
        case False
        then have "pp_b_view w P \<notin> pp_t_M5_pair"
          by (rule no_nonroot_pair)
        then have
            "pp_b_view w P \<noteq> pp_t_M5_s"
            "pp_b_view w P \<noteq> pp_t_M5_s'"
          unfolding pp_t_M5_pair_def by blast+
        then show ?thesis
          by (simp add: pp_t_M5_flip_rule)
      qed
    qed
    show ?thesis
      using image_pair unchanged by simp
  qed
qed

lemma pp_t_M5_pair_iff_after_exotic:
  "pp_t_M5_exotic P \<in> pp_t_M5_pair
    \<longleftrightarrow> P \<in> pp_t_M5_pair"
  using pp_t_M5_no_outsider_enters_pair
    pp_t_M5_exotic_preserves_pair by blast

theorem pp_t_M5_exotic_involution:
  "pp_t_M5_exotic (pp_t_M5_exotic P) = P"
proof (rule set_eqI)
  fix w
  have pair_stable:
      "pp_b_view w (pp_t_M5_exotic P) \<in> pp_t_M5_pair
        \<longleftrightarrow> pp_b_view w P \<in> pp_t_M5_pair"
  proof -
    have
        "pp_b_view w (pp_t_M5_exotic P) \<in> pp_t_M5_pair
          \<longleftrightarrow>
         pp_t_M5_exotic (pp_b_view w P) \<in> pp_t_M5_pair"
      by (simp add: pp_t_M5_exotic_view)
    also have "... \<longleftrightarrow>
        pp_b_view w P \<in> pp_t_M5_pair"
      by (rule pp_t_M5_pair_iff_after_exotic)
    finally show ?thesis .
  qed
  show "w \<in> pp_t_M5_exotic (pp_t_M5_exotic P)
      \<longleftrightarrow> w \<in> P"
  proof (cases "pp_b_view w P = pp_t_M5_s")
    case True
    then have viewed:
        "pp_b_view w (pp_t_M5_exotic P) = pp_t_M5_s'"
      by (simp add: pp_t_M5_exotic_view pp_t_M5_exotic_s)
    have not_root: "[] \<notin> pp_b_view w P"
      using True by simp
    have "w \<notin> P"
      using not_root by (simp add: pp_b_view_membership_root)
    then show ?thesis
      using viewed by (simp add: pp_t_M5_flip_rule)
  next
    case not_s: False
    show ?thesis
    proof (cases "pp_b_view w P = pp_t_M5_s'")
      case True
      then have viewed:
          "pp_b_view w (pp_t_M5_exotic P) = pp_t_M5_s"
        by (simp add: pp_t_M5_exotic_view pp_t_M5_exotic_s')
      have root_in: "[] \<in> pp_b_view w P"
        using True by simp
      have "w \<in> P"
        using root_in by (simp add: pp_b_view_membership_root)
      then show ?thesis
        using viewed by (simp add: pp_t_M5_flip_rule)
    next
      case not_s': False
      have original_not_pair:
          "pp_b_view w P \<notin> pp_t_M5_pair"
        using not_s not_s'
        unfolding pp_t_M5_pair_def by blast
      have image_not_pair:
          "pp_b_view w (pp_t_M5_exotic P) \<notin> pp_t_M5_pair"
        using pair_stable original_not_pair by blast
      then have image_neither:
          "pp_b_view w (pp_t_M5_exotic P) \<noteq> pp_t_M5_s"
          "pp_b_view w (pp_t_M5_exotic P) \<noteq> pp_t_M5_s'"
        unfolding pp_t_M5_pair_def by blast+
      have first_unchanged:
          "w \<in> pp_t_M5_exotic P \<longleftrightarrow> w \<in> P"
        using not_s not_s'
        by (simp add: pp_t_M5_flip_rule)
      show ?thesis
        using image_neither first_unchanged
        by (simp add: pp_t_M5_flip_rule)
    qed
  qed
qed

corollary pp_t_M5_exotic_bijective:
  "bij pp_t_M5_exotic"
  unfolding bij_def inj_def surj_def
  using pp_t_M5_exotic_involution by metis

definition pp_t_M5_truth_preserving ::
    "pp_b_operator \<Rightarrow> bool" where
  "pp_t_M5_truth_preserving F \<longleftrightarrow>
    (\<forall>P. ([] \<in> F P) = ([] \<in> P))"

definition pp_t_M5_truth_flipping ::
    "pp_b_operator \<Rightarrow> bool" where
  "pp_t_M5_truth_flipping F \<longleftrightarrow>
    (\<forall>P. ([] \<in> F P) = ([] \<notin> P))"

theorem pp_t_M5_exotic_not_truth_uniform:
  "\<not> pp_t_M5_truth_preserving pp_t_M5_exotic
    \<and> \<not> pp_t_M5_truth_flipping pp_t_M5_exotic"
proof
  show "\<not> pp_t_M5_truth_preserving pp_t_M5_exotic"
  proof
    assume preserving:
        "pp_t_M5_truth_preserving pp_t_M5_exotic"
    have
        "([] \<in> pp_t_M5_exotic pp_t_M5_s') =
         ([] \<in> pp_t_M5_s')"
      using preserving
      unfolding pp_t_M5_truth_preserving_def by blast
    then show False
      by (simp add: pp_t_M5_exotic_s')
  qed
next
  show "\<not> pp_t_M5_truth_flipping pp_t_M5_exotic"
  proof
    assume flipping:
        "pp_t_M5_truth_flipping pp_t_M5_exotic"
    have
        "([] \<in> pp_t_M5_exotic UNIV) =
         ([] \<notin> (UNIV :: pp_b_prop))"
      using flipping
      unfolding pp_t_M5_truth_flipping_def by blast
    then show False
      by (simp add: pp_t_M5_exotic_fixes_top)
  qed
qed

definition pp_t_M5_biconditional_operator ::
    "pp_b_prop \<Rightarrow> pp_b_operator" where
  "pp_t_M5_biconditional_operator A =
    (\<lambda>P. (P \<inter> A) \<union> (- P \<inter> - A))"

lemma pp_t_M5_biconditional_fixes_top_only_if_top:
  assumes "pp_t_M5_biconditional_operator A UNIV = UNIV"
  shows "A = UNIV"
  using assms
  by (simp add: pp_t_M5_biconditional_operator_def)

lemma pp_t_M5_biconditional_top_is_identity:
  "pp_t_M5_biconditional_operator UNIV = id"
  by (rule ext)
    (simp add: pp_t_M5_biconditional_operator_def)

theorem pp_t_M5_exotic_not_biconditional:
  "\<not> (\<exists>A.
    pp_t_M5_exotic = pp_t_M5_biconditional_operator A)"
proof
  assume "\<exists>A.
      pp_t_M5_exotic = pp_t_M5_biconditional_operator A"
  then obtain A where representation:
      "pp_t_M5_exotic = pp_t_M5_biconditional_operator A"
    by blast
  have fixes_top:
      "pp_t_M5_biconditional_operator A UNIV = UNIV"
    using representation pp_t_M5_exotic_fixes_top by simp
  have "A = UNIV"
    using fixes_top
    by (rule pp_t_M5_biconditional_fixes_top_only_if_top)
  then have identity:
      "pp_t_M5_biconditional_operator A = id"
    by (simp add: pp_t_M5_biconditional_top_is_identity)
  have exotic_identity: "pp_t_M5_exotic = id"
    using representation identity by simp
  show False
    using exotic_identity pp_t_M5_exotic_not_identity by contradiction
qed

text \<open>
  We now place this operator in the HOL-ZF function domain.  The definition
  converts a ZF proposition to its Boolean-tree extension, applies the
  operator, and converts the result back.  Equivariance supplies both the
  modalized function-domain condition and cone-naturality.
\<close>

definition pp_t_M5_exotic_den :: ZF where
  "pp_t_M5_exotic_den =
    Lambda (pp_t_domain Prop)
      (\<lambda>P. pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P)))"

lemma pp_t_M5_exotic_respects_views:
  assumes "pp_b_view w P = pp_b_view w Q"
  shows "pp_b_view w (pp_t_M5_exotic P) =
    pp_b_view w (pp_t_M5_exotic Q)"
  using assms pp_t_M5_exotic_equivariant
  unfolding pp_b_equivariant_def by simp

theorem pp_t_M5_exotic_den_typed:
  "Elem pp_t_M5_exotic_den
    (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  unfolding pp_t_M5_exotic_den_def
proof (rule pp_t_lambda_closed)
  fix P
  assume "Elem P (pp_t_domain Prop)"
  show "Elem (pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P)))
      (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
next
  fix w P Q
  assume P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_eqv Prop w P Q"
  have exact_P: "pp_zf_of_b (pp_b_of_zf P) = P"
    using pp_zf_of_b_of_zf[OF P] .
  have exact_Q: "pp_zf_of_b (pp_b_of_zf Q) = Q"
    using pp_zf_of_b_of_zf[OF Q] .
  have input_views:
      "pp_b_view w (pp_b_of_zf P) =
        pp_b_view w (pp_b_of_zf Q)"
  proof (rule set_eqI)
    fix u
    have future: "prefix w (w @ u)"
      by (simp add: prefix_def)
    have at_future:
        "pp_t_holds P (w @ u) =
          pp_t_holds Q (w @ u)"
      using PQ future by simp
    show "u \<in> pp_b_view w (pp_b_of_zf P)
        \<longleftrightarrow>
        u \<in> pp_b_view w (pp_b_of_zf Q)"
      using at_future
      by (simp add: pp_b_view_def pp_b_of_zf_def)
  qed
  have output_views:
      "pp_b_view w
          (pp_t_M5_exotic (pp_b_of_zf P)) =
        pp_b_view w
          (pp_t_M5_exotic (pp_b_of_zf Q))"
    using pp_t_M5_exotic_respects_views[OF input_views] .
  show "pp_t_eqv Prop w
      (pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P)))
      (pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf Q)))"
  proof (simp only: pp_t_eqv.simps, intro allI impI)
    fix v
    assume future: "prefix w v"
    then obtain u where v: "v = w @ u"
      by (auto simp: prefix_def)
    have at_u:
        "(u \<in> pp_b_view w
            (pp_t_M5_exotic (pp_b_of_zf P))) =
          (u \<in> pp_b_view w
            (pp_t_M5_exotic (pp_b_of_zf Q)))"
      using arg_cong[OF output_views,
        of "\<lambda>X. u \<in> X"] .
    show "pp_t_holds
          (pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P))) v =
        pp_t_holds
          (pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf Q))) v"
      using at_u
      by (simp add: v pp_b_view_def)
  qed
qed

lemma pp_t_M5_exotic_den_apply:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_M5_exotic_den \<acute> P =
    pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P))"
  using P
  by (simp add: pp_t_M5_exotic_den_def Lambda_app)

theorem pp_t_M5_exotic_den_cone_natural:
  "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) s
    pp_t_M5_exotic_den pp_t_M5_exotic_den"
  unfolding pp_t_cone_rel.simps
  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (rule allI)
  subgoal premises prems for P Q u
  proof -
    have views:
        "pp_b_view (s @ u) (pp_b_of_zf P) =
          pp_b_view u (pp_b_of_zf Q)"
    proof (rule set_eqI)
      fix v
      have future:
          "pp_t_holds P (s @ (u @ v)) =
            pp_t_holds Q (u @ v)"
        using prems(3) by simp
      show "v \<in> pp_b_view (s @ u) (pp_b_of_zf P)
          \<longleftrightarrow>
          v \<in> pp_b_view u (pp_b_of_zf Q)"
        using future
        by (simp add: pp_b_view_def pp_b_of_zf_def)
    qed
    have classified:
        "(pp_b_view (s @ u) (pp_b_of_zf P)
            \<in> pp_t_M5_swapped_index) =
          (pp_b_view u (pp_b_of_zf Q)
            \<in> pp_t_M5_swapped_index)"
      using arg_cong[OF views,
        of "\<lambda>V. V \<in> pp_t_M5_swapped_index"] .
    show ?thesis
      using classified
      by (simp add: pp_t_M5_exotic_den_apply[OF prems(1)]
          pp_t_M5_exotic_den_apply[OF prems(2)]
          pp_t_M5_exotic_def pp_t_M5_classifier_def)
  qed
  done

theorem pp_t_M5_exotic_den_exact:
  "pp_b_operator_of pp_t_M5_exotic_den = pp_t_M5_exotic"
proof (rule ext)
  fix P
  show "pp_b_operator_of pp_t_M5_exotic_den P =
      pp_t_M5_exotic P"
    by (simp add: pp_b_operator_of_def
        pp_t_M5_exotic_den_apply[OF pp_zf_of_b_in_domain]
        pp_b_of_zf_def)
qed

theorem pp_t_M5_exotic_den_involution:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_M5_exotic_den \<acute>
      (pp_t_M5_exotic_den \<acute> P) = P"
proof -
  have first:
      "Elem (pp_t_M5_exotic_den \<acute> P) (pp_t_domain Prop)"
    using pp_t_app_closed[OF pp_t_M5_exotic_den_typed P] .
  have inner:
      "pp_t_M5_exotic_den \<acute> P =
        pp_zf_of_b (pp_t_M5_exotic (pp_b_of_zf P))"
    by (rule pp_t_M5_exotic_den_apply[OF P])
  have outer:
      "pp_t_M5_exotic_den \<acute>
          (pp_t_M5_exotic_den \<acute> P) =
        pp_zf_of_b
          (pp_t_M5_exotic
            (pp_b_of_zf (pp_t_M5_exotic_den \<acute> P)))"
    by (rule pp_t_M5_exotic_den_apply[OF first])
  have exact_P: "pp_zf_of_b (pp_b_of_zf P) = P"
    using pp_zf_of_b_of_zf[OF P] .
  show ?thesis
    using outer inner
      pp_t_M5_exotic_involution[of "pp_b_of_zf P"]
      exact_P by simp
qed

lemma pp_t_M5_exotic_den_swaps:
  "pp_t_M5_exotic_den \<acute> pp_zf_of_b pp_t_M5_s =
      pp_zf_of_b pp_t_M5_s'"
  "pp_t_M5_exotic_den \<acute> pp_zf_of_b pp_t_M5_s' =
      pp_zf_of_b pp_t_M5_s"
  by (simp_all add:
      pp_t_M5_exotic_den_apply[OF pp_zf_of_b_in_domain]
      pp_t_M5_exotic_s pp_t_M5_exotic_s')

lemma pp_t_M5_exotic_den_fixes_extremes:
  "pp_t_M5_exotic_den \<acute> pp_zf_of_b UNIV =
      pp_zf_of_b UNIV"
  "pp_t_M5_exotic_den \<acute> pp_zf_of_b {} =
      pp_zf_of_b {}"
  by (simp_all add:
      pp_t_M5_exotic_den_apply[OF pp_zf_of_b_in_domain]
      pp_t_M5_exotic_fixes_top pp_t_M5_exotic_fixes_bottom)

subsection \<open>The enlarged definable stock\<close>

text \<open>
  A basis expression is a closed logical term, the new exotic constant, or
  an application of two earlier expressions.  Consequently the following
  basis is exactly the applicative stock of denotations definable after the
  exotic constant is added to the language.  In particular, it is not merely
  the old stock with one denotation adjoined: all new applications involving
  the exotic constant are present as well.
\<close>

datatype pp_t_M5_basis_expr =
    PPM5Logical oterm
  | PPM5Exotic
  | PPM5Apply pp_t_M5_basis_expr pp_t_M5_basis_expr

instantiation pp_t_M5_basis_expr :: countable
begin

instance
  by countable_datatype

end

fun pp_t_M5_basis_expr_type ::
    "pp_t_M5_basis_expr \<Rightarrow> otype option"
where
  "pp_t_M5_basis_expr_type (PPM5Logical M) =
    (if pp_logical_vocabulary M
     then infer_type [] M else None)"
| "pp_t_M5_basis_expr_type PPM5Exotic =
    Some (Prop \<rightarrow>\<^sub>o Prop)"
| "pp_t_M5_basis_expr_type (PPM5Apply F X) =
    (case pp_t_M5_basis_expr_type F of
      Some (\<sigma> \<rightarrow>\<^sub>o \<tau>) =>
        (if pp_t_M5_basis_expr_type X = Some \<sigma>
         then Some \<tau> else None)
    | _ => None)"

fun pp_t_M5_basis_expr_den ::
    "pp_t_M5_basis_expr \<Rightarrow> ZF"
where
  "pp_t_M5_basis_expr_den (PPM5Logical M) = pp_t_closed_den M"
| "pp_t_M5_basis_expr_den PPM5Exotic = pp_t_M5_exotic_den"
| "pp_t_M5_basis_expr_den (PPM5Apply F X) =
    pp_t_M5_basis_expr_den F \<acute> pp_t_M5_basis_expr_den X"

definition pp_t_M5_rebuilt_basis :: "otype \<Rightarrow> ZF set" where
  "pp_t_M5_rebuilt_basis \<sigma> =
    pp_t_M5_basis_expr_den `
      {T. pp_t_M5_basis_expr_type T = Some \<sigma>}"

lemma pp_t_M5_basis_expr_den_typed:
  assumes T: "pp_t_M5_basis_expr_type T = Some \<sigma>"
  shows "Elem (pp_t_M5_basis_expr_den T) (pp_t_domain \<sigma>)"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPM5Logical M)
  then have logical: "pp_logical_vocabulary M"
    and inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have typed: "[] \<turnstile> M : \<sigma>"
    using infer_type_sound[OF inferred] .
  show ?case
    using pp_t_closed_den_in_domain[OF typed] by simp
next
  case PPM5Exotic
  then have "\<sigma> = (Prop \<rightarrow>\<^sub>o Prop)"
    by simp
  then show ?case
    using pp_t_M5_exotic_den_typed by simp
next
  case (PPM5Apply F X)
  then obtain \<alpha> \<beta> where
      F_type: "pp_t_M5_basis_expr_type F =
        Some (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
    and X_type: "pp_t_M5_basis_expr_type X = Some \<alpha>"
    and sigma: "\<sigma> = \<beta>"
    by (auto split: option.splits otype.splits if_splits)
  have F_den:
      "Elem (pp_t_M5_basis_expr_den F)
        (pp_t_domain (\<alpha> \<rightarrow>\<^sub>o \<beta>))"
    using PPM5Apply.IH(1)[OF F_type] .
  have X_den:
      "Elem (pp_t_M5_basis_expr_den X) (pp_t_domain \<alpha>)"
    using PPM5Apply.IH(2)[OF X_type] .
  show ?case
    unfolding sigma pp_t_M5_basis_expr_den.simps
    using pp_t_app_closed[OF F_den X_den] .
qed

lemma pp_t_M5_basis_expr_den_cone_natural:
  assumes T: "pp_t_M5_basis_expr_type T = Some \<sigma>"
  shows "pp_t_cone_rel \<sigma> s
    (pp_t_M5_basis_expr_den T) (pp_t_M5_basis_expr_den T)"
  using T
proof (induction T arbitrary: \<sigma>)
  case (PPM5Logical M)
  then have logical: "pp_logical_vocabulary M"
    and inferred: "infer_type [] M = Some \<sigma>"
    by (auto split: if_splits)
  have typed: "[] \<turnstile> M : \<sigma>"
    using infer_type_sound[OF inferred] .
  show ?case
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] by simp
next
  case PPM5Exotic
  then show ?case
    using pp_t_M5_exotic_den_cone_natural[of s] by simp
next
  case (PPM5Apply F X)
  then obtain \<alpha> \<beta> where
      F_type: "pp_t_M5_basis_expr_type F =
        Some (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
    and X_type: "pp_t_M5_basis_expr_type X = Some \<alpha>"
    and sigma: "\<sigma> = \<beta>"
    by (auto split: option.splits otype.splits if_splits)
  have F_rel:
      "pp_t_cone_rel (\<alpha> \<rightarrow>\<^sub>o \<beta>) s
        (pp_t_M5_basis_expr_den F) (pp_t_M5_basis_expr_den F)"
    using PPM5Apply.IH(1)[OF F_type] .
  have X_rel:
      "pp_t_cone_rel \<alpha> s
        (pp_t_M5_basis_expr_den X) (pp_t_M5_basis_expr_den X)"
    using PPM5Apply.IH(2)[OF X_type] .
  have X_den:
      "Elem (pp_t_M5_basis_expr_den X) (pp_t_domain \<alpha>)"
    using pp_t_M5_basis_expr_den_typed[OF X_type] .
  show ?case
    unfolding sigma pp_t_M5_basis_expr_den.simps
    using F_rel X_den X_den X_rel by simp
qed

lemma pp_t_M5_rebuilt_basis_countable:
  "countable (pp_t_M5_rebuilt_basis \<sigma>)"
  unfolding pp_t_M5_rebuilt_basis_def
  by simp

lemma pp_t_M5_rebuilt_basis_typed:
  assumes "d \<in> pp_t_M5_rebuilt_basis \<sigma>"
  shows "Elem d (pp_t_domain \<sigma>)"
  using assms pp_t_M5_basis_expr_den_typed
  unfolding pp_t_M5_rebuilt_basis_def by blast

lemma pp_t_M5_rebuilt_basis_cone_natural:
  assumes "d \<in> pp_t_M5_rebuilt_basis \<sigma>"
  shows "pp_t_cone_rel \<sigma> s d d"
  using assms pp_t_M5_basis_expr_den_cone_natural
  unfolding pp_t_M5_rebuilt_basis_def by blast

lemma pp_t_M5_rebuilt_basis_contains_logical:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_closed_den M \<in> pp_t_M5_rebuilt_basis \<sigma>"
proof -
  have inferred: "infer_type [] M = Some \<sigma>"
    using infer_type_complete[OF typed] .
  have expression:
      "pp_t_M5_basis_expr_type (PPM5Logical M) = Some \<sigma>"
    using logical inferred by simp
  show ?thesis
    unfolding pp_t_M5_rebuilt_basis_def
  proof (rule image_eqI[where x="PPM5Logical M"])
    show "pp_t_closed_den M =
        pp_t_M5_basis_expr_den (PPM5Logical M)"
      by simp
    show "PPM5Logical M \<in>
        {T. pp_t_M5_basis_expr_type T = Some \<sigma>}"
      using expression by simp
  qed
qed

lemma pp_t_M5_exotic_in_rebuilt_definable_basis:
  "pp_t_M5_exotic_den \<in>
    pp_t_M5_rebuilt_basis (Prop \<rightarrow>\<^sub>o Prop)"
  unfolding pp_t_M5_rebuilt_basis_def
  by (rule image_eqI[where x=PPM5Exotic]) simp_all

lemma pp_t_M5_rebuilt_basis_application:
  assumes f:
      "f \<in> pp_t_M5_rebuilt_basis
        (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and x: "x \<in> pp_t_M5_rebuilt_basis \<sigma>"
  shows "f \<acute> x \<in> pp_t_M5_rebuilt_basis \<tau>"
proof -
  obtain F where
      F_type: "pp_t_M5_basis_expr_type F =
        Some (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and f_def: "f = pp_t_M5_basis_expr_den F"
    using f unfolding pp_t_M5_rebuilt_basis_def by blast
  obtain X where X_type:
      "pp_t_M5_basis_expr_type X = Some \<sigma>"
    and x_def: "x = pp_t_M5_basis_expr_den X"
    using x unfolding pp_t_M5_rebuilt_basis_def by blast
  have application:
      "pp_t_M5_basis_expr_type (PPM5Apply F X) = Some \<tau>"
    using F_type X_type by simp
  show ?thesis
    unfolding pp_t_M5_rebuilt_basis_def f_def x_def
  proof (rule image_eqI[where x="PPM5Apply F X"])
    show "pp_t_M5_basis_expr_den F \<acute>
        pp_t_M5_basis_expr_den X =
        pp_t_M5_basis_expr_den (PPM5Apply F X)"
      by simp
    show "PPM5Apply F X \<in>
        {T. pp_t_M5_basis_expr_type T = Some \<tau>}"
      using application by simp
  qed
qed

interpretation M5Rebuilt:
  pp_t_stock_basis pp_t_M5_rebuilt_basis
proof
  fix \<sigma> d
  assume "d \<in> pp_t_M5_rebuilt_basis \<sigma>"
  then show "Elem d (pp_t_domain \<sigma>)"
    by (rule pp_t_M5_rebuilt_basis_typed)
next
  fix \<sigma>
  show "countable (pp_t_M5_rebuilt_basis \<sigma>)"
    by (rule pp_t_M5_rebuilt_basis_countable)
next
  fix \<sigma> d s
  assume "d \<in> pp_t_M5_rebuilt_basis \<sigma>"
  then show "pp_t_cone_rel \<sigma> s d d"
    by (rule pp_t_M5_rebuilt_basis_cone_natural)
next
  fix \<sigma> M
  assume typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  show "pp_t_closed_den M \<in> pp_t_M5_rebuilt_basis \<sigma>"
    using pp_t_M5_rebuilt_basis_contains_logical[
      OF typed logical] .
next
  fix \<sigma> \<tau> f x
  assume f:
      "f \<in> pp_t_M5_rebuilt_basis
        (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and x: "x \<in> pp_t_M5_rebuilt_basis \<sigma>"
  have app: "f \<acute> x \<in> pp_t_M5_rebuilt_basis \<tau>"
    using pp_t_M5_rebuilt_basis_application[OF f x] .
  have typed: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_M5_rebuilt_basis_typed[OF app] .
  have refl: "pp_t_eqv \<tau> [] (f \<acute> x) (f \<acute> x)"
    using pp_t_eqv_reflexive[OF typed] .
  show "\<exists>d \<in> pp_t_M5_rebuilt_basis \<tau>.
      pp_t_eqv \<tau> [] (f \<acute> x) d"
    using app refl by blast
qed

lemma pp_t_M5_exotic_pure_in_rebuilt_definable_stock:
  "pp_t_basis_stock pp_t_M5_rebuilt_basis
    (Prop \<rightarrow>\<^sub>o Prop) w pp_t_M5_exotic_den"
  using M5Rebuilt.pp_t_basis_member_in_stock[
    OF pp_t_M5_exotic_in_rebuilt_definable_basis] .

theorem pp_t_M5_rebuilt_operator_stock_countable:
  "countable M5Rebuilt.pp_b_basis_operator_stock"
  by (rule M5Rebuilt.pp_b_basis_operator_stock_countable)

theorem pp_t_M5_rebuilt_operator_stock_equivariant:
  assumes "F \<in> M5Rebuilt.pp_b_basis_operator_stock"
  shows "pp_b_equivariant F"
  using assms by (rule M5Rebuilt.pp_b_basis_operator_stock_equivariant)

theorem pp_t_M5_rebuilt_basis_least:
  assumes logical:
      "\<And>\<sigma> M. [] \<turnstile> M : \<sigma> \<Longrightarrow>
        pp_logical_vocabulary M \<Longrightarrow>
        pp_t_closed_den M \<in> B \<sigma>"
    and exotic:
      "pp_t_M5_exotic_den \<in> B (Prop \<rightarrow>\<^sub>o Prop)"
    and application:
      "\<And>\<sigma> \<tau> f x.
        f \<in> B (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow>
        x \<in> B \<sigma> \<Longrightarrow> f \<acute> x \<in> B \<tau>"
  shows "pp_t_M5_rebuilt_basis \<sigma> \<subseteq> B \<sigma>"
proof
  fix d
  assume "d \<in> pp_t_M5_rebuilt_basis \<sigma>"
  then obtain T where T:
      "pp_t_M5_basis_expr_type T = Some \<sigma>"
    and d: "d = pp_t_M5_basis_expr_den T"
    unfolding pp_t_M5_rebuilt_basis_def by blast
  have "pp_t_M5_basis_expr_den T \<in> B \<sigma>"
    using T
  proof (induction T arbitrary: \<sigma>)
    case (PPM5Logical M)
    then have vocab: "pp_logical_vocabulary M"
      and inferred: "infer_type [] M = Some \<sigma>"
      by (auto split: if_splits)
    have typed: "[] \<turnstile> M : \<sigma>"
      using infer_type_sound[OF inferred] .
    show ?case
      using logical[OF typed vocab] by simp
  next
    case PPM5Exotic
    then show ?case
      using exotic by simp
  next
    case (PPM5Apply F X)
    then obtain \<alpha> \<beta> where
        F_type: "pp_t_M5_basis_expr_type F =
          Some (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
      and X_type: "pp_t_M5_basis_expr_type X = Some \<alpha>"
      and sigma: "\<sigma> = \<beta>"
      by (auto split: option.splits otype.splits if_splits)
    have F: "pp_t_M5_basis_expr_den F \<in>
        B (\<alpha> \<rightarrow>\<^sub>o \<beta>)"
      using PPM5Apply.IH(1)[OF F_type] .
    have X: "pp_t_M5_basis_expr_den X \<in> B \<alpha>"
      using PPM5Apply.IH(2)[OF X_type] .
    show ?case
      unfolding sigma pp_t_M5_basis_expr_den.simps
      using application[OF F X] .
  qed
  then show "d \<in> B \<sigma>"
    unfolding d .
qed

theorem pp_b_common_generic_witness_for_countable_stock:
  fixes Stock :: "pp_b_operator set"
  assumes countable: "countable Stock"
    and equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows "\<exists>R.
    (\<forall>F \<in> Stock. pp_b_root_unary_recombination F R)
    \<and>
    (\<forall>F \<in> Stock. \<forall>G \<in> Stock.
      (F R = G R \<longleftrightarrow> F = G))"
proof (cases "Stock = {}")
  case True
  then show ?thesis by simp
next
  case False
  let ?E = "from_nat_into Stock"
  let ?Pairs = "Stock \<times> Stock"
  let ?EP = "from_nat_into ?Pairs"
  have range_E: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have pairs_countable: "countable ?Pairs"
    using countable by simp
  have pairs_nonempty: "?Pairs \<noteq> {}"
    using False by blast
  have range_EP: "range ?EP = ?Pairs"
    using pairs_nonempty pairs_countable
    by (rule range_from_nat_into)
  let ?Q =
    "\<lambda>k.
      if even k
      then pp_b_counterexample_choice ?E (k div 2)
      else
        (let p = ?EP (k div 2)
         in if fst p = snd p then {}
            else SOME P. fst p P \<noteq> snd p P)"
  let ?R = "pp_b_generic_witness ?Q"
  have recombines:
      "pp_b_root_unary_recombination F ?R"
    if F: "F \<in> Stock" for F
  proof (unfold pp_b_root_unary_recombination_def, intro impI)
    assume necessary: "\<forall>w. w \<in> F ?R"
    show "\<forall>P. [] \<in> F P"
    proof (rule ccontr)
      assume nonuniversal: "\<not> (\<forall>P. [] \<in> F P)"
      have F_range: "F \<in> range ?E"
        using F range_E by simp
      then obtain n where F_n: "F = ?E n"
        by blast
      have E_n: "?E n = F"
        using F_n by simp
      have choice_false:
          "[] \<notin> F (pp_b_counterexample_choice ?E n)"
        using pp_b_counterexample_choice_falsifies[
          of ?E n] nonuniversal E_n by simp
      have view_R:
          "pp_b_view (pp_b_code (2 * n)) ?R =
            pp_b_counterexample_choice ?E n"
        by simp
      have view_output:
          "pp_b_view (pp_b_code (2 * n)) (F ?R) =
            F (pp_b_counterexample_choice ?E n)"
        using equivariant[OF F] view_R
        unfolding pp_b_equivariant_def by simp
      have root_view:
          "[] \<in> pp_b_view (pp_b_code (2 * n)) (F ?R)"
        using necessary by simp
      have "[] \<in> F (pp_b_counterexample_choice ?E n)"
        using root_view view_output by simp
      then show False
        using choice_false by contradiction
    qed
  qed
  have separates:
      "F ?R = G ?R \<Longrightarrow> F = G"
    if F: "F \<in> Stock" and G: "G \<in> Stock" for F G
  proof (rule ccontr)
    assume outputs: "F ?R = G ?R"
      and distinct: "F \<noteq> G"
    have pair: "(F, G) \<in> ?Pairs"
      using F G by simp
    have pair_range: "(F, G) \<in> range ?EP"
      using pair range_EP by simp
    then obtain n where pair_n_rev: "(F, G) = ?EP n"
      by blast
    have pair_n: "?EP n = (F, G)"
      using pair_n_rev by simp
    have witness:
        "\<exists>P. F P \<noteq> G P"
      using distinct by (auto simp: fun_eq_iff)
    have Q_distinct:
        "F (?Q (Suc (2 * n))) \<noteq>
          G (?Q (Suc (2 * n)))"
      using someI_ex[OF witness] pair_n distinct by simp
    have F_view:
        "pp_b_view (pp_b_code (Suc (2 * n))) (F ?R) =
          F (?Q (Suc (2 * n)))"
    proof -
      have view_R:
          "pp_b_view (pp_b_code (Suc (2 * n))) ?R =
            ?Q (Suc (2 * n))"
        by (rule pp_b_view_generic_witness)
      have F_equivariant:
          "pp_b_view (pp_b_code (Suc (2 * n))) (F ?R) =
            F (pp_b_view (pp_b_code (Suc (2 * n))) ?R)"
        using equivariant[OF F]
        unfolding pp_b_equivariant_def by blast
      show ?thesis
        using F_equivariant view_R by simp
    qed
    have G_view:
        "pp_b_view (pp_b_code (Suc (2 * n))) (G ?R) =
          G (?Q (Suc (2 * n)))"
    proof -
      have view_R:
          "pp_b_view (pp_b_code (Suc (2 * n))) ?R =
            ?Q (Suc (2 * n))"
        by (rule pp_b_view_generic_witness)
      have G_equivariant:
          "pp_b_view (pp_b_code (Suc (2 * n))) (G ?R) =
            G (pp_b_view (pp_b_code (Suc (2 * n))) ?R)"
        using equivariant[OF G]
        unfolding pp_b_equivariant_def by blast
      show ?thesis
        using G_equivariant view_R by simp
    qed
    show False
      using outputs F_view G_view Q_distinct by simp
  qed
  show ?thesis
  proof (intro exI[of _ ?R] conjI)
    show "\<forall>F \<in> Stock.
        pp_b_root_unary_recombination F ?R"
    proof (rule ballI)
      fix F
      assume "F \<in> Stock"
      then show "pp_b_root_unary_recombination F ?R"
        by (rule recombines)
    qed
  next
    show "\<forall>F \<in> Stock. \<forall>G \<in> Stock.
        (F ?R = G ?R \<longleftrightarrow> F = G)"
    proof (rule ballI)
    fix F
    assume F: "F \<in> Stock"
    show "\<forall>G \<in> Stock. F ?R = G ?R \<longleftrightarrow> F = G"
      by (auto intro: separates[OF F])
    qed
  qed
qed

definition pp_t_M5_common_boolean_seed :: pp_b_prop where
  "pp_t_M5_common_boolean_seed =
    (SOME R.
      (\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
        pp_b_root_unary_recombination F R)
      \<and>
      (\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
        \<forall>G \<in> M5Rebuilt.pp_b_basis_operator_stock.
          (F R = G R \<longleftrightarrow> F = G)))"

lemma pp_t_M5_common_boolean_seed_spec:
  "(\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
      pp_b_root_unary_recombination F
        pp_t_M5_common_boolean_seed)
    \<and>
    (\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
      \<forall>G \<in> M5Rebuilt.pp_b_basis_operator_stock.
        (F pp_t_M5_common_boolean_seed =
          G pp_t_M5_common_boolean_seed
        \<longleftrightarrow> F = G))"
proof -
  have exists:
      "\<exists>R.
        (\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
          pp_b_root_unary_recombination F R)
        \<and>
        (\<forall>F \<in> M5Rebuilt.pp_b_basis_operator_stock.
          \<forall>G \<in> M5Rebuilt.pp_b_basis_operator_stock.
            (F R = G R \<longleftrightarrow> F = G))"
    using pp_b_common_generic_witness_for_countable_stock[
      OF pp_t_M5_rebuilt_operator_stock_countable
        pp_t_M5_rebuilt_operator_stock_equivariant] .
  show ?thesis
    unfolding pp_t_M5_common_boolean_seed_def
    using someI_ex[OF exists] .
qed

definition pp_t_M5_root_fundamental :: ZF where
  "pp_t_M5_root_fundamental =
    pp_zf_of_b pp_t_M5_common_boolean_seed"

lemma pp_t_M5_root_fundamental_typed:
  "Elem pp_t_M5_root_fundamental (pp_t_domain Prop)"
  unfolding pp_t_M5_root_fundamental_def
  by (rule pp_zf_of_b_in_domain)

lemma pp_t_M5_root_fundamental_recombines:
  "pp_t_unary_recombines_at
    (pp_t_basis_stock pp_t_M5_rebuilt_basis
      (Prop \<rightarrow>\<^sub>o Prop))
    pp_t_M5_root_fundamental []"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X_typed:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] X"
    and necessary:
      "\<forall>v. prefix [] v \<longrightarrow>
        pp_t_holds (X \<acute> pp_t_M5_root_fundamental) v"
    and q: "Elem q (pp_t_domain Prop)"
  have X_basis:
      "X \<in> pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop)"
    using X_stock
    by (simp add: M5Rebuilt.pp_t_basis_stock_root_iff)
  have X_operator:
      "pp_b_operator_of X \<in>
        M5Rebuilt.pp_b_basis_operator_stock"
    using X_basis
    unfolding M5Rebuilt.pp_b_basis_operator_stock_def by blast
  have recombines:
      "pp_b_root_unary_recombination
        (pp_b_operator_of X) pp_t_M5_common_boolean_seed"
    using pp_t_M5_common_boolean_seed_spec X_operator by blast
  have necessary':
      "\<forall>v.
        pp_t_holds
          (X \<acute> pp_zf_of_b pp_t_M5_common_boolean_seed) v"
    using necessary
    unfolding pp_t_M5_root_fundamental_def by simp
  show "pp_t_holds (X \<acute> q) []"
    using pp_b_recombination_transfers_to_zf[
      OF recombines necessary'] q by blast
qed

lemma pp_b_operator_of_injective_on_typed_unary:
  assumes X:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and Y:
      "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and operators: "pp_b_operator_of X = pp_b_operator_of Y"
  shows "X = Y"
proof -
  have X_fun:
      "Elem X (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[OF X] .
  have Y_fun:
      "Elem Y (Fun (pp_t_domain Prop) (pp_t_domain Prop))"
    using pp_t_arrow_member_function[OF Y] .
  obtain F where X_rep:
      "X = Lambda (pp_t_domain Prop) F"
    using Elem_Fun_Lambda[OF X_fun] by blast
  obtain G where Y_rep:
      "Y = Lambda (pp_t_domain Prop) G"
    using Elem_Fun_Lambda[OF Y_fun] by blast
  have pointwise:
      "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow>
        F p = G p"
  proof -
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    have outputs:
        "pp_b_of_zf (X \<acute> p) = pp_b_of_zf (Y \<acute> p)"
    proof -
      have at_p:
          "pp_b_operator_of X (pp_b_of_zf p) =
            pp_b_operator_of Y (pp_b_of_zf p)"
        using fun_cong[OF operators, of "pp_b_of_zf p"] .
      show ?thesis
        using at_p pp_zf_of_b_of_zf[OF p]
        by (simp add: pp_b_operator_of_def)
    qed
    have Xp: "Elem (X \<acute> p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF X p] .
    have Yp: "Elem (Y \<acute> p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF Y p] .
    have app_eq: "X \<acute> p = Y \<acute> p"
    proof (rule pp_t_prop_ext[OF Xp Yp])
      fix w
      have at_w:
          "(w \<in> pp_b_of_zf (X \<acute> p)) =
            (w \<in> pp_b_of_zf (Y \<acute> p))"
        using arg_cong[OF outputs,
          of "\<lambda>S. w \<in> S"] .
      show "pp_t_holds (X \<acute> p) w \<longleftrightarrow>
          pp_t_holds (Y \<acute> p) w"
        using at_w by (simp add: pp_b_of_zf_def)
    qed
    show "F p = G p"
      using app_eq p X_rep Y_rep
      by (simp add: Lambda_app)
  qed
  show ?thesis
    using X_rep Y_rep pointwise by (simp add: Lambda_ext)
qed

theorem pp_t_M5_root_fundamental_is_fun_prime:
  assumes X:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] X"
    and Y:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] Y"
  shows
    "(X \<acute> pp_t_M5_root_fundamental =
        Y \<acute> pp_t_M5_root_fundamental)
      \<longleftrightarrow> X = Y"
proof
  assume outputs:
      "X \<acute> pp_t_M5_root_fundamental =
        Y \<acute> pp_t_M5_root_fundamental"
  have X_basis:
      "X \<in> pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop)"
    using X by (simp add: M5Rebuilt.pp_t_basis_stock_root_iff)
  have Y_basis:
      "Y \<in> pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop)"
    using Y by (simp add: M5Rebuilt.pp_t_basis_stock_root_iff)
  have X_typed:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_M5_rebuilt_basis_typed[OF X_basis] .
  have Y_typed:
      "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_M5_rebuilt_basis_typed[OF Y_basis] .
  have X_operator:
      "pp_b_operator_of X \<in>
        M5Rebuilt.pp_b_basis_operator_stock"
    using X_basis
    unfolding M5Rebuilt.pp_b_basis_operator_stock_def by blast
  have Y_operator:
      "pp_b_operator_of Y \<in>
        M5Rebuilt.pp_b_basis_operator_stock"
    using Y_basis
    unfolding M5Rebuilt.pp_b_basis_operator_stock_def by blast
  have abstract_outputs:
      "pp_b_operator_of X pp_t_M5_common_boolean_seed =
        pp_b_operator_of Y pp_t_M5_common_boolean_seed"
    using outputs
    unfolding pp_t_M5_root_fundamental_def
      pp_b_operator_of_def by simp
  have operator_eq:
      "pp_b_operator_of X = pp_b_operator_of Y"
    using pp_t_M5_common_boolean_seed_spec
      X_operator Y_operator abstract_outputs by blast
  show "X = Y"
    using pp_b_operator_of_injective_on_typed_unary[
      OF X_typed Y_typed operator_eq] .
next
  assume "X = Y"
  then show "X \<acute> pp_t_M5_root_fundamental =
      Y \<acute> pp_t_M5_root_fundamental"
    by simp
qed

definition pp_t_M5_fundamental_at :: "bool list \<Rightarrow> ZF" where
  "pp_t_M5_fundamental_at w =
    pp_t_cone_lift w pp_t_M5_root_fundamental"

lemma pp_t_M5_fundamental_at_typed:
  "Elem (pp_t_M5_fundamental_at w) (pp_t_domain Prop)"
  unfolding pp_t_M5_fundamental_at_def
  by (rule pp_t_cone_lift_in_domain)

lemma pp_t_M5_fundamental_at_recombines:
  "pp_t_unary_recombines_at
    (pp_t_basis_stock pp_t_M5_rebuilt_basis
      (Prop \<rightarrow>\<^sub>o Prop))
    (pp_t_M5_fundamental_at w) w"
  unfolding pp_t_M5_fundamental_at_def
  using M5Rebuilt.pp_t_basis_root_recombination_transports_to_cone[
    OF pp_t_M5_root_fundamental_typed
      pp_t_M5_root_fundamental_recombines] .

lemma pp_t_cone_rel_application:
  assumes fg:
      "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f g"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_cone_rel \<sigma> s x y"
  shows "pp_t_cone_rel \<tau> s (f \<acute> x) (g \<acute> y)"
  using assms by simp

lemma pp_t_application_equality_transports_to_cone:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and F:
      "Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and g:
      "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and G:
      "Elem G (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and fF: "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s f F"
    and gG: "pp_t_cone_rel (\<sigma> \<rightarrow>\<^sub>o \<tau>) s g G"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and X: "Elem X (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and Y: "Elem Y (pp_t_domain \<sigma>)"
    and xX: "pp_t_cone_rel \<sigma> s x X"
    and yY: "pp_t_cone_rel \<sigma> s y Y"
  shows
    "pp_t_eqv \<tau> (s @ u) (f \<acute> x) (g \<acute> y)
      \<longleftrightarrow>
      pp_t_eqv \<tau> u (F \<acute> X) (G \<acute> Y)"
proof -
  have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF f x] .
  have FX: "Elem (F \<acute> X) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF F X] .
  have gy: "Elem (g \<acute> y) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF g y] .
  have GY: "Elem (G \<acute> Y) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF G Y] .
  have fx_FX: "pp_t_cone_rel \<tau> s (f \<acute> x) (F \<acute> X)"
    using pp_t_cone_rel_application[OF fF x X xX] .
  have gy_GY: "pp_t_cone_rel \<tau> s (g \<acute> y) (G \<acute> Y)"
    using pp_t_cone_rel_application[OF gG y Y yY] .
  show ?thesis
    by (rule UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF fx FX gy GY fx_FX gy_GY])
qed

context pp_t_stock_basis
begin

lemma pp_t_fun_prime_transports_to_cone:
  assumes r: "Elem r (pp_t_domain Prop)"
    and root:
      "\<And>F G.
        Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<Longrightarrow>
        Elem G (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<Longrightarrow>
        pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) [] F \<Longrightarrow>
        pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) [] G \<Longrightarrow>
        (pp_t_eqv Prop [] (F \<acute> r) (G \<acute> r)
          \<longleftrightarrow>
          pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] F G)"
    and f:
      "Elem f (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and g:
      "Elem g (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and f_stock:
      "pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) w f"
    and g_stock:
      "pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) w g"
  shows
    "pp_t_eqv Prop w
        (f \<acute> pp_t_cone_lift w r)
        (g \<acute> pp_t_cone_lift w r)
      \<longleftrightarrow>
      pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
proof -
  let ?F = "pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) w f"
  let ?G = "pp_t_cone_restrict (Prop \<rightarrow>\<^sub>o Prop) w g"
  have F: "Elem ?F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_cone_restrict_in_domain[OF f] .
  have G: "Elem ?G (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_cone_restrict_in_domain[OF g] .
  have fF: "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) w f ?F"
    using pp_t_cone_restrict_related[OF f] .
  have gG: "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) w g ?G"
    using pp_t_cone_restrict_related[OF g] .
  have F_stock:
      "pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) [] ?F"
    using pp_t_basis_stock_cone_iff[OF f F fF, of "[]"]
      f_stock by simp
  have G_stock:
      "pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop) [] ?G"
    using pp_t_basis_stock_cone_iff[OF g G gG, of "[]"]
      g_stock by simp
  have lift: "Elem (pp_t_cone_lift w r) (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have lift_r:
      "pp_t_cone_rel Prop w (pp_t_cone_lift w r) r"
    using pp_t_cone_extend_related[OF r, of w] by simp
  have outputs:
      "pp_t_eqv Prop (w @ [])
          (f \<acute> pp_t_cone_lift w r)
          (g \<acute> pp_t_cone_lift w r)
        \<longleftrightarrow>
        pp_t_eqv Prop [] (?F \<acute> r) (?G \<acute> r)"
    using pp_t_application_equality_transports_to_cone[
      OF f F g G fF gG lift r lift r lift_r lift_r,
      of "[]"] .
  have operators:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) (w @ []) f g
        \<longleftrightarrow>
        pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
    by (rule UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF f F g G fF gG])
  have root_instance:
      "pp_t_eqv Prop [] (?F \<acute> r) (?G \<acute> r)
        \<longleftrightarrow>
        pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
    using root[OF F G F_stock G_stock] .
  have w_nil: "w @ [] = w"
    by simp
  have outputs_at_w:
      "pp_t_eqv Prop w
          (f \<acute> pp_t_cone_lift w r)
          (g \<acute> pp_t_cone_lift w r)
        \<longleftrightarrow>
        pp_t_eqv Prop [] (?F \<acute> r) (?G \<acute> r)"
    using outputs unfolding w_nil .
  have operators_at_w:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g
        \<longleftrightarrow>
        pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
    using operators unfolding w_nil .
  have root_to_world:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G
        \<longleftrightarrow>
        pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
  proof
    assume root_operators:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
    show "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
      using iffD2[OF operators_at_w root_operators] .
  next
    assume world_operators:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
    show "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
      using iffD1[OF operators_at_w world_operators] .
  qed
  show ?thesis
  proof
    assume world_outputs:
        "pp_t_eqv Prop w
          (f \<acute> pp_t_cone_lift w r)
          (g \<acute> pp_t_cone_lift w r)"
    have root_outputs:
        "pp_t_eqv Prop [] (?F \<acute> r) (?G \<acute> r)"
      using iffD1[OF outputs_at_w world_outputs] .
    have root_operators:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
      using iffD1[OF root_instance root_outputs] .
    show "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
      using iffD1[OF root_to_world root_operators] .
  next
    assume world_operators:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w f g"
    have root_operators:
        "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] ?F ?G"
      using iffD2[OF root_to_world world_operators] .
    have root_outputs:
        "pp_t_eqv Prop [] (?F \<acute> r) (?G \<acute> r)"
      using iffD2[OF root_instance root_operators] .
    show "pp_t_eqv Prop w
        (f \<acute> pp_t_cone_lift w r)
        (g \<acute> pp_t_cone_lift w r)"
      using iffD2[OF outputs_at_w root_outputs] .
  qed
qed

end

lemma pp_t_M5_root_fundamental_fun_prime_eqv:
  assumes X_typed:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and Y_typed:
      "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] X"
    and Y_stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] Y"
  shows
    "pp_t_eqv Prop []
        (X \<acute> pp_t_M5_root_fundamental)
        (Y \<acute> pp_t_M5_root_fundamental)
      \<longleftrightarrow>
      pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] X Y"
proof -
  have X_app:
      "Elem (X \<acute> pp_t_M5_root_fundamental) (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF X_typed pp_t_M5_root_fundamental_typed] .
  have Y_app:
      "Elem (Y \<acute> pp_t_M5_root_fundamental) (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF Y_typed pp_t_M5_root_fundamental_typed] .
  have outputs:
      "pp_t_eqv Prop []
          (X \<acute> pp_t_M5_root_fundamental)
          (Y \<acute> pp_t_M5_root_fundamental)
        \<longleftrightarrow>
        X \<acute> pp_t_M5_root_fundamental =
          Y \<acute> pp_t_M5_root_fundamental"
    using pp_t_root_eqv_iff_eq[OF X_app Y_app] .
  have operators:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) [] X Y
        \<longleftrightarrow> X = Y"
    using pp_t_root_eqv_iff_eq[OF X_typed Y_typed] .
  show ?thesis
    using outputs operators
      pp_t_M5_root_fundamental_is_fun_prime[OF X_stock Y_stock]
    by blast
qed

theorem pp_t_M5_fundamental_at_is_fun_prime:
  assumes X_typed:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and Y_typed:
      "Elem Y (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) w X"
    and Y_stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) w Y"
  shows
    "pp_t_eqv Prop w
        (X \<acute> pp_t_M5_fundamental_at w)
        (Y \<acute> pp_t_M5_fundamental_at w)
      \<longleftrightarrow>
      pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w X Y"
  unfolding pp_t_M5_fundamental_at_def
  using M5Rebuilt.pp_t_fun_prime_transports_to_cone[
    OF pp_t_M5_root_fundamental_typed
      pp_t_M5_root_fundamental_fun_prime_eqv
      X_typed Y_typed X_stock Y_stock] .

interpretation M5Full:
  pp_t_seeded_stock
    "pp_t_basis_stock pp_t_M5_rebuilt_basis"
    pp_t_M5_fundamental_at
proof
  fix \<sigma>
  show "pp_t_predicate_admissible \<sigma>
      (pp_t_basis_stock pp_t_M5_rebuilt_basis \<sigma>)"
    by (rule M5Rebuilt.pp_t_basis_stock_admissible)
next
  fix \<sigma> w v x
  assume stock:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis \<sigma> w x"
    and future: "prefix w v"
  show "pp_t_basis_stock pp_t_M5_rebuilt_basis \<sigma> v x"
    using M5Rebuilt.pp_t_basis_stock_persistent[
      OF stock future] .
next
  fix w
  show "Elem (pp_t_M5_fundamental_at w) (pp_t_domain Prop)"
    by (rule pp_t_M5_fundamental_at_typed)
next
  fix w
  show "pp_t_unary_recombines_at
      (pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop))
      (pp_t_M5_fundamental_at w) w"
    by (rule pp_t_M5_fundamental_at_recombines)
next
  fix \<sigma> M \<rho> w
  assume typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  show "pp_t_basis_stock pp_t_M5_rebuilt_basis \<sigma> w
      (pp_t_eval
        (pp_t_seeded_internal_constants
          (pp_t_basis_stock pp_t_M5_rebuilt_basis)
          pp_t_M5_fundamental_at) \<rho> M)"
    using M5Rebuilt.pp_t_basis_stock_contains_eval[
      OF typed logical] .
next
  fix \<sigma> \<tau> w f x
  assume f:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and x:
      "pp_t_basis_stock pp_t_M5_rebuilt_basis \<sigma> w x"
  show "pp_t_basis_stock pp_t_M5_rebuilt_basis
      \<tau> w (f \<acute> x)"
    using M5Rebuilt.pp_t_basis_stock_application_closed[
      OF f x] .
qed

lemmas pp_t_M5_full_rebuilt_background_gvalid =
  M5Full.pp_t_seeded_recombination_background_gvalid

theorem pp_t_M5_full_rebuilt_exotic_certificate:
  "(\<forall>w.
      pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) w pp_t_M5_exotic_den)
    \<and> pp_b_operator_of pp_t_M5_exotic_den = pp_t_M5_exotic
    \<and> (\<forall>P.
      Elem P (pp_t_domain Prop) \<longrightarrow>
      pp_t_M5_exotic_den \<acute>
        (pp_t_M5_exotic_den \<acute> P) = P)
    \<and> \<not> pp_t_M5_truth_preserving pp_t_M5_exotic
    \<and> \<not> pp_t_M5_truth_flipping pp_t_M5_exotic
    \<and> \<not> (\<exists>A.
      pp_t_M5_exotic = pp_t_M5_biconditional_operator A)"
  using pp_t_M5_exotic_pure_in_rebuilt_definable_stock
    pp_t_M5_exotic_den_exact
    pp_t_M5_exotic_den_involution
    pp_t_M5_exotic_not_truth_uniform
    pp_t_M5_exotic_not_biconditional
  by blast

theorem pp_t_M5_existential_nonuniform_invertible_collision_free:
  "\<exists>F.
    bij F
    \<and> \<not> pp_t_M5_truth_preserving F
    \<and> \<not> pp_t_M5_truth_flipping F
    \<and> (\<forall>P Q. F P = F Q \<longrightarrow> P = Q)"
proof (intro exI[of _ pp_t_M5_exotic] conjI)
  show "bij pp_t_M5_exotic"
    by (rule pp_t_M5_exotic_bijective)
  show "\<not> pp_t_M5_truth_preserving pp_t_M5_exotic"
    using pp_t_M5_exotic_not_truth_uniform by blast
  show "\<not> pp_t_M5_truth_flipping pp_t_M5_exotic"
    using pp_t_M5_exotic_not_truth_uniform by blast
  show "\<forall>P Q.
      pp_t_M5_exotic P = pp_t_M5_exotic Q \<longrightarrow> P = Q"
    using pp_t_M5_exotic_bijective
    unfolding bij_def inj_def by blast
qed

text \<open>
  This existential certificate is a counterexample to the unrestricted
  proposed generalization of the collision method.  A non-truth-uniform
  invertible need not have a collision: the displayed M5 operator is such an
  invertible and is injective.  A PP-specific collision argument would
  therefore have to use some further condition imposed on the existential
  witness by PP, rather than existential reversibility or failure of
  truth-uniformity alone.
\<close>

theorem pp_t_M5_full_rebuilt_model:
  "(\<forall>w.
      pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) w pp_t_M5_exotic_den)
    \<and> countable
      (pp_t_M5_rebuilt_basis (Prop \<rightarrow>\<^sub>o Prop))
    \<and> pp_t_unary_recombines_at
      (pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop))
      pp_t_M5_root_fundamental []
    \<and> (\<forall>X Y.
      pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] X \<longrightarrow>
      pp_t_basis_stock pp_t_M5_rebuilt_basis
        (Prop \<rightarrow>\<^sub>o Prop) [] Y \<longrightarrow>
      ((X \<acute> pp_t_M5_root_fundamental =
          Y \<acute> pp_t_M5_root_fundamental)
        \<longleftrightarrow> X = Y))"
  using pp_t_M5_exotic_pure_in_rebuilt_definable_stock
    pp_t_M5_rebuilt_basis_countable
    pp_t_M5_root_fundamental_recombines
    pp_t_M5_root_fundamental_is_fun_prime by blast

text \<open>
  Thus there is a complete typed Henkin interpretation of Bacon's
  Recombination background whose pure stock is the least applicatively
  generated stock containing the closed logical denotations and the displayed
  exotic operator.  The operator is an exact member of the modalized unary
  function domain, commutes with every cone view, swaps the displayed pair,
  and fixes truth and falsity.  The same chosen fundamental proposition both
  supplies Recombination and separates the pure unary operators at every
  world, which is the model-theoretic content of QSS for this stock.

  This theorem does not assert PP for the rebuilt stock.  In the basis-stock
  semantics, PP is the further fixed-point condition that the classifier of
  the unary pure stock itself belongs to the next pure stock.
\<close>

end
