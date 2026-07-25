theory Bacon_PP_Diagonal_Reduction
  imports Bacon_PP_Stock_Requirements
begin

section \<open>Reducing the escape requirement to a diagonal set\<close>

text \<open>
  The requirement set of \<open>Bacon_PP_Stock_Requirements\<close> asks, for each family in the
  stock, either two separating propositions or one proposition escaping the index of
  its constant value.  The index of the value is exactly the quantity whose
  seed-independence is in doubt, so it is worth asking how much of it the requirement
  really needs.

  The answer is: only the diagonal.  For an equivariant binary family \<open>Y\<close> put

  \begin{center}
  \<open>D\<^sub>Y = {b. Y b b is true at the root}\<close>.
  \end{center}

  Two facts hold.  First, the diagonal of an equivariant family is always a
  classifier, \<open>Y b b = pp_classifier D\<^sub>Y b\<close>.  Second --- and this is the useful one ---
  when \<open>Y r\<close> is pure, so that \<open>Y\<close> is constant along the orbit of \<open>r\<close>, the orbit
  sits inside the index of \<open>Y r\<close> exactly when it sits inside \<open>D\<^sub>Y\<close>.

  So the escape requirement can be posed against \<open>D\<^sub>Y\<close> instead of against
  \<open>pp_operator_index (Y r)\<close>.  That is a genuine reduction of the uniformity burden:
  \<open>D\<^sub>Y\<close> is a function of the family alone, it does not mention the seed, and it is
  obtained from \<open>Y\<close> by a single root-truth test rather than by evaluating \<open>Y\<close> at the
  seed.  It also shrinks the construction: one required proposition per family instead
  of three, and no case analysis on constancy, except in the one degenerate situation
  where the diagonal is universal.
\<close>

subsection \<open>The diagonal set\<close>

definition pp_diagonal_set ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop set"
  where
  "pp_diagonal_set Y = {b. pp_root_true (Y b b)}"

lemma pp_diagonal_set_iff:
  "b \<in> pp_diagonal_set Y \<longleftrightarrow> pp_root_true (Y b b)"
  by (simp add: pp_diagonal_set_def)

theorem pp_equivariant_diagonal_is_classifier:
  assumes family: "pp_equivariant_binary_family Y"
  shows "Y b b = pp_classifier (pp_diagonal_set Y) b"
proof (rule set_eqI)
  fix i
  have action: "pp_view i (Y b b) = Y (pp_view i b) (pp_view i b)"
    using family unfolding pp_equivariant_binary_family_def by blast
  have "i \<in> Y b b \<longleftrightarrow> pp_root_true (pp_view i (Y b b))"
    by (simp add: pp_root_true_def pp_view_membership_at_root)
  also have "... \<longleftrightarrow>
      pp_root_true (Y (pp_view i b) (pp_view i b))"
    using action by simp
  also have "... \<longleftrightarrow> pp_view i b \<in> pp_diagonal_set Y"
    by (simp add: pp_diagonal_set_iff)
  also have "... \<longleftrightarrow> i \<in> pp_classifier (pp_diagonal_set Y) b"
    by (simp add: pp_classifier_def)
  finally show
      "i \<in> Y b b \<longleftrightarrow> i \<in> pp_classifier (pp_diagonal_set Y) b" .
qed

subsection \<open>The reduction\<close>

theorem pp_orbit_index_iff_diagonal:
  assumes stable: "pp_parameter_orbit_stable Y r"
  shows "pp_orbit r \<subseteq> pp_operator_index (Y r) \<longleftrightarrow>
    pp_orbit r \<subseteq> pp_diagonal_set Y"
proof -
  have shift: "Y (pp_view i r) = Y r" for i
    using stable unfolding pp_parameter_orbit_stable_def by blast
  have pointwise:
      "(pp_view i r \<in> pp_operator_index (Y r)) =
       (pp_view i r \<in> pp_diagonal_set Y)" for i
  proof -
    have "pp_view i r \<in> pp_operator_index (Y r) \<longleftrightarrow>
        pp_root_true (Y r (pp_view i r))"
      by (simp add: pp_operator_index_def)
    also have "... \<longleftrightarrow>
        pp_root_true (Y (pp_view i r) (pp_view i r))"
      using shift[of i] by simp
    also have "... \<longleftrightarrow> pp_view i r \<in> pp_diagonal_set Y"
      by (simp add: pp_diagonal_set_iff)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding pp_orbit_def using pointwise by auto
qed

text \<open>
  The degenerate case.  If the family is constant then its diagonal set simply is the
  index of its value, so a universal diagonal forces a universal index and the QLN
  biconditional holds for free.
\<close>

lemma pp_constant_family_diagonal:
  assumes "pp_family_constant Y"
  shows "pp_diagonal_set Y = pp_operator_index (Y r)"
proof (rule set_eqI)
  fix b
  have "Y b = Y r"
    using assms unfolding pp_family_constant_def by blast
  then have "pp_root_true (Y b b) = pp_root_true (Y r b)"
    by simp
  then show "b \<in> pp_diagonal_set Y \<longleftrightarrow> b \<in> pp_operator_index (Y r)"
    by (simp add: pp_diagonal_set_iff pp_operator_index_def)
qed

subsection \<open>The refined requirement set\<close>

text \<open>
  One proposition per family in the main case.  Separators are needed only for a
  family whose diagonal is universal and which is not constant; a constant family with
  universal diagonal has a universal index by the lemma above, and needs nothing.
\<close>

definition pp_diagonal_required_of ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop set"
  where
  "pp_diagonal_required_of Y =
    (if pp_diagonal_set Y \<noteq> UNIV
     then {pp_escape (pp_diagonal_set Y)}
     else if \<not> pp_family_constant Y
     then {pp_sep0 Y, pp_sep1 Y}
     else {})"

lemma pp_diagonal_required_of_countable:
  "countable (pp_diagonal_required_of Y)"
  by (simp add: pp_diagonal_required_of_def)

lemma pp_diagonal_required_escape:
  assumes "pp_diagonal_set Y \<noteq> UNIV"
  shows "pp_escape (pp_diagonal_set Y) \<in> pp_diagonal_required_of Y"
  using assms by (simp add: pp_diagonal_required_of_def)

lemma pp_diagonal_required_sep0:
  assumes "pp_diagonal_set Y = UNIV"
    and "\<not> pp_family_constant Y"
  shows "pp_sep0 Y \<in> pp_diagonal_required_of Y"
  using assms by (simp add: pp_diagonal_required_of_def)

lemma pp_diagonal_required_sep1:
  assumes "pp_diagonal_set Y = UNIV"
    and "\<not> pp_family_constant Y"
  shows "pp_sep1 Y \<in> pp_diagonal_required_of Y"
  using assms by (simp add: pp_diagonal_required_of_def)

subsection \<open>The refined witness theorem\<close>

theorem pp_diagonal_stock_witness:
  fixes Fam ::
    "pp_sem_prop \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and A :: "pp_sem_prop set"
  assumes countable: "countable A"
    and equivariant:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_equivariant_binary_family Y"
    and cover:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_diagonal_required_of Y \<subseteq> A"
  shows "\<exists>r. pp_img r = r \<and>
    (\<forall>Y \<in> Fam r. pp_fun_invariant (Y r) \<longrightarrow>
       pp_root_unary_QLN_operator (Y r) r)"
proof -
  obtain r where symmetric: "pp_img r = r"
    and contained: "A \<subseteq> pp_orbit r"
    using pp_prescribed_orbit_witness[OF countable] by blast
  have main: "pp_root_unary_QLN_operator (Y r) r"
      if Y_fam: "Y \<in> Fam r" and invariant: "pp_fun_invariant (Y r)"
      for Y
  proof -
    have family: "pp_equivariant_binary_family Y"
      using Y_fam by (rule equivariant)
    have required: "pp_diagonal_required_of Y \<subseteq> pp_orbit r"
      using cover[OF Y_fam] contained by blast
    have member: "pp_function_space_member (Y r)"
      using family by (rule pp_equivariant_binary_family_member)
    have stable: "pp_parameter_orbit_stable Y r"
      using pp_binary_family_invariant_iff_parameter_orbit_stable[
          OF family, of r] invariant
      by blast
    have reduction:
        "pp_orbit r \<subseteq> pp_operator_index (Y r) \<longleftrightarrow>
         pp_orbit r \<subseteq> pp_diagonal_set Y"
      using stable by (rule pp_orbit_index_iff_diagonal)
    have escape_condition:
        "(pp_orbit r \<subseteq> pp_operator_index (Y r)) =
         (pp_operator_index (Y r) = UNIV)"
    proof (cases "pp_diagonal_set Y = UNIV")
      case False
      have in_orbit: "pp_escape (pp_diagonal_set Y) \<in> pp_orbit r"
        using pp_diagonal_required_escape[OF False] required by blast
      have "pp_escape (pp_diagonal_set Y) \<notin> pp_diagonal_set Y"
        using False by (rule pp_escape_notin)
      then have not_inside: "\<not> pp_orbit r \<subseteq> pp_diagonal_set Y"
        using in_orbit by blast
      then have not_index: "\<not> pp_orbit r \<subseteq> pp_operator_index (Y r)"
        using reduction by blast
      then have "pp_operator_index (Y r) \<noteq> UNIV"
        by blast
      then show ?thesis using not_index by simp
    next
      case True
      show ?thesis
      proof (cases "pp_family_constant Y")
        case True
        then have "pp_diagonal_set Y = pp_operator_index (Y r)"
          by (rule pp_constant_family_diagonal)
        then have "pp_operator_index (Y r) = UNIV"
          using \<open>pp_diagonal_set Y = UNIV\<close> by simp
        then show ?thesis by simp
      next
        case False
        have b: "pp_sep0 Y \<in> pp_orbit r"
          using pp_diagonal_required_sep0[OF \<open>pp_diagonal_set Y = UNIV\<close> False]
            required by blast
        have c: "pp_sep1 Y \<in> pp_orbit r"
          using pp_diagonal_required_sep1[OF \<open>pp_diagonal_set Y = UNIV\<close> False]
            required by blast
        have "\<not> pp_fun_invariant (Y r)"
          using family False b c
          by (rule pp_nonconstant_family_not_invariant)
        then show ?thesis using invariant by simp
      qed
    qed
    show ?thesis
      using pp_invariant_operator_QLN_iff_orbit_escape[
          OF member invariant, of r]
        escape_condition
      by blast
  qed
  show ?thesis
    using symmetric main by blast
qed

corollary pp_diagonal_envelope_witness:
  fixes Fam ::
    "pp_sem_prop \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and Fam0 :: "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Fam0"
    and envelope: "\<And>s. Fam s \<subseteq> Fam0"
    and equivariant:
      "\<And>Y. Y \<in> Fam0 \<Longrightarrow> pp_equivariant_binary_family Y"
  shows "\<exists>r. pp_img r = r \<and>
    (\<forall>Y \<in> Fam r. pp_fun_invariant (Y r) \<longrightarrow>
       pp_root_unary_QLN_operator (Y r) r)"
proof -
  let ?A = "(\<Union>Y \<in> Fam0. pp_diagonal_required_of Y)"
  have countable_A: "countable ?A"
  proof (rule countable_UN)
    show "countable Fam0" by (rule countable)
  next
    fix Y
    assume "Y \<in> Fam0"
    show "countable (pp_diagonal_required_of Y)"
      by (rule pp_diagonal_required_of_countable)
  qed
  have equivariant': "\<And>s Y. Y \<in> Fam s \<Longrightarrow>
      pp_equivariant_binary_family Y"
    using envelope equivariant by blast
  have cover: "\<And>s Y. Y \<in> Fam s \<Longrightarrow>
      pp_diagonal_required_of Y \<subseteq> ?A"
    using envelope by blast
  show ?thesis
    by (rule pp_diagonal_stock_witness[
        OF countable_A equivariant' cover])
qed

subsection \<open>What this buys, and what it does not\<close>

text \<open>
  The uniformity burden has been reduced but not discharged.  What must now be uniform
  in the seed is the family of diagonal sets \<open>D\<^sub>Y\<close>, not the family of indices
  \<open>pp_operator_index (Y r)\<close>, and the requirement is one proposition per family rather
  than three.  The diagonal set is also a strictly simpler object: by
  \<open>pp_equivariant_diagonal_is_classifier\<close> it is precisely the index of the classifier
  that the diagonal of \<open>Y\<close> already is.

  This does not settle the question, because \<open>D\<^sub>Y\<close> is still computed from \<open>Y\<close>, and
  \<open>Y\<close> is still the denotation of a term whose quantifiers range over seed-generated
  domains.  A term such as \<open>\<lambda>b. \<lambda>c. \<forall>X. (X \<longrightarrow> c)\<close> has a value that moves when the
  domain at \<open>Prop\<close> moves, and its diagonal moves with it.  So the envelope hypothesis
  remains a hypothesis, and it is very likely false in its literal form: the syntax is
  countable but there are continuum-many seeds, so the union of the family sets over
  all seeds has no reason to be countable.

  The honest reading is therefore that the remaining problem is not to prove the
  envelope condition, which is probably false, but to replace it: either by
  constructing Henkin domains that do not depend on the seed at all, or by a genuine
  fixed-point argument on the map from seeds to diagonal requirements.  The reduction
  above is what makes the second option tractable to state, since the map now lands in
  sets of propositions rather than in indices of seed-evaluated operators.
\<close>

end
