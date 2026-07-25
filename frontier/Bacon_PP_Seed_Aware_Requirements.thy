theory Bacon_PP_Seed_Aware_Requirements
  imports Bacon_PP_Seed_Nontriviality
begin

section \<open>Requirements imposed only where they are needed\<close>

text \<open>
  The requirement sets of the previous theories are imposed on every family in the
  stock, whether or not that family causes any trouble at its own seed.  That is
  wasteful, and the waste is not harmless: it inflates the set of propositions that a
  uniformity hypothesis has to cover, and it can demand escapes that are impossible
  to supply.

  The sharpest instance is the membership-testing term
  \<open>\<lambda>b. \<lambda>c. \<exists>X : Prop. Id(X, b)\<close>.  Its diagonal set is the whole proposition domain
  of the seed, so the diagonal is proper and the previous requirement demands a
  proposition escaping the domain.  But the value of that family at its own seed is
  universally root-true --- the seed does belong to its own domain --- so its index is
  \<open>UNIV\<close> and it satisfies QLN outright.  The requirement was spurious.

  This theory therefore guards every requirement by the condition under which it is
  actually needed: the value at the seed is pure and its index is proper.  Everything
  else is dropped.  The resulting cover is the weakest of the three, and it is the
  right target for any later uniformity or fixed-point argument.
\<close>

subsection \<open>The guarded requirement set\<close>

definition pp_seed_aware_required_of ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop set"
  where
  "pp_seed_aware_required_of Y s =
    (if pp_fun_invariant (Y s) \<and>
        pp_operator_index (Y s) \<noteq> UNIV
     then (if pp_diagonal_set Y \<noteq> UNIV
           then {pp_escape (pp_diagonal_set Y)}
           else {pp_sep0 Y, pp_sep1 Y})
     else {})"

lemma pp_seed_aware_required_of_countable:
  "countable (pp_seed_aware_required_of Y s)"
  by (simp add: pp_seed_aware_required_of_def)

lemma pp_seed_aware_required_of_trivial:
  assumes "\<not> pp_fun_invariant (Y s) \<or>
    pp_operator_index (Y s) = UNIV"
  shows "pp_seed_aware_required_of Y s = {}"
  using assms by (auto simp: pp_seed_aware_required_of_def)

lemma pp_seed_aware_escape:
  assumes needed: "pp_fun_invariant (Y s)"
    and proper: "pp_operator_index (Y s) \<noteq> UNIV"
    and diagonal: "pp_diagonal_set Y \<noteq> UNIV"
  shows "pp_escape (pp_diagonal_set Y) \<in>
    pp_seed_aware_required_of Y s"
  using assms by (simp add: pp_seed_aware_required_of_def)

lemma pp_seed_aware_sep0:
  assumes needed: "pp_fun_invariant (Y s)"
    and proper: "pp_operator_index (Y s) \<noteq> UNIV"
    and diagonal: "pp_diagonal_set Y = UNIV"
  shows "pp_sep0 Y \<in> pp_seed_aware_required_of Y s"
  using assms by (simp add: pp_seed_aware_required_of_def)

lemma pp_seed_aware_sep1:
  assumes needed: "pp_fun_invariant (Y s)"
    and proper: "pp_operator_index (Y s) \<noteq> UNIV"
    and diagonal: "pp_diagonal_set Y = UNIV"
  shows "pp_sep1 Y \<in> pp_seed_aware_required_of Y s"
  using assms by (simp add: pp_seed_aware_required_of_def)

subsection \<open>The seed-aware witness theorem\<close>

theorem pp_seed_aware_diagonal_stock_witness:
  fixes Fam ::
    "pp_sem_prop \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and A :: "pp_sem_prop set"
  assumes countable: "countable A"
    and equivariant:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_equivariant_binary_family Y"
    and cover:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow>
        pp_seed_aware_required_of Y s \<subseteq> A"
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
    have required: "pp_seed_aware_required_of Y r \<subseteq> pp_orbit r"
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
    proof (cases "pp_operator_index (Y r) = UNIV")
      case True
      then show ?thesis by simp
    next
      case proper: False
      show ?thesis
      proof (cases "pp_diagonal_set Y = UNIV")
        case False
        have in_orbit: "pp_escape (pp_diagonal_set Y) \<in> pp_orbit r"
          using pp_seed_aware_escape[OF invariant proper False] required
          by blast
        have "pp_escape (pp_diagonal_set Y) \<notin> pp_diagonal_set Y"
          using False by (rule pp_escape_notin)
        then have "\<not> pp_orbit r \<subseteq> pp_diagonal_set Y"
          using in_orbit by blast
        then have "\<not> pp_orbit r \<subseteq> pp_operator_index (Y r)"
          using reduction by blast
        then show ?thesis using proper by simp
      next
        case universal: True
        have nonconstant: "\<not> pp_family_constant Y"
        proof
          assume "pp_family_constant Y"
          then have "pp_diagonal_set Y = pp_operator_index (Y r)"
            by (rule pp_constant_family_diagonal)
          then show False using universal proper by simp
        qed
        have b: "pp_sep0 Y \<in> pp_orbit r"
          using pp_seed_aware_sep0[OF invariant proper universal] required
          by blast
        have c: "pp_sep1 Y \<in> pp_orbit r"
          using pp_seed_aware_sep1[OF invariant proper universal] required
          by blast
        have "\<not> pp_fun_invariant (Y r)"
          using family nonconstant b c
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

subsection \<open>The guarded cover is the weakest of the three\<close>

lemma pp_seed_aware_below_diagonal:
  "pp_seed_aware_required_of Y s \<subseteq> pp_diagonal_required_of Y"
proof (cases "pp_fun_invariant (Y s) \<and>
    pp_operator_index (Y s) \<noteq> UNIV")
  case False
  then have "pp_seed_aware_required_of Y s = {}"
    by (auto simp: pp_seed_aware_required_of_def)
  then show ?thesis by simp
next
  case guard: True
  then have proper: "pp_operator_index (Y s) \<noteq> UNIV" by simp
  show ?thesis
  proof (cases "pp_diagonal_set Y = UNIV")
    case False
    then show ?thesis
      using guard
      by (simp add: pp_seed_aware_required_of_def
          pp_diagonal_required_of_def)
  next
    case universal: True
    have nonconstant: "\<not> pp_family_constant Y"
    proof
      assume "pp_family_constant Y"
      then have "pp_diagonal_set Y = pp_operator_index (Y s)"
        by (rule pp_constant_family_diagonal)
      then show False using universal proper by simp
    qed
    show ?thesis
      using guard universal nonconstant
      by (simp add: pp_seed_aware_required_of_def
          pp_diagonal_required_of_def)
  qed
qed

corollary pp_diagonal_cover_gives_seed_aware_cover:
  assumes "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_diagonal_required_of Y \<subseteq> A"
    and "Y \<in> Fam s"
  shows "pp_seed_aware_required_of Y s \<subseteq> A"
  using assms pp_seed_aware_below_diagonal by blast

text \<open>
  So any of the three uniformity hypotheses suffices, and the guarded one is the
  weakest.  In particular the membership-testing family described at the head of this
  theory contributes nothing to the guarded cover, because its value at its own seed
  has universal index.
\<close>

end
