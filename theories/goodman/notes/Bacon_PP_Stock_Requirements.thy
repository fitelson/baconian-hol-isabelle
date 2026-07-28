theory Bacon_PP_Stock_Requirements
  imports
    "Higher_Order_Metaphysics_PP.Bacon_PP_Symmetric_Witness"
    "Higher_Order_Metaphysics_PP.Bacon_PP_Orbit_Stability"
begin

section \<open>Simultaneous requirements for a self-classifying stock\<close>

text \<open>
  This theory begins the construction of a countable, orbit-generic, self-classifying
  stock.  The starting point is the observation that the circularity described in
  \<open>STATUS.md\<close> --- that the stock of Pure-free denotations depends on the very witness
  it is supposed to constrain --- is weaker than it looks, and that a large part of it
  can be removed by a single simultaneous-requirement construction with no priority
  ordering and no injury.

  The reduction runs as follows.  Every element of the term-generated domain at type
  \<open>t \<rightarrow> t\<close> over the seed \<open>r\<close> has the form \<open>Y r\<close> for an equivariant binary family
  \<open>Y\<close> in which \<open>r\<close> occurs only as the argument; abstracting the seed out turns the
  fundamentality predicate \<open>Fun\<close> into \<open>\<lambda>x. \<lambda>P. Id(P, x)\<close>, and \<open>Pure\<close> is
  interpreted by \<open>pp_purity_operator\<close>, which is parameter-free and equivariant.

  \<open>Bacon_PP_Orbit_Stability\<close> already proves that \<open>Y r\<close> is invariant exactly when
  \<open>Y\<close> is constant on the orbit of \<open>r\<close>.  So if the witness is built so that every
  \emph{non-constant} family in the stock takes two different values on the orbit,
  then every \emph{invariant} value in the stock comes from a globally constant family
  and is therefore parameter-free.  Its classifier index is then a fixed set, and the
  ordinary generic-witness requirement applies to it.

  Both kinds of requirement are met by placing prescribed propositions at reserved
  cones, and the paired-cone construction of \<open>Bacon_PP_Symmetric_Witness\<close> supplies
  countably many independent cones while keeping the witness tree-symmetric.  Hence
  the requirements do not interact and no priority ordering is needed.

  What this does \emph{not} yet remove is the dependence of the family set itself on
  \<open>r\<close> through the object-language quantifier domains.  That residue is recorded at
  the end of the theory.
\<close>

subsection \<open>Choice functions for the two kinds of requirement\<close>

definition pp_escape :: "pp_sem_prop set \<Rightarrow> pp_sem_prop" where
  "pp_escape S = (SOME P. P \<notin> S)"

lemma pp_escape_notin:
  assumes "S \<noteq> UNIV"
  shows "pp_escape S \<notin> S"
proof -
  have "\<exists>P. P \<notin> S" using assms by blast
  then show ?thesis
    unfolding pp_escape_def by (rule someI_ex)
qed

definition pp_family_constant ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_family_constant Y \<longleftrightarrow> (\<forall>b c. Y b = Y c)"

definition pp_sep0 ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_sep0 Y = (SOME b. \<exists>c. Y b \<noteq> Y c)"

definition pp_sep1 ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_sep1 Y = (SOME c. Y (pp_sep0 Y) \<noteq> Y c)"

lemma pp_sep_separates:
  assumes "\<not> pp_family_constant Y"
  shows "Y (pp_sep0 Y) \<noteq> Y (pp_sep1 Y)"
proof -
  have "\<exists>b. \<exists>c. Y b \<noteq> Y c"
    using assms unfolding pp_family_constant_def by blast
  then have first: "\<exists>c. Y (pp_sep0 Y) \<noteq> Y c"
    unfolding pp_sep0_def by (rule someI_ex)
  then show ?thesis
    unfolding pp_sep1_def by (rule someI_ex)
qed

subsection \<open>The orbit of a paired witness contains a prescribed countable set\<close>

lemma pp_paired_witness_orbit:
  "q n \<in> pp_orbit (pp_paired_witness q)"
  unfolding pp_orbit_def
  using pp_view_paired_witness[of n q]
  by (intro range_eqI[where x = "pp_cone_a n"]) simp

theorem pp_prescribed_orbit_witness:
  fixes A :: "pp_sem_prop set"
  assumes countable: "countable A"
  shows "\<exists>r. pp_img r = r \<and> A \<subseteq> pp_orbit r"
proof -
  let ?A = "insert {} A"
  have nonempty: "?A \<noteq> {}" by simp
  have countable': "countable ?A"
    using countable by simp
  let ?q = "from_nat_into ?A"
  have range_q: "range ?q = ?A"
    using nonempty countable' by (rule range_from_nat_into)
  let ?r = "pp_paired_witness ?q"
  have symmetric: "pp_img ?r = ?r"
    by (rule pp_paired_witness_symmetric)
  have contained: "?A \<subseteq> pp_orbit ?r"
  proof
    fix P
    assume P_mem: "P \<in> ?A"
    have "P \<in> range ?q"
      using P_mem range_q by simp
    then obtain n where n: "?q n = P"
      by auto
    have "?q n \<in> pp_orbit ?r"
      by (rule pp_paired_witness_orbit)
    then show "P \<in> pp_orbit ?r"
      using n by simp
  qed
  show ?thesis
    using symmetric contained by blast
qed

subsection \<open>Non-constant families lose invariance at a generic witness\<close>

lemma pp_parameter_orbit_stable_constant_on_orbit:
  assumes stable: "pp_parameter_orbit_stable Y r"
    and mem: "b \<in> pp_orbit r"
  shows "Y b = Y r"
proof -
  obtain i where "b = pp_view i r"
    using mem unfolding pp_orbit_def by blast
  then show ?thesis
    using stable unfolding pp_parameter_orbit_stable_def by simp
qed

theorem pp_two_orbit_values_defeat_stability:
  assumes b: "b \<in> pp_orbit r"
    and c: "c \<in> pp_orbit r"
    and different: "Y b \<noteq> Y c"
  shows "\<not> pp_parameter_orbit_stable Y r"
proof
  assume stable: "pp_parameter_orbit_stable Y r"
  have "Y b = Y r"
    using stable b by (rule pp_parameter_orbit_stable_constant_on_orbit)
  moreover have "Y c = Y r"
    using stable c by (rule pp_parameter_orbit_stable_constant_on_orbit)
  ultimately show False using different by simp
qed

corollary pp_nonconstant_family_not_invariant:
  assumes family: "pp_equivariant_binary_family Y"
    and separated: "\<not> pp_family_constant Y"
    and b: "pp_sep0 Y \<in> pp_orbit r"
    and c: "pp_sep1 Y \<in> pp_orbit r"
  shows "\<not> pp_fun_invariant (Y r)"
proof -
  have "\<not> pp_parameter_orbit_stable Y r"
    using b c pp_sep_separates[OF separated]
    by (rule pp_two_orbit_values_defeat_stability)
  then show ?thesis
    using pp_binary_family_invariant_iff_parameter_orbit_stable[
        OF family, of r]
    by blast
qed

subsection \<open>Constant families have a parameter-free index\<close>

lemma pp_family_constant_value:
  assumes "pp_family_constant Y"
  shows "Y b = Y {}"
  using assms unfolding pp_family_constant_def by blast

lemma pp_family_constant_index:
  assumes "pp_family_constant Y"
  shows "pp_operator_index (Y b) = pp_operator_index (Y {})"
proof -
  have "Y b = Y {}"
    using assms unfolding pp_family_constant_def by blast
  then show ?thesis by simp
qed

subsection \<open>The simultaneous-requirement theorem\<close>

text \<open>
  The requirement set.  For every family in the stock we need one proposition escaping
  the index of its constant value, when that index is proper, and for every
  non-constant family we need the two propositions separating it.  All of them are
  placed in the orbit at once.
\<close>

definition pp_stock_requirements ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow> pp_sem_prop set"
  where
  "pp_stock_requirements Fam =
    (\<lambda>Y. pp_escape (pp_operator_index (Y {}))) ` Fam \<union>
    pp_sep0 ` Fam \<union> pp_sep1 ` Fam"

lemma pp_stock_requirements_countable:
  assumes "countable Fam"
  shows "countable (pp_stock_requirements Fam)"
  unfolding pp_stock_requirements_def
  using assms by (intro countable_Un countable_image)

theorem pp_stock_requirement_witness:
  fixes Fam :: "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Fam"
  shows "\<exists>r. pp_img r = r \<and>
    pp_stock_requirements Fam \<subseteq> pp_orbit r"
  using pp_prescribed_orbit_witness[
      OF pp_stock_requirements_countable[OF countable]] .

text \<open>
  The main theorem of this theory.  For every countable set of equivariant families
  there is a tree-symmetric witness at which every invariant value of the stock is
  parameter-free and satisfies unary QLN.  In particular the pure part of the stock is
  completely independent of the witness, which is what removes the circularity.
\<close>

theorem pp_countable_family_stock_has_generic_witness:
  fixes Fam :: "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Fam"
    and equivariant:
      "\<And>Y. Y \<in> Fam \<Longrightarrow> pp_equivariant_binary_family Y"
  shows "\<exists>r. pp_img r = r \<and>
    (\<forall>Y \<in> Fam. pp_fun_invariant (Y r) \<longrightarrow>
       ((\<forall>b. Y b = Y r) \<and>
        pp_root_unary_QLN_operator (Y r) r))"
proof -
  obtain r where symmetric: "pp_img r = r"
    and requirements: "pp_stock_requirements Fam \<subseteq> pp_orbit r"
    using pp_stock_requirement_witness[OF countable] by blast
  have sep0: "pp_sep0 Y \<in> pp_orbit r" if "Y \<in> Fam" for Y
  proof -
    have "pp_sep0 Y \<in> pp_stock_requirements Fam"
      using that unfolding pp_stock_requirements_def by simp
    then show ?thesis using requirements by blast
  qed
  have sep1: "pp_sep1 Y \<in> pp_orbit r" if "Y \<in> Fam" for Y
  proof -
    have "pp_sep1 Y \<in> pp_stock_requirements Fam"
      using that unfolding pp_stock_requirements_def by simp
    then show ?thesis using requirements by blast
  qed
  have escaper:
      "pp_escape (pp_operator_index (Y {})) \<in> pp_orbit r"
      if "Y \<in> Fam" for Y
  proof -
    have "pp_escape (pp_operator_index (Y {}))
        \<in> pp_stock_requirements Fam"
      using that unfolding pp_stock_requirements_def by simp
    then show ?thesis using requirements by blast
  qed
  have main:
      "(\<forall>b. Y b = Y r) \<and> pp_root_unary_QLN_operator (Y r) r"
      if Y_fam: "Y \<in> Fam" and invariant: "pp_fun_invariant (Y r)"
      for Y
  proof -
    have family: "pp_equivariant_binary_family Y"
      using Y_fam by (rule equivariant)
    have is_constant: "pp_family_constant Y"
    proof (rule ccontr)
      assume nonconstant: "\<not> pp_family_constant Y"
      have "\<not> pp_fun_invariant (Y r)"
        using family nonconstant sep0[OF Y_fam] sep1[OF Y_fam]
        by (rule pp_nonconstant_family_not_invariant)
      then show False using invariant by simp
    qed
    have all_values: "\<forall>b. Y b = Y r"
      using is_constant unfolding pp_family_constant_def by blast
    have index_fixed:
        "pp_operator_index (Y r) = pp_operator_index (Y {})"
      using is_constant by (rule pp_family_constant_index)
    have member: "pp_function_space_member (Y r)"
      using family by (rule pp_equivariant_binary_family_member)
    have escape_condition:
        "(pp_orbit r \<subseteq> pp_operator_index (Y r)) =
         (pp_operator_index (Y r) = UNIV)"
    proof (cases "pp_operator_index (Y r) = UNIV")
      case True
      then show ?thesis by simp
    next
      case False
      then have proper: "pp_operator_index (Y {}) \<noteq> UNIV"
        using index_fixed by simp
      have "pp_escape (pp_operator_index (Y {}))
          \<notin> pp_operator_index (Y {})"
        using proper by (rule pp_escape_notin)
      then have "\<not> pp_orbit r \<subseteq> pp_operator_index (Y r)"
        using escaper[OF Y_fam] index_fixed by blast
      then show ?thesis using False by simp
    qed
    have qln: "pp_root_unary_QLN_operator (Y r) r"
      using pp_invariant_operator_QLN_iff_orbit_escape[
          OF member invariant, of r]
        escape_condition
      by blast
    show ?thesis using all_values qln by blast
  qed
  show ?thesis
    using symmetric main by blast
qed

subsection \<open>Sanity check: fundamentality is not pure at such a witness\<close>

text \<open>
  \<open>Fun\<close> is the local identity predicate for the fundamental proposition, so it is the
  value at \<open>r\<close> of the family \<open>pp_operator_equal\<close>.  That family is equivariant and
  non-constant, so at any witness meeting its separation requirement \<open>Fun\<close> is not
  pure.  This is exactly right: Purity of Fun is the principle the present question
  deliberately does not assume, and a construction that made it come out true for free
  would be answering the wrong question.
\<close>

lemma pp_operator_equal_family:
  "pp_equivariant_binary_family pp_operator_equal"
  unfolding pp_equivariant_binary_family_def
proof (intro allI)
  fix i b c
  show "pp_view i (pp_operator_equal b c) =
      pp_operator_equal (pp_view i b) (pp_view i c)"
  proof (rule set_eqI)
    fix j
    have "j \<in> pp_view i (pp_operator_equal b c) \<longleftrightarrow>
        pp_view (j @ i) b = pp_view (j @ i) c"
      by (simp add: pp_view_def pp_operator_equal_def)
    also have "... \<longleftrightarrow>
        pp_view j (pp_view i b) = pp_view j (pp_view i c)"
      by (simp add: pp_view_compose)
    also have "... \<longleftrightarrow>
        j \<in> pp_operator_equal (pp_view i b) (pp_view i c)"
      by (simp add: pp_operator_equal_def)
    finally show
        "j \<in> pp_view i (pp_operator_equal b c) \<longleftrightarrow>
         j \<in> pp_operator_equal (pp_view i b) (pp_view i c)" .
  qed
qed

lemma pp_operator_equal_not_constant:
  "\<not> pp_family_constant pp_operator_equal"
proof
  assume "pp_family_constant pp_operator_equal"
  then have "pp_operator_equal {} = pp_operator_equal UNIV"
    unfolding pp_family_constant_def by blast
  then have "pp_operator_equal {} {} = pp_operator_equal UNIV {}"
    by simp
  moreover have "[] \<in> pp_operator_equal {} ({} :: pp_sem_prop)"
    by (simp add: pp_operator_equal_def)
  moreover have
      "[] \<notin> pp_operator_equal UNIV ({} :: pp_sem_prop)"
    by (simp add: pp_operator_equal_def pp_view_def)
  ultimately show False by simp
qed

theorem pp_fundamentality_not_pure_at_generic_witness:
  assumes b: "pp_sep0 pp_operator_equal \<in> pp_orbit r"
    and c: "pp_sep1 pp_operator_equal \<in> pp_orbit r"
  shows "\<not> pp_fun_invariant (pp_operator_equal r)"
  using pp_operator_equal_family pp_operator_equal_not_constant b c
  by (rule pp_nonconstant_family_not_invariant)

corollary pp_fundamentality_not_pure_when_required:
  assumes "pp_operator_equal \<in> Fam"
    and "pp_stock_requirements Fam \<subseteq> pp_orbit r"
  shows "\<not> pp_fun_invariant (pp_operator_equal r)"
proof -
  have "pp_sep0 pp_operator_equal \<in> pp_orbit r"
    using assms unfolding pp_stock_requirements_def by blast
  moreover have "pp_sep1 pp_operator_equal \<in> pp_orbit r"
    using assms unfolding pp_stock_requirements_def by blast
  ultimately show ?thesis
    by (rule pp_fundamentality_not_pure_at_generic_witness)
qed

subsection \<open>The seed-dependent case, and the exact residual hypothesis\<close>

text \<open>
  The theorem above assumes a fixed countable set \<open>Fam\<close>.  In the intended application
  \<open>Fam\<close> is the set of denotations of closed terms of type \<open>t \<rightarrow> (t \<rightarrow> t)\<close> in the
  object language with \<open>Pure\<close> and with the seed abstracted out of \<open>Fun\<close>.  Two of the
  three sources of dependence on the witness are thereby removed outright: \<open>Fun\<close>
  because its seed has been abstracted, and \<open>Pure\<close> because \<open>pp_purity_operator\<close> is
  parameter-free.

  The residue is the object-language quantifiers.  Their domains are the Henkin
  domains, which are generated from the seed, so strictly \<open>Fam\<close> is \<open>Fam r\<close>.  This
  residue is not cosmetic, and in particular it is not repaired by the separation
  requirements above.  Consider a family of the shape
  \<open>Y b P = \<forall>X \<in> D. \<Psi> X P\<close>, in which the parameter \<open>b\<close> does not occur.  Such a
  family is constant, so the separation requirements never touch it, yet its index
  \<open>{P. \<forall>X \<in> D. \<Psi> X P}\<close> moves when \<open>D\<close> moves.  Hence \<open>pp_family_constant_index\<close>
  gives \<open>index (Y\<^sub>r r) = index (Y\<^sub>r {})\<close> but not \<open>index (Y\<^sub>r {}) = index (Y\<^sub>s {})\<close>, and
  the escape requirement can no longer be posed independently of the seed.

  A monotone union of domains does not by itself repair this either, since enlarging a
  domain changes the denotation of quantified terms that were already present; it is
  not merely that new families arrive.  What a stage-wise construction would need in
  addition is a persistence theorem, to the effect that each term's denotation is
  eventually constant along the chain of domains.

  What can be isolated exactly is the hypothesis under which the construction goes
  through unchanged: a single countable set of propositions covering the requirements
  of every family that any seed can produce.  That is the content of
  \<open>pp_seed_dependent_stock_has_generic_witness\<close> below, and it converts the residual
  problem into one crisp condition on the object language.
\<close>

definition pp_required_of ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop set"
  where
  "pp_required_of Y =
    (if pp_family_constant Y
     then {pp_escape (pp_operator_index (Y {}))}
     else {pp_sep0 Y, pp_sep1 Y})"

lemma pp_required_of_constant:
  assumes "pp_family_constant Y"
  shows "pp_escape (pp_operator_index (Y {})) \<in> pp_required_of Y"
  using assms by (simp add: pp_required_of_def)

lemma pp_required_of_sep0:
  assumes "\<not> pp_family_constant Y"
  shows "pp_sep0 Y \<in> pp_required_of Y"
  using assms by (simp add: pp_required_of_def)

lemma pp_required_of_sep1:
  assumes "\<not> pp_family_constant Y"
  shows "pp_sep1 Y \<in> pp_required_of Y"
  using assms by (simp add: pp_required_of_def)

text \<open>
  The seed-dependent theorem.  \<open>Fam\<close> may now vary with the seed; all that is asked is
  that one countable set of propositions cover the requirements of every family that
  any seed produces.
\<close>

theorem pp_seed_dependent_stock_has_generic_witness:
  fixes Fam ::
    "pp_sem_prop \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and A :: "pp_sem_prop set"
  assumes countable: "countable A"
    and equivariant:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_equivariant_binary_family Y"
    and cover:
      "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_required_of Y \<subseteq> A"
  shows "\<exists>r. pp_img r = r \<and>
    (\<forall>Y \<in> Fam r. pp_fun_invariant (Y r) \<longrightarrow>
       ((\<forall>b. Y b = Y r) \<and>
        pp_root_unary_QLN_operator (Y r) r))"
proof -
  obtain r where symmetric: "pp_img r = r"
    and contained: "A \<subseteq> pp_orbit r"
    using pp_prescribed_orbit_witness[OF countable] by blast
  have main:
      "(\<forall>b. Y b = Y r) \<and> pp_root_unary_QLN_operator (Y r) r"
      if Y_fam: "Y \<in> Fam r" and invariant: "pp_fun_invariant (Y r)"
      for Y
  proof -
    have family: "pp_equivariant_binary_family Y"
      using Y_fam by (rule equivariant)
    have required: "pp_required_of Y \<subseteq> pp_orbit r"
      using cover[OF Y_fam] contained by blast
    have is_constant: "pp_family_constant Y"
    proof (rule ccontr)
      assume nonconstant: "\<not> pp_family_constant Y"
      have b: "pp_sep0 Y \<in> pp_orbit r"
        using pp_required_of_sep0[OF nonconstant] required by blast
      have c: "pp_sep1 Y \<in> pp_orbit r"
        using pp_required_of_sep1[OF nonconstant] required by blast
      have "\<not> pp_fun_invariant (Y r)"
        using family nonconstant b c
        by (rule pp_nonconstant_family_not_invariant)
      then show False using invariant by simp
    qed
    have all_values: "\<forall>b. Y b = Y r"
      using is_constant unfolding pp_family_constant_def by blast
    have index_fixed:
        "pp_operator_index (Y r) = pp_operator_index (Y {})"
      using is_constant by (rule pp_family_constant_index)
    have member: "pp_function_space_member (Y r)"
      using family by (rule pp_equivariant_binary_family_member)
    have escape_condition:
        "(pp_orbit r \<subseteq> pp_operator_index (Y r)) =
         (pp_operator_index (Y r) = UNIV)"
    proof (cases "pp_operator_index (Y r) = UNIV")
      case True
      then show ?thesis by simp
    next
      case False
      then have proper: "pp_operator_index (Y {}) \<noteq> UNIV"
        using index_fixed by simp
      have in_orbit:
          "pp_escape (pp_operator_index (Y {})) \<in> pp_orbit r"
        using pp_required_of_constant[OF is_constant] required by blast
      have "pp_escape (pp_operator_index (Y {}))
          \<notin> pp_operator_index (Y {})"
        using proper by (rule pp_escape_notin)
      then have "\<not> pp_orbit r \<subseteq> pp_operator_index (Y r)"
        using in_orbit index_fixed by blast
      then show ?thesis using False by simp
    qed
    have qln: "pp_root_unary_QLN_operator (Y r) r"
      using pp_invariant_operator_QLN_iff_orbit_escape[
          OF member invariant, of r]
        escape_condition
      by blast
    show ?thesis using all_values qln by blast
  qed
  show ?thesis
    using symmetric main by blast
qed

text \<open>
  A uniform countable envelope for the family sets is one sufficient way to obtain the
  cover, and is the form the condition is most likely to take in practice.
\<close>

corollary pp_uniform_envelope_gives_generic_witness:
  fixes Fam ::
    "pp_sem_prop \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and Fam0 :: "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Fam0"
    and envelope: "\<And>s. Fam s \<subseteq> Fam0"
    and equivariant:
      "\<And>Y. Y \<in> Fam0 \<Longrightarrow> pp_equivariant_binary_family Y"
  shows "\<exists>r. pp_img r = r \<and>
    (\<forall>Y \<in> Fam r. pp_fun_invariant (Y r) \<longrightarrow>
       ((\<forall>b. Y b = Y r) \<and>
        pp_root_unary_QLN_operator (Y r) r))"
proof -
  let ?A = "(\<Union>Y \<in> Fam0. pp_required_of Y)"
  have countable_A: "countable ?A"
  proof (rule countable_UN)
    show "countable Fam0" by (rule countable)
  next
    fix Y
    assume "Y \<in> Fam0"
    show "countable (pp_required_of Y)"
      by (simp add: pp_required_of_def)
  qed
  have equivariant': "\<And>s Y. Y \<in> Fam s \<Longrightarrow>
      pp_equivariant_binary_family Y"
    using envelope equivariant by blast
  have cover: "\<And>s Y. Y \<in> Fam s \<Longrightarrow> pp_required_of Y \<subseteq> ?A"
    using envelope by blast
  show ?thesis
    by (rule pp_seed_dependent_stock_has_generic_witness[
        OF countable_A equivariant' cover])
qed

subsection \<open>What remains\<close>

text \<open>
  The residual obligation is now a single condition, and it is a condition about the
  object language rather than about the witness: either a uniform countable envelope
  \<open>Fam\<^sub>0\<close> containing \<open>Fam s\<close> for every seed \<open>s\<close>, or the weaker uniform requirement
  cover.  Either would close the construction, since
  \<open>pp_seed_dependent_stock_has_generic_witness\<close> then produces the witness outright,
  with no priority ordering and no injury.

  Two further scope notes.  First, the conclusion here is root-level QLN.  Validating
  PP at every world with \<open>Fun\<^bsub>r\<^esub> = pp_operator_equal r\<close> requires the corresponding
  tail-orbit requirements as well; the all-worlds guarded theorem in
  \<open>Bacon_PP_Generic_Witness\<close> uses a different, shifting-fundamental presentation and
  cannot simply be substituted.  Second, none of this yet shows that the resulting
  structure models H, Classicism, CE and CEV; that obligation is untouched.
\<close>

end
