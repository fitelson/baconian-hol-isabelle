theory Bacon_PP_Goodman_M3_Complete
  imports Bacon_PP_Goodman_M6
begin

section \<open>Completion of Goodman M3\<close>

subsection \<open>The gluing construction produces algebraically generic elements\<close>

theorem pp_M3_countable_invariant_stock_has_free_generator:
  assumes countable: "countable Stock"
    and member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
  shows "\<exists>r. pp_M3_free_for_stock Stock r"
proof -
  let ?Bad =
    "(\<lambda>F. - pp_operator_index F) `
      (Stock - {pp_M3_zero_operator})"
  have bad_countable: "countable ?Bad"
    using countable by simp
  have bad_proper: "\<And>S. S \<in> ?Bad \<Longrightarrow> S \<noteq> UNIV"
  proof -
    fix S
    assume S_bad: "S \<in> ?Bad"
    then obtain F where F_stock: "F \<in> Stock"
      and F_nonzero: "F \<noteq> pp_M3_zero_operator"
      and S: "S = - pp_operator_index F"
      by auto
    have representation:
        "F = pp_classifier (pp_operator_index F)"
      using member[OF F_stock] invariant[OF F_stock]
      by (rule pp_fun_invariant_is_classifier)
    show "S \<noteq> UNIV"
    proof
      assume "S = UNIV"
      then have index_empty: "pp_operator_index F = {}"
        unfolding S by blast
      have "F = pp_classifier {}"
        using representation index_empty by simp
      also have "... = pp_M3_zero_operator"
        by (rule ext)
          (simp add: pp_classifier_def pp_M3_zero_operator_def)
      finally show False
        using F_nonzero by contradiction
    qed
  qed
  obtain r where generic:
      "\<forall>S \<in> ?Bad. \<not> pp_orbit r \<subseteq> S"
    using pp_generic_witness_for_countable_proper_stock[
      OF bad_countable bad_proper] by blast
  have free: "pp_M3_free_for_stock Stock r"
    unfolding pp_M3_free_for_stock_def
  proof (intro ballI impI)
    fix F
    assume F_stock: "F \<in> Stock"
      and F_nonzero: "F \<noteq> pp_M3_zero_operator"
    have bad_mem:
        "- pp_operator_index F \<in> ?Bad"
      using F_stock F_nonzero by blast
    have escape:
        "\<not> pp_orbit r \<subseteq> - pp_operator_index F"
      using generic bad_mem by blast
    then obtain q where q_orbit: "q \<in> pp_orbit r"
      and q_index: "q \<in> pp_operator_index F"
      by blast
    obtain i where q: "q = pp_view i r"
      using q_orbit unfolding pp_orbit_def by blast
    have representation:
        "F = pp_classifier (pp_operator_index F)"
      using member[OF F_stock] invariant[OF F_stock]
      by (rule pp_fun_invariant_is_classifier)
    have view_index:
        "pp_view i r \<in> pp_operator_index F"
      using q_index q by simp
    have classifier_mem:
        "i \<in> pp_classifier (pp_operator_index F) r"
      using view_index
      by (simp add: pp_classifier_def)
    have "i \<in> F r"
      using representation classifier_mem by simp
    then show "F r \<noteq> {}"
      by blast
  qed
  show ?thesis
    using free by blast
qed

corollary pp_M3_countable_boolean_stock_has_fun_prime:
  assumes countable: "countable Stock"
    and member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
    and zero_in: "pp_M3_zero_operator \<in> Stock"
    and difference_closed:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        pp_M3_difference_operator F G \<in> Stock"
  shows "\<exists>r. pp_stock_fun_prime Stock r"
proof -
  obtain r where free: "pp_M3_free_for_stock Stock r"
    using pp_M3_countable_invariant_stock_has_free_generator[
      OF countable member invariant] by blast
  have "pp_stock_fun_prime Stock r"
    using pp_M3_fun_prime_iff_free[
      OF zero_in difference_closed, of r] free by blast
  then show ?thesis by blast
qed

text \<open>
  This is the precise gluing claim behind Bacon's construction.  The bad set
  for a nonzero operator is the complement of its root-truth index.  The
  countable branch-gluing theorem chooses one proposition whose orbit escapes
  every such bad set.  Consequently every nonzero operator takes a nonempty
  value there; Boolean difference closure turns this directly into fun-prime.
\<close>

subsection \<open>The finite-cylinder product topology\<close>

definition pp_M3_cylinder ::
    "pp_word set \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_M3_cylinder F p =
    {q. \<forall>w \<in> F. (w \<in> q) = (w \<in> p)}"

definition pp_M3_product_nowhere_dense ::
    "pp_sem_prop set \<Rightarrow> bool" where
  "pp_M3_product_nowhere_dense A \<longleftrightarrow>
    (\<forall>F p. finite F \<longrightarrow>
      (\<exists>G q.
        finite G \<and>
        pp_M3_cylinder G q \<subseteq> pp_M3_cylinder F p \<and>
        pp_M3_cylinder G q \<inter> A = {}))"

definition pp_M3_product_meager ::
    "pp_sem_prop set \<Rightarrow> bool" where
  "pp_M3_product_meager A \<longleftrightarrow>
    (\<exists>N :: nat \<Rightarrow> pp_sem_prop set.
      (\<forall>n. pp_M3_product_nowhere_dense (N n)) \<and>
      A \<subseteq> \<Union>(range N))"

text \<open>
  These are the standard basis characterizations for the product topology on
  \<open>2\<^sup>pp_word\<close>: a basic open cylinder fixes finitely many coordinates;
  nowhere density says that every such cylinder has a basic refinement
  disjoint from the set; meagerness is containment in a countable union of
  nowhere-dense sets.
\<close>

definition pp_M3_necessary_cone ::
    "pp_word \<Rightarrow> pp_sem_prop set" where
  "pp_M3_necessary_cone i =
    {p. pp_view i p = UNIV}"

lemma pp_M3_fresh_cone_point:
  fixes F :: "pp_word set"
    and i :: pp_word
  assumes finite: "finite F"
  obtains x where "x \<notin> F" "\<exists>u. x = u @ i"
proof -
  let ?L = "insert 0 (length ` F)"
  let ?n = "Suc (Max ?L)"
  let ?x = "replicate ?n 0 @ i"
  have L_finite: "finite ?L"
    using finite by simp
  have length_bound: "length y \<le> Max ?L" if "y \<in> F" for y
  proof -
    have "length y \<in> ?L"
      using that by blast
    then show ?thesis
      by (rule Max_ge[OF L_finite])
  qed
  have x_out: "?x \<notin> F"
  proof
    assume x_mem: "?x \<in> F"
    have "length ?x \<le> Max ?L"
      using length_bound[OF x_mem] .
    then show False by simp
  qed
  have suffix: "\<exists>u. ?x = u @ i"
    by blast
  show thesis
    using x_out suffix by (rule that)
qed

lemma pp_M3_necessary_cone_nowhere_dense:
  "pp_M3_product_nowhere_dense (pp_M3_necessary_cone i)"
  unfolding pp_M3_product_nowhere_dense_def
proof (intro allI impI)
  fix F :: "pp_word set"
  fix p :: pp_sem_prop
  assume finite: "finite F"
  obtain x :: pp_word where x_out: "x \<notin> F"
    and suffix: "\<exists>u. x = u @ i"
    by (rule pp_M3_fresh_cone_point[OF finite])
  obtain u where x: "x = u @ i"
    using suffix by blast
  let ?G = "insert x F"
  let ?q = "p - {x}"
  have refinement:
      "pp_M3_cylinder ?G ?q \<subseteq> pp_M3_cylinder F p"
    unfolding pp_M3_cylinder_def
    using x_out by auto
  have disjoint:
      "pp_M3_cylinder ?G ?q \<inter>
        pp_M3_necessary_cone i = {}"
  proof (rule equals0I)
    fix a
    assume a_mem:
      "a \<in> pp_M3_cylinder ?G ?q \<inter>
        pp_M3_necessary_cone i"
    have x_not_a: "x \<notin> a"
      using a_mem
      unfolding pp_M3_cylinder_def by simp
    have view_top: "pp_view i a = UNIV"
      using a_mem
      unfolding pp_M3_necessary_cone_def by simp
    have "u \<in> pp_view i a"
      using view_top by simp
    then have "x \<in> a"
      unfolding pp_view_def using x by simp
    then show False
      using x_not_a by contradiction
  qed
  show "\<exists>G q.
      finite G \<and>
      pp_M3_cylinder G q \<subseteq> pp_M3_cylinder F p \<and>
      pp_M3_cylinder G q \<inter> pp_M3_necessary_cone i = {}"
    using finite refinement disjoint
    by (intro exI[of _ ?G] exI[of _ ?q]) simp
qed

definition pp_M3_word_enum :: "nat \<Rightarrow> pp_word" where
  "pp_M3_word_enum = from_nat_into (UNIV :: pp_word set)"

lemma pp_M3_word_enum_surjective:
  "range pp_M3_word_enum = (UNIV :: pp_word set)"
  unfolding pp_M3_word_enum_def
  by (rule range_from_nat_into) simp_all

theorem pp_M3_fun_prime_class_is_product_meager:
  "pp_M3_product_meager
    {p. pp_stock_fun_prime (pp_fclosure G) p}"
proof -
  let ?N = "\<lambda>n. pp_M3_necessary_cone (pp_M3_word_enum n)"
  have nowhere: "\<forall>n. pp_M3_product_nowhere_dense (?N n)"
    using pp_M3_necessary_cone_nowhere_dense by blast
  have cover:
      "{p. pp_stock_fun_prime (pp_fclosure G) p}
        \<subseteq> \<Union>(range ?N)"
  proof
    fix p
    assume p_mem:
        "p \<in> {p. pp_stock_fun_prime (pp_fclosure G) p}"
    have top_orbit: "UNIV \<in> pp_orbit p"
      using pp_M3_fun_prime_has_extreme_views p_mem by blast
    then obtain i where view_top: "pp_view i p = UNIV"
      unfolding pp_orbit_def by blast
    have "i \<in> range pp_M3_word_enum"
      using pp_M3_word_enum_surjective by simp
    then obtain n where i: "pp_M3_word_enum n = i"
      by blast
    have "p \<in> ?N n"
      unfolding pp_M3_necessary_cone_def using view_top i by simp
    then show "p \<in> \<Union>(range ?N)"
      by blast
  qed
  show ?thesis
    unfolding pp_M3_product_meager_def
    using nowhere cover by (intro exI[of _ ?N]) blast
qed

text \<open>
  Thus M3's terminological warning is exact: fun-prime propositions are
  generic in the algebraic, free-generator sense, but they form a meager class
  in the Cantor product topology.  The meagerness follows already from the
  necessary-view half of the extreme-view theorem.
\<close>

end
