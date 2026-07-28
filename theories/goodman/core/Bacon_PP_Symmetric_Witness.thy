theory Bacon_PP_Symmetric_Witness
  imports Bacon_PP_TreeAut
begin

section \<open>A tree-symmetric generic witness\<close>

text \<open>
  \<open>Bacon_PP_Generic_Witness\<close> produces, for every countable stock of classifier
  indices, a proposition whose orbit escapes every proper index.  That witness is
  built by gluing independently chosen views at the depth-one cones \<open>[n]\<close>, and
  nothing makes it stable under the tree automorphism.

  Stability matters.  The Pure-free language contains the fundamentality predicate
  \<open>Fun\<close> as well as the logical constants, and in the intended model \<open>Fun\<close> is the
  local identity predicate for the fundamental proposition.  So \<open>Fun\<close> is
  conjugation-fixed exactly when the fundamental witness is.  Without that, the
  non-definability argument of \<open>Bacon_PP_TypeCoherence\<close> would apply only to the
  logical fragment.

  A witness cannot be made symmetric by choosing symmetric views cone by cone.  For a
  witness glued from the depth-one cones, \<open>pp_img R = R\<close> forces every chosen view
  \<open>pp_view [n] R\<close> to be fixed by letterwise swapping, because \<open>pp_tw\<close> leaves the
  final letter alone and swaps all the others.  But \<open>{P. pp_swap_all P = P}\<close> is a
  proper stock index that no letterwise-fixed proposition escapes, so a stock
  containing it defeats every such local choice.  Note this is letterwise symmetry,
  not tree symmetry: the two conditions differ precisely at the final letter.

  The repair is to symmetrize globally, across \emph{pairs} of cones exchanged by the
  automorphism.  The pair \<open>[0, n]\<close> and \<open>[1, n]\<close> is exchanged by \<open>pp_tw\<close>, so an
  arbitrary unsymmetric view may be placed on the first and its mirror image on the
  second.
\<close>

subsection \<open>Letterwise swapping\<close>

definition pp_swap_all :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_swap_all P = {w. map pp_sw w \<in> P}"

lemma pp_sw_comp_sw[simp]: "pp_sw \<circ> pp_sw = id"
  by (rule ext) simp

lemma pp_map_sw_sw[simp]: "map pp_sw (map pp_sw w) = w"
  by simp

lemma pp_swap_all_swap_all[simp]: "pp_swap_all (pp_swap_all P) = P"
  by (auto simp: pp_swap_all_def)

lemma pp_swap_all_mem[simp]: "w \<in> pp_swap_all P \<longleftrightarrow> map pp_sw w \<in> P"
  by (simp add: pp_swap_all_def)

text \<open>
  The set of letterwise-symmetric propositions is a proper stock index containing
  every symmetric proposition.  This is why local symmetrization fails.
\<close>

lemma pp_symmetric_propositions_proper:
  "{P. pp_swap_all P = P} \<noteq> UNIV"
proof -
  have "pp_swap_all {[0::nat]} \<noteq> {[0::nat]}"
  proof -
    have "[1::nat] \<in> pp_swap_all {[0::nat]}"
      by (simp add: pp_sw_def)
    moreover have "[1::nat] \<notin> {[0::nat]}"
      by simp
    ultimately show ?thesis by blast
  qed
  then show ?thesis by blast
qed

subsection \<open>The automorphism on a suffix cone\<close>

lemma pp_tw_append_nonempty:
  assumes "i \<noteq> []"
  shows "pp_tw (u @ i) = map pp_sw u @ pp_tw i"
proof (induct u)
  case Nil
  show ?case by simp
next
  case (Cons a u)
  obtain b v where i: "i = b # v"
    using assms by (cases i) auto
  have ne: "u @ i \<noteq> []"
    by (simp add: i)
  have "pp_tw ((a # u) @ i) = pp_sw a # pp_tw (u @ i)"
    by (simp add: i)
  also have "... = pp_sw a # (map pp_sw u @ pp_tw i)"
    using Cons.hyps by simp
  finally show ?case by simp
qed

definition pp_cone_a :: "nat \<Rightarrow> pp_word" where
  "pp_cone_a n = [0, n]"

definition pp_cone_b :: "nat \<Rightarrow> pp_word" where
  "pp_cone_b n = [1, n]"

lemma pp_cone_a_nonempty[simp]: "pp_cone_a n \<noteq> []"
  by (simp add: pp_cone_a_def)

lemma pp_cone_b_nonempty[simp]: "pp_cone_b n \<noteq> []"
  by (simp add: pp_cone_b_def)

lemma pp_tw_cone_a[simp]: "pp_tw (pp_cone_a n) = pp_cone_b n"
  by (simp add: pp_cone_a_def pp_cone_b_def pp_sw_def)

lemma pp_tw_cone_b[simp]: "pp_tw (pp_cone_b n) = pp_cone_a n"
  by (simp add: pp_cone_a_def pp_cone_b_def pp_sw_def)

lemma pp_tw_in_cone_a:
  "pp_tw (u @ pp_cone_a n) = map pp_sw u @ pp_cone_b n"
  by (simp add: pp_tw_append_nonempty)

lemma pp_tw_in_cone_b:
  "pp_tw (u @ pp_cone_b n) = map pp_sw u @ pp_cone_a n"
  by (simp add: pp_tw_append_nonempty)

lemma pp_cone_append_eq_a:
  "u @ pp_cone_a n = v @ pp_cone_a m \<longleftrightarrow> u = v \<and> n = m"
  by (auto simp: pp_cone_a_def)

lemma pp_cone_append_eq_b:
  "u @ pp_cone_b n = v @ pp_cone_b m \<longleftrightarrow> u = v \<and> n = m"
  by (auto simp: pp_cone_b_def)

lemma pp_cone_append_a_neq_b:
  "u @ pp_cone_a n \<noteq> v @ pp_cone_b m"
  by (auto simp: pp_cone_a_def pp_cone_b_def)

subsection \<open>The paired-cone witness\<close>

definition pp_paired_witness ::
    "(nat \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_paired_witness q =
    (\<Union>n. pp_lift (pp_cone_a n) (q n) \<union>
         pp_lift (pp_cone_b n) (pp_swap_all (q n)))"

lemma pp_paired_witness_mem:
  "w \<in> pp_paired_witness q \<longleftrightarrow>
    ((\<exists>n u. w = u @ pp_cone_a n \<and> u \<in> q n) \<or>
     (\<exists>n u. w = u @ pp_cone_b n \<and> map pp_sw u \<in> q n))"
  by (auto simp: pp_paired_witness_def pp_lift_def)

theorem pp_view_paired_witness[simp]:
  "pp_view (pp_cone_a n) (pp_paired_witness q) = q n"
proof (rule set_eqI)
  fix j
  have "j \<in> pp_view (pp_cone_a n) (pp_paired_witness q) \<longleftrightarrow>
      j @ pp_cone_a n \<in> pp_paired_witness q"
    by (simp add: pp_view_def)
  also have "... \<longleftrightarrow> j \<in> q n"
    by (auto simp: pp_paired_witness_mem pp_cone_append_eq_a
        pp_cone_append_a_neq_b)
  finally show
      "j \<in> pp_view (pp_cone_a n) (pp_paired_witness q) \<longleftrightarrow> j \<in> q n" .
qed

theorem pp_paired_witness_symmetric:
  "pp_img (pp_paired_witness q) = pp_paired_witness q"
proof -
  have forward:
      "pp_tw w \<in> pp_paired_witness q" if "w \<in> pp_paired_witness q" for w
  proof -
    from that consider
        (a) n u where "w = u @ pp_cone_a n" "u \<in> q n"
      | (b) n u where "w = u @ pp_cone_b n" "map pp_sw u \<in> q n"
      by (auto simp: pp_paired_witness_mem)
    then show ?thesis
    proof cases
      case a
      have "pp_tw w = map pp_sw u @ pp_cone_b n \<and>
          map pp_sw (map pp_sw u) \<in> q n"
        using a by (simp add: pp_tw_in_cone_a)
      then show ?thesis
        unfolding pp_paired_witness_mem by blast
    next
      case b
      have "pp_tw w = map pp_sw u @ pp_cone_a n \<and>
          map pp_sw u \<in> q n"
        using b by (simp add: pp_tw_in_cone_b)
      then show ?thesis
        unfolding pp_paired_witness_mem by blast
    qed
  qed
  show ?thesis
  proof
    show "pp_img (pp_paired_witness q) \<subseteq> pp_paired_witness q"
    proof
      fix w
      assume "w \<in> pp_img (pp_paired_witness q)"
      then have "pp_tw w \<in> pp_paired_witness q" by simp
      then have "pp_tw (pp_tw w) \<in> pp_paired_witness q"
        by (rule forward)
      then show "w \<in> pp_paired_witness q" by simp
    qed
  next
    show "pp_paired_witness q \<subseteq> pp_img (pp_paired_witness q)"
    proof
      fix w
      assume "w \<in> pp_paired_witness q"
      then have "pp_tw w \<in> pp_paired_witness q" by (rule forward)
      then show "w \<in> pp_img (pp_paired_witness q)" by simp
    qed
  qed
qed

subsection \<open>The symmetric generic witness theorems\<close>

theorem pp_symmetric_generic_witness_for_sequence:
  fixes E :: "nat \<Rightarrow> pp_sem_prop set"
  assumes proper: "\<And>n. E n \<noteq> UNIV"
  shows "\<exists>R. pp_img R = R \<and> (\<forall>n. \<not> pp_orbit R \<subseteq> E n)"
proof -
  let ?q = "pp_outside_choice E"
  let ?R = "pp_paired_witness ?q"
  have outside: "?q n \<notin> E n" for n
    using proper by (rule pp_outside_choice_notin)
  have orbit: "?q n \<in> pp_orbit ?R" for n
    unfolding pp_orbit_def
    using pp_view_paired_witness[of n ?q]
    by (intro range_eqI[where x = "pp_cone_a n"]) simp
  have generic: "\<not> pp_orbit ?R \<subseteq> E n" for n
    using orbit[of n] outside[of n] by blast
  have symmetric: "pp_img ?R = ?R"
    by (rule pp_paired_witness_symmetric)
  show ?thesis
    using generic symmetric by blast
qed

theorem pp_symmetric_generic_witness_for_countable_proper_stock:
  fixes Stock :: "pp_sem_prop set set"
  assumes countable: "countable Stock"
    and proper: "\<And>S. S \<in> Stock \<Longrightarrow> S \<noteq> UNIV"
  shows "\<exists>R. pp_img R = R \<and> (\<forall>S \<in> Stock. \<not> pp_orbit R \<subseteq> S)"
proof (cases "Stock = {}")
  case True
  show ?thesis
  proof (intro exI[of _ "{}"] conjI)
    show "pp_img {} = {}"
      by (simp add: pp_img_def)
  next
    show "\<forall>S \<in> Stock. \<not> pp_orbit {} \<subseteq> S"
      using True by simp
  qed
next
  case False
  let ?E = "from_nat_into Stock"
  have E_range: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have E_mem: "?E n \<in> Stock" for n
    using E_range by blast
  have E_proper: "?E n \<noteq> UNIV" for n
    using E_mem by (rule proper)
  obtain R where symmetric: "pp_img R = R"
    and generic: "\<forall>n. \<not> pp_orbit R \<subseteq> ?E n"
    using pp_symmetric_generic_witness_for_sequence[of ?E] E_proper
    by blast
  show ?thesis
  proof (intro exI[of _ R] conjI ballI)
    show "pp_img R = R" by (rule symmetric)
  next
    fix S
    assume S_mem: "S \<in> Stock"
    have "S \<in> range ?E"
      using S_mem E_range by simp
    then obtain n where "?E n = S"
      by auto
    then show "\<not> pp_orbit R \<subseteq> S"
      using generic by blast
  qed
qed

theorem pp_countable_stock_has_symmetric_generic_QLN_witness:
  fixes Stock :: "pp_sem_prop set set"
  assumes countable: "countable Stock"
  shows "\<exists>R. pp_img R = R \<and>
    (\<forall>S \<in> Stock. pp_root_unary_QLN S R)"
proof -
  let ?Proper = "Stock - {UNIV}"
  have proper_countable: "countable ?Proper"
    using countable by (rule countable_subset[rotated]) auto
  obtain R where symmetric: "pp_img R = R"
    and generic: "\<forall>S \<in> ?Proper. \<not> pp_orbit R \<subseteq> S"
    using pp_symmetric_generic_witness_for_countable_proper_stock[
        OF proper_countable]
    by blast
  show ?thesis
  proof (intro exI[of _ R] conjI ballI)
    show "pp_img R = R" by (rule symmetric)
  next
    fix S
    assume S_mem: "S \<in> Stock"
    show "pp_root_unary_QLN S R"
    proof (cases "S = UNIV")
      case True
      then show ?thesis by (simp add: pp_root_unary_QLN_iff)
    next
      case False
      then have "S \<in> ?Proper" using S_mem by simp
      then have "\<not> pp_orbit R \<subseteq> S" using generic by blast
      with False show ?thesis
        by (simp add: pp_root_unary_QLN_iff)
    qed
  qed
qed

corollary pp_countable_function_stock_has_symmetric_QLN_witness:
  fixes Stock :: "(pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Stock"
    and member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
  shows "\<exists>R. pp_img R = R \<and>
    (\<forall>F \<in> Stock. pp_root_unary_QLN_operator F R)"
proof -
  let ?Indices = "pp_operator_index ` Stock"
  have indices_countable: "countable ?Indices"
    using countable by (rule countable_image)
  obtain R where symmetric: "pp_img R = R"
    and index_QLN: "\<forall>S \<in> ?Indices. pp_root_unary_QLN S R"
    using pp_countable_stock_has_symmetric_generic_QLN_witness[
        OF indices_countable]
    by blast
  show ?thesis
  proof (intro exI[of _ R] conjI ballI)
    show "pp_img R = R" by (rule symmetric)
  next
    fix F
    assume F_stock: "F \<in> Stock"
    have qln: "pp_root_unary_QLN (pp_operator_index F) R"
      using index_QLN F_stock by blast
    then have orbit_condition:
        "(pp_orbit R \<subseteq> pp_operator_index F) =
         (pp_operator_index F = UNIV)"
      by (simp add: pp_root_unary_QLN_iff)
    show "pp_root_unary_QLN_operator F R"
      using pp_invariant_operator_QLN_iff_orbit_escape[
          OF member[OF F_stock] invariant[OF F_stock], of R]
        orbit_condition
      by blast
  qed
qed

text \<open>
  Hence the fundamental witness can always be chosen tree-symmetric.  In the intended
  model the fundamentality predicate is the local identity predicate for that witness,
  so the whole Pure-free signature, and not merely its logical fragment, can be taken
  conjugation-fixed.
\<close>

end
