theory Bacon_PP_LevelClasses
  imports Bacon_PP_MSet
begin

section \<open>Depth classes and the refutation of FIN-base\<close>

text \<open>
  This theory mechanises the semantic core of a counterexample to the
  finiteness lemma (FIN-base):

    for every closed Pure-free family \<open>Y\<close> of type \<open>t \<rightarrow> (t \<rightarrow> t)\<close>, only
    finitely many \<open>X\<close> in the Pure-free stock occur as orbit-constant values
    \<open>Y\<^sub>b\<close>.

  The witnessing family classifies pairs of propositions belonging to a common
  \emph{cyclic level partition} of the word monoid.  The main combinatorial
  theorem shows that the cyclic level partitions are exactly the
  depth-modulo-\<open>p\<close> partitions for \<open>p > 0\<close>.  Since the defining condition
  mentions only Boolean structure, the immediate-successor relation on worlds,
  and quantification over propositions and over sets of propositions, it is
  expressible by a closed Pure-free term of Bacon's object language; the
  explicit terms are given in the accompanying report and that half is not
  mechanised here.

  Mechanised here: the action on depth classes, the classification of cyclic
  level partitions, orbit-constancy of the family at every depth class, the
  identification of each realised value with a classifier, and pairwise
  distinctness of the resulting infinitely many invariant values.
\<close>

subsection \<open>Arithmetic preliminaries\<close>

lemma mod_shift_forces_equal:
  fixes p q a :: nat
  assumes q: "0 < q" and a: "a < q" and lt: "p < q" and pos: "0 < p"
    and shift: "(a + p) mod q = a"
  shows False
proof (cases "a + p < q")
  case True
  then have "(a + p) mod q = a + p" by simp
  then show ?thesis using shift pos by simp
next
  case False
  then have "(a + p) mod q = (a + p - q) mod q"
    by (simp add: mod_if)
  moreover have "a + p - q < q" using a lt by simp
  ultimately have "(a + p) mod q = a + p - q" by simp
  then have "a + p - q = a" using shift by simp
  then show ?thesis using False lt by simp
qed

subsection \<open>Depth classes\<close>

definition pp_level_class :: "nat \<Rightarrow> nat \<Rightarrow> pp_sem_prop" where
  "pp_level_class p r = {w. length w mod p = r mod p}"

definition pp_level_partition :: "nat \<Rightarrow> pp_sem_prop set" where
  "pp_level_partition p = {pp_level_class p r | r. r < p}"

lemma pp_level_class_mod[simp]:
  "pp_level_class p (r mod p) = pp_level_class p r"
  by (simp add: pp_level_class_def)

lemma pp_level_class_mem_iff:
  "w \<in> pp_level_class p r \<longleftrightarrow> length w mod p = r mod p"
  by (simp add: pp_level_class_def)

lemma pp_level_class_in_partition:
  assumes "0 < p"
  shows "pp_level_class p r \<in> pp_level_partition p"
proof -
  have "r mod p < p" using assms by simp
  then have "pp_level_class p (r mod p) \<in> pp_level_partition p"
    unfolding pp_level_partition_def by blast
  then show ?thesis by simp
qed

lemma pp_level_class_nonempty:
  assumes "0 < p"
  shows "pp_level_class p r \<noteq> {}"
proof -
  have "replicate (r mod p) (0::nat) \<in> pp_level_class p r"
    using assms by (simp add: pp_level_class_mem_iff)
  then show ?thesis by blast
qed

lemma pp_level_class_disjoint:
  assumes "r mod p \<noteq> s mod p"
  shows "pp_level_class p r \<inter> pp_level_class p s = {}"
  using assms by (auto simp: pp_level_class_mem_iff)

lemma pp_level_partition_cover:
  assumes "0 < p"
  shows "\<Union> (pp_level_partition p) = UNIV"
proof
  show "\<Union> (pp_level_partition p) \<subseteq> UNIV" by simp
next
  show "UNIV \<subseteq> \<Union> (pp_level_partition p)"
  proof
    fix w :: pp_word
    assume "w \<in> UNIV"
    have "pp_level_class p (length w) \<in> pp_level_partition p"
      using assms by (rule pp_level_class_in_partition)
    moreover have "w \<in> pp_level_class p (length w)"
      by (simp add: pp_level_class_mem_iff)
    ultimately show "w \<in> \<Union> (pp_level_partition p)" by blast
  qed
qed

text \<open>Distinct moduli give distinct depth classes.\<close>

lemma pp_level_class_modulus_unique:
  assumes p: "0 < p" and q: "0 < q"
    and eq: "pp_level_class p r = pp_level_class q s"
  shows "p = q"
proof -
  define a where "a = r mod p"
  define b where "b = s mod q"
  have a_lt: "a < p" using p by (simp add: a_def)
  have b_lt: "b < q" using q by (simp add: b_def)
  have lengths: "(n mod p = a) \<longleftrightarrow> (n mod q = b)" for n :: nat
  proof -
    have "replicate n (0::nat) \<in> pp_level_class p r \<longleftrightarrow>
          replicate n (0::nat) \<in> pp_level_class q s"
      using eq by simp
    then show ?thesis
      by (simp add: pp_level_class_mem_iff a_def b_def)
  qed
  have "a mod p = a" using a_lt by simp
  then have aq: "a mod q = b" using lengths by blast
  then have "b \<le> a" by (metis mod_less_eq_dividend)
  have "b mod q = b" using b_lt by simp
  then have bp: "b mod p = a" using lengths by blast
  then have "a \<le> b" by (metis mod_less_eq_dividend)
  with \<open>b \<le> a\<close> have ab: "a = b" by simp
  have a_lt_q: "a < q" using ab b_lt by simp
  have b_lt_p: "b < p" using ab a_lt by simp
  have shift_q: "(a + p) mod q = a"
  proof -
    have "(a + p) mod p = a" using a_lt by simp
    then have "(a + p) mod q = b" using lengths by blast
    then show ?thesis using ab by simp
  qed
  have shift_p: "(b + q) mod p = b"
  proof -
    have "(b + q) mod q = b" using b_lt by simp
    then have "(b + q) mod p = a" using lengths by blast
    then show ?thesis using ab by simp
  qed
  show "p = q"
  proof (rule ccontr)
    assume "p \<noteq> q"
    then consider (lt) "p < q" | (gt) "q < p" by linarith
    then show False
    proof cases
      case lt
      show False
        using mod_shift_forces_equal[OF q a_lt_q lt p shift_q] .
    next
      case gt
      show False
        using mod_shift_forces_equal[OF p b_lt_p gt q shift_p] .
    qed
  qed
qed

subsection \<open>The action on depth classes\<close>

lemma pp_view_level_class:
  assumes p: "0 < p"
  shows "pp_view i (pp_level_class p r) =
           pp_level_class p (r + (p - length i mod p))"
proof (rule set_eqI)
  fix w :: pp_word
  define c where "c = length i mod p"
  have c_lt: "c < p" using p by (simp add: c_def)
  have "w \<in> pp_view i (pp_level_class p r) \<longleftrightarrow>
        (length w + length i) mod p = r mod p"
    by (simp add: pp_view_def pp_level_class_mem_iff)
  also have "... \<longleftrightarrow> (length w + c) mod p = r mod p"
    by (simp add: c_def mod_add_right_eq)
  also have "... \<longleftrightarrow> length w mod p = (r + (p - c)) mod p"
  proof
    assume "(length w + c) mod p = r mod p"
    then have "(length w + c + (p - c)) mod p = (r + (p - c)) mod p"
      by (metis mod_add_left_eq)
    moreover have "length w + c + (p - c) = length w + p"
      using c_lt by simp
    ultimately show "length w mod p = (r + (p - c)) mod p"
      by simp
  next
    assume "length w mod p = (r + (p - c)) mod p"
    then have "(length w + c) mod p = (r + (p - c) + c) mod p"
      by (metis mod_add_left_eq)
    moreover have "r + (p - c) + c = r + p"
      using c_lt by simp
    ultimately show "(length w + c) mod p = r mod p"
      by simp
  qed
  also have "... \<longleftrightarrow> w \<in> pp_level_class p (r + (p - c))"
    by (simp add: pp_level_class_mem_iff)
  finally show "w \<in> pp_view i (pp_level_class p r) \<longleftrightarrow>
                w \<in> pp_level_class p (r + (p - length i mod p))"
    by (simp add: c_def)
qed

corollary pp_view_level_partition_closed:
  assumes "0 < p" and "Z \<in> pp_level_partition p"
  shows "pp_view i Z \<in> pp_level_partition p"
proof -
  obtain r where r: "r < p" "Z = pp_level_class p r"
    using assms unfolding pp_level_partition_def by blast
  have "pp_view i Z = pp_level_class p (r + (p - length i mod p))"
    using assms(1) r by (simp add: pp_view_level_class)
  then show ?thesis
    using assms(1) pp_level_class_in_partition by simp
qed

subsection \<open>Cyclic level partitions\<close>

definition pp_succ :: "pp_word \<Rightarrow> pp_word \<Rightarrow> bool" where
  "pp_succ i j \<longleftrightarrow> (\<exists>k. j = k # i)"

definition pp_shift_class ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_shift_class q q' \<longleftrightarrow>
     (\<forall>i j. pp_succ i j \<longrightarrow> i \<in> q \<longrightarrow> j \<in> q')"

definition pp_cyclic_level_partition ::
    "pp_sem_prop set \<Rightarrow> bool" where
  "pp_cyclic_level_partition Z \<longleftrightarrow>
     (\<forall>q \<in> Z. q \<noteq> {}) \<and>
     (\<forall>q \<in> Z. \<forall>q' \<in> Z. q \<noteq> q' \<longrightarrow> q \<inter> q' = {}) \<and>
     \<Union> Z = UNIV \<and>
     (\<forall>q \<in> Z. \<exists>q' \<in> Z. pp_shift_class q q') \<and>
     (\<forall>q' \<in> Z. \<exists>q \<in> Z. pp_shift_class q q')"

lemma pp_succ_length:
  "pp_succ i j \<Longrightarrow> length j = Suc (length i)"
  by (auto simp: pp_succ_def)

lemma pp_shift_class_level:
  "pp_shift_class (pp_level_class p r) (pp_level_class p (Suc r))"
proof (unfold pp_shift_class_def, intro allI impI)
  fix i j
  assume succ: "pp_succ i j" and mem: "i \<in> pp_level_class p r"
  have "length j = Suc (length i)"
    using succ by (rule pp_succ_length)
  moreover have "length i mod p = r mod p"
    using mem by (simp add: pp_level_class_mem_iff)
  ultimately have "length j mod p = Suc r mod p"
    by (metis mod_Suc_eq)
  then show "j \<in> pp_level_class p (Suc r)"
    by (simp add: pp_level_class_mem_iff)
qed

theorem pp_level_partition_cyclic:
  assumes p: "0 < p"
  shows "pp_cyclic_level_partition (pp_level_partition p)"
proof (unfold pp_cyclic_level_partition_def, intro conjI ballI)
  fix q assume "q \<in> pp_level_partition p"
  then show "q \<noteq> {}"
    using p pp_level_class_nonempty
    unfolding pp_level_partition_def by auto
next
  fix q q'
  assume "q \<in> pp_level_partition p" "q' \<in> pp_level_partition p"
  then obtain r s where rs: "r < p" "q = pp_level_class p r"
      "s < p" "q' = pp_level_class p s"
    unfolding pp_level_partition_def by blast
  show "q \<noteq> q' \<longrightarrow> q \<inter> q' = {}"
  proof
    assume "q \<noteq> q'"
    then have "r mod p \<noteq> s mod p"
      using rs by auto
    then show "q \<inter> q' = {}"
      using rs pp_level_class_disjoint by simp
  qed
next
  show "\<Union> (pp_level_partition p) = UNIV"
    using p by (rule pp_level_partition_cover)
next
  fix q assume "q \<in> pp_level_partition p"
  then obtain r where r: "r < p" "q = pp_level_class p r"
    unfolding pp_level_partition_def by blast
  have "pp_level_class p (Suc r) \<in> pp_level_partition p"
    using p by (rule pp_level_class_in_partition)
  moreover have "pp_shift_class q (pp_level_class p (Suc r))"
    using r by (simp add: pp_shift_class_level)
  ultimately show "\<exists>q' \<in> pp_level_partition p. pp_shift_class q q'"
    by blast
next
  fix q' assume "q' \<in> pp_level_partition p"
  then obtain s where s: "s < p" "q' = pp_level_class p s"
    unfolding pp_level_partition_def by blast
  define r where "r = s + p - 1"
  have suc_r: "Suc r = s + p"
    using p by (simp add: r_def)
  have "pp_level_class p r \<in> pp_level_partition p"
    using p by (rule pp_level_class_in_partition)
  moreover have "pp_shift_class (pp_level_class p r) q'"
  proof -
    have "pp_shift_class (pp_level_class p r) (pp_level_class p (Suc r))"
      by (rule pp_shift_class_level)
    moreover have "pp_level_class p (Suc r) = q'"
      using suc_r s by (simp add: pp_level_class_def)
    ultimately show ?thesis by simp
  qed
  ultimately show "\<exists>q \<in> pp_level_partition p. pp_shift_class q q'"
    by blast
qed

subsection \<open>Every cyclic level partition is a depth partition\<close>

definition pp_cls :: "pp_sem_prop set \<Rightarrow> pp_word \<Rightarrow> pp_sem_prop" where
  "pp_cls Z w = (THE q. q \<in> Z \<and> w \<in> q)"

definition pp_lev :: "pp_sem_prop set \<Rightarrow> nat \<Rightarrow> pp_sem_prop" where
  "pp_lev Z n = pp_cls Z (replicate n (0::nat))"

definition pp_period :: "pp_sem_prop set \<Rightarrow> nat" where
  "pp_period Z = (LEAST m. 0 < m \<and> pp_lev Z m = pp_lev Z 0)"

context
  fixes Z :: "pp_sem_prop set"
  assumes cyc: "pp_cyclic_level_partition Z"
begin

lemma cyc_nonempty: "q \<in> Z \<Longrightarrow> q \<noteq> {}"
  using cyc unfolding pp_cyclic_level_partition_def by blast

lemma cyc_disjoint:
  "q \<in> Z \<Longrightarrow> q' \<in> Z \<Longrightarrow> q \<noteq> q' \<Longrightarrow> q \<inter> q' = {}"
  using cyc unfolding pp_cyclic_level_partition_def by blast

lemma cyc_cover: "\<Union> Z = UNIV"
  using cyc unfolding pp_cyclic_level_partition_def by blast

lemma cyc_shift: "q \<in> Z \<Longrightarrow> \<exists>q' \<in> Z. pp_shift_class q q'"
  using cyc unfolding pp_cyclic_level_partition_def by blast

lemma cyc_shift_onto: "q' \<in> Z \<Longrightarrow> \<exists>q \<in> Z. pp_shift_class q q'"
  using cyc unfolding pp_cyclic_level_partition_def by blast

lemma cyc_cls_unique:
  assumes "q \<in> Z" and "w \<in> q"
  shows "pp_cls Z w = q"
  unfolding pp_cls_def
proof (rule the_equality)
  show "q \<in> Z \<and> w \<in> q" using assms by blast
next
  fix q' assume "q' \<in> Z \<and> w \<in> q'"
  then show "q' = q"
    using assms cyc_disjoint by blast
qed

lemma cyc_cls_mem: "pp_cls Z w \<in> Z \<and> w \<in> pp_cls Z w"
proof -
  obtain q where q: "q \<in> Z" "w \<in> q"
    using cyc_cover by blast
  then show ?thesis
    using cyc_cls_unique by auto
qed

lemma cyc_cls_length:
  "length v = length w \<Longrightarrow> pp_cls Z v = pp_cls Z w"
proof (induct v arbitrary: w)
  case Nil
  then show ?case by simp
next
  case (Cons a v)
  then obtain b w' where w: "w = b # w'" and len: "length v = length w'"
    by (cases w) auto
  have ih: "pp_cls Z v = pp_cls Z w'"
    using Cons.hyps len by blast
  obtain q' where q': "q' \<in> Z" "pp_shift_class (pp_cls Z v) q'"
    using cyc_shift cyc_cls_mem by blast
  have "pp_succ v (a # v)" by (simp add: pp_succ_def)
  then have "a # v \<in> q'"
    using q' cyc_cls_mem unfolding pp_shift_class_def by blast
  then have left: "pp_cls Z (a # v) = q'"
    using q' cyc_cls_unique by blast
  have "pp_succ w' (b # w')" by (simp add: pp_succ_def)
  then have "b # w' \<in> q'"
    using q' ih cyc_cls_mem unfolding pp_shift_class_def by metis
  then have "pp_cls Z (b # w') = q'"
    using q' cyc_cls_unique by blast
  then show ?case using left w by simp
qed

lemma pp_lev_cls: "pp_cls Z w = pp_lev Z (length w)"
  unfolding pp_lev_def by (rule cyc_cls_length) simp

lemma pp_lev_mem: "pp_lev Z n \<in> Z"
  unfolding pp_lev_def using cyc_cls_mem by blast

lemma pp_lev_contains: "length w = n \<Longrightarrow> w \<in> pp_lev Z n"
  using pp_lev_cls cyc_cls_mem by metis

lemma pp_lev_iff:
  "w \<in> pp_lev Z n \<longleftrightarrow> pp_lev Z (length w) = pp_lev Z n"
proof
  assume "w \<in> pp_lev Z n"
  then show "pp_lev Z (length w) = pp_lev Z n"
    using pp_lev_mem cyc_cls_unique pp_lev_cls by metis
next
  assume "pp_lev Z (length w) = pp_lev Z n"
  then show "w \<in> pp_lev Z n"
    using pp_lev_contains by metis
qed

lemma cyc_shift_class_unique:
  assumes "q \<in> Z" "q' \<in> Z" "q'' \<in> Z"
    and "pp_shift_class q q'" and "pp_shift_class q q''"
  shows "q' = q''"
proof -
  obtain w where w: "w \<in> q"
    using assms(1) cyc_nonempty by blast
  have "pp_succ w (0 # w)" by (simp add: pp_succ_def)
  then have "0 # w \<in> q'" and "0 # w \<in> q''"
    using assms w unfolding pp_shift_class_def by blast+
  then show ?thesis
    using assms cyc_disjoint by blast
qed

lemma pp_lev_shift: "pp_shift_class (pp_lev Z n) (pp_lev Z (Suc n))"
proof -
  obtain q' where q': "q' \<in> Z" "pp_shift_class (pp_lev Z n) q'"
    using cyc_shift pp_lev_mem by blast
  have "pp_succ (replicate n (0::nat)) (0 # replicate n (0::nat))"
    by (simp add: pp_succ_def)
  moreover have "replicate n (0::nat) \<in> pp_lev Z n"
    by (rule pp_lev_contains) simp
  ultimately have "0 # replicate n (0::nat) \<in> q'"
    using q' unfolding pp_shift_class_def by blast
  then have "pp_cls Z (0 # replicate n (0::nat)) = q'"
    using q' cyc_cls_unique by blast
  moreover have "pp_cls Z (0 # replicate n (0::nat)) = pp_lev Z (Suc n)"
    using pp_lev_cls by simp
  ultimately show ?thesis using q' by simp
qed

lemma pp_lev_step_congruent:
  assumes "pp_lev Z m = pp_lev Z n"
  shows "pp_lev Z (Suc m) = pp_lev Z (Suc n)"
proof -
  have "pp_shift_class (pp_lev Z m) (pp_lev Z (Suc m))"
    by (rule pp_lev_shift)
  moreover have "pp_shift_class (pp_lev Z m) (pp_lev Z (Suc n))"
    using assms pp_lev_shift by simp
  ultimately show ?thesis
    using cyc_shift_class_unique pp_lev_mem by blast
qed

lemma pp_lev_shift_congruent:
  assumes "pp_lev Z m = pp_lev Z n"
  shows "pp_lev Z (m + k) = pp_lev Z (n + k)"
proof (induct k)
  case 0
  show ?case using assms by simp
next
  case (Suc k)
  have "pp_lev Z (Suc (m + k)) = pp_lev Z (Suc (n + k))"
    using Suc by (rule pp_lev_step_congruent)
  then show ?case by simp
qed

lemma pp_lev_returns: "\<exists>m. 0 < m \<and> pp_lev Z m = pp_lev Z 0"
proof -
  obtain q where q: "q \<in> Z" "pp_shift_class q (pp_lev Z 0)"
    using cyc_shift_onto pp_lev_mem by blast
  obtain w where w: "w \<in> q" using q cyc_nonempty by blast
  then have "q = pp_lev Z (length w)"
    using q cyc_cls_unique pp_lev_cls by metis
  then have "pp_shift_class (pp_lev Z (length w)) (pp_lev Z 0)"
    using q by simp
  moreover have
    "pp_shift_class (pp_lev Z (length w)) (pp_lev Z (Suc (length w)))"
    by (rule pp_lev_shift)
  ultimately have "pp_lev Z (Suc (length w)) = pp_lev Z 0"
    using cyc_shift_class_unique pp_lev_mem by blast
  then show ?thesis by blast
qed

lemma pp_period_spec:
  "0 < pp_period Z \<and> pp_lev Z (pp_period Z) = pp_lev Z 0"
  unfolding pp_period_def
  using pp_lev_returns by (rule LeastI_ex)

lemma pp_period_pos: "0 < pp_period Z"
  using pp_period_spec by blast

lemma pp_period_least:
  "0 < m \<Longrightarrow> pp_lev Z m = pp_lev Z 0 \<Longrightarrow> pp_period Z \<le> m"
  unfolding pp_period_def by (rule Least_le) simp

lemma pp_lev_periodic: "pp_lev Z (n + pp_period Z) = pp_lev Z n"
proof -
  have "pp_lev Z (pp_period Z + n) = pp_lev Z (0 + n)"
    using pp_period_spec pp_lev_shift_congruent by blast
  then show ?thesis by (simp add: add.commute)
qed

lemma pp_lev_periodic_mult: "pp_lev Z (n + pp_period Z * k) = pp_lev Z n"
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "pp_lev Z (n + pp_period Z * Suc k)
      = pp_lev Z ((n + pp_period Z * k) + pp_period Z)"
    by (simp add: algebra_simps)
  also have "... = pp_lev Z (n + pp_period Z * k)"
    by (rule pp_lev_periodic)
  also have "... = pp_lev Z n"
    using Suc by simp
  finally show ?case .
qed

lemma pp_lev_mod: "pp_lev Z n = pp_lev Z (n mod pp_period Z)"
proof -
  have "n = n mod pp_period Z + pp_period Z * (n div pp_period Z)"
    by simp
  then show ?thesis
    using pp_lev_periodic_mult by metis
qed

lemma pp_lev_inj_below_period:
  assumes r: "r < pp_period Z" and s: "s < pp_period Z"
    and eq: "pp_lev Z r = pp_lev Z s"
  shows "r = s"
proof (rule ccontr)
  assume "r \<noteq> s"
  then consider (lt) "r < s" | (gt) "s < r" by linarith
  then show False
  proof cases
    case lt
    have "pp_lev Z (r + (pp_period Z - s)) = pp_lev Z (s + (pp_period Z - s))"
      by (rule pp_lev_shift_congruent[OF eq])
    moreover have "s + (pp_period Z - s) = pp_period Z"
      using s by simp
    ultimately have "pp_lev Z (r + (pp_period Z - s)) = pp_lev Z 0"
      using pp_period_spec by simp
    moreover have "0 < r + (pp_period Z - s)"
      using lt s by simp
    ultimately have "pp_period Z \<le> r + (pp_period Z - s)"
      by (rule pp_period_least[rotated])
    then show False using lt s by simp
  next
    case gt
    have "pp_lev Z (s + (pp_period Z - r)) = pp_lev Z (r + (pp_period Z - r))"
      by (rule pp_lev_shift_congruent[OF eq[symmetric]])
    moreover have "r + (pp_period Z - r) = pp_period Z"
      using r by simp
    ultimately have "pp_lev Z (s + (pp_period Z - r)) = pp_lev Z 0"
      using pp_period_spec by simp
    moreover have "0 < s + (pp_period Z - r)"
      using gt r by simp
    ultimately have "pp_period Z \<le> s + (pp_period Z - r)"
      by (rule pp_period_least[rotated])
    then show False using gt r by simp
  qed
qed

lemma pp_lev_eq_level_class:
  assumes r: "r < pp_period Z"
  shows "pp_lev Z r = pp_level_class (pp_period Z) r"
proof (rule set_eqI)
  fix w :: pp_word
  have "w \<in> pp_lev Z r \<longleftrightarrow> pp_lev Z (length w) = pp_lev Z r"
    by (rule pp_lev_iff)
  also have "... \<longleftrightarrow>
      pp_lev Z (length w mod pp_period Z) = pp_lev Z r"
    using pp_lev_mod by metis
  also have "... \<longleftrightarrow> length w mod pp_period Z = r"
  proof
    assume "pp_lev Z (length w mod pp_period Z) = pp_lev Z r"
    then show "length w mod pp_period Z = r"
      using pp_lev_inj_below_period r pp_period_pos by simp
  next
    assume "length w mod pp_period Z = r"
    then show "pp_lev Z (length w mod pp_period Z) = pp_lev Z r"
      by simp
  qed
  also have "... \<longleftrightarrow> w \<in> pp_level_class (pp_period Z) r"
    using r by (simp add: pp_level_class_mem_iff)
  finally show "w \<in> pp_lev Z r \<longleftrightarrow> w \<in> pp_level_class (pp_period Z) r" .
qed

lemma cyc_eq_level_partition: "Z = pp_level_partition (pp_period Z)"
proof
  show "Z \<subseteq> pp_level_partition (pp_period Z)"
  proof
    fix q assume q: "q \<in> Z"
    then obtain w where w: "w \<in> q" using cyc_nonempty by blast
    have "q = pp_lev Z (length w)"
      using q w cyc_cls_unique pp_lev_cls by metis
    also have "... = pp_lev Z (length w mod pp_period Z)"
      using pp_lev_mod by blast
    also have "... = pp_level_class (pp_period Z) (length w mod pp_period Z)"
      using pp_period_pos by (simp add: pp_lev_eq_level_class)
    finally show "q \<in> pp_level_partition (pp_period Z)"
      using pp_period_pos pp_level_class_in_partition by simp
  qed
next
  show "pp_level_partition (pp_period Z) \<subseteq> Z"
  proof
    fix q assume "q \<in> pp_level_partition (pp_period Z)"
    then obtain r where r: "r < pp_period Z"
        "q = pp_level_class (pp_period Z) r"
      unfolding pp_level_partition_def by blast
    then have "q = pp_lev Z r"
      using pp_lev_eq_level_class by simp
    then show "q \<in> Z" using pp_lev_mem by simp
  qed
qed

end

theorem pp_cyclic_level_partition_iff:
  "pp_cyclic_level_partition Z \<longleftrightarrow> (\<exists>p. 0 < p \<and> Z = pp_level_partition p)"
proof
  assume "pp_cyclic_level_partition Z"
  then show "\<exists>p. 0 < p \<and> Z = pp_level_partition p"
    using cyc_eq_level_partition pp_period_pos by blast
next
  assume "\<exists>p. 0 < p \<and> Z = pp_level_partition p"
  then show "pp_cyclic_level_partition Z"
    using pp_level_partition_cyclic by blast
qed

subsection \<open>The refuting family\<close>

text \<open>
  \<open>pp_cyc_rel\<close> is the root-level relation denoted by the Pure-free term
  \<open>\<lambda>b c. \<exists>F. CycPart(F) \<and> F b \<and> F c\<close>; \<open>pp_cyc_family\<close> is the corresponding
  equivariant element of \<open>A\<^sub>t\<^sub>\<rightarrow>\<^sub>t\<^sub>\<rightarrow>\<^sub>t\<close>, computed by the binary classifier
  identity \<open>Y b c = {i. R (i \<cdot> b) (i \<cdot> c)}\<close>.
\<close>

definition pp_cyc_rel :: "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_cyc_rel b c \<longleftrightarrow>
     (\<exists>Z. pp_cyclic_level_partition Z \<and> b \<in> Z \<and> c \<in> Z)"

definition pp_cyc_family ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_cyc_family b c = {i. pp_cyc_rel (pp_view i b) (pp_view i c)}"

lemma pp_cyc_family_equivariant:
  "pp_view i (pp_cyc_family b c) =
     pp_cyc_family (pp_view i b) (pp_view i c)"
  by (auto simp: pp_view_def pp_cyc_family_def pp_view_compose[symmetric]
      append_assoc)

lemma pp_cyc_rel_level_fibre:
  assumes p: "0 < p"
  shows "pp_cyc_rel (pp_level_class p r) c \<longleftrightarrow> c \<in> pp_level_partition p"
proof
  assume "pp_cyc_rel (pp_level_class p r) c"
  then obtain Z where Z: "pp_cyclic_level_partition Z"
      "pp_level_class p r \<in> Z" "c \<in> Z"
    unfolding pp_cyc_rel_def by blast
  obtain q where q: "0 < q" "Z = pp_level_partition q"
    using Z(1) pp_cyclic_level_partition_iff by blast
  obtain s where s: "s < q" "pp_level_class p r = pp_level_class q s"
    using Z(2) q unfolding pp_level_partition_def by blast
  have "p = q"
    using pp_level_class_modulus_unique[OF p q(1) s(2)] .
  then show "c \<in> pp_level_partition p"
    using Z(3) q by simp
next
  assume c: "c \<in> pp_level_partition p"
  have "pp_cyclic_level_partition (pp_level_partition p)"
    using p by (rule pp_level_partition_cyclic)
  moreover have "pp_level_class p r \<in> pp_level_partition p"
    using p by (rule pp_level_class_in_partition)
  ultimately show "pp_cyc_rel (pp_level_class p r) c"
    unfolding pp_cyc_rel_def using c by blast
qed

theorem pp_cyc_family_at_level_class:
  assumes p: "0 < p"
  shows "pp_cyc_family (pp_level_class p r) =
           pp_classifier (pp_level_partition p)"
proof (rule ext, rule set_eqI)
  fix c :: pp_sem_prop and i :: pp_word
  have view: "pp_view i (pp_level_class p r) =
      pp_level_class p (r + (p - length i mod p))"
    using p by (rule pp_view_level_class)
  have "i \<in> pp_cyc_family (pp_level_class p r) c \<longleftrightarrow>
      pp_cyc_rel (pp_view i (pp_level_class p r)) (pp_view i c)"
    by (simp add: pp_cyc_family_def)
  also have "... \<longleftrightarrow> pp_view i c \<in> pp_level_partition p"
    using view p pp_cyc_rel_level_fibre by simp
  also have "... \<longleftrightarrow> i \<in> pp_classifier (pp_level_partition p) c"
    by (simp add: pp_classifier_def)
  finally show "i \<in> pp_cyc_family (pp_level_class p r) c \<longleftrightarrow>
                i \<in> pp_classifier (pp_level_partition p) c" .
qed

corollary pp_cyc_family_orbit_constant:
  assumes p: "0 < p"
  shows "pp_cyc_family (pp_view j (pp_level_class p r)) =
           pp_cyc_family (pp_level_class p r)"
proof -
  have "pp_view j (pp_level_class p r) =
      pp_level_class p (r + (p - length j mod p))"
    using p by (rule pp_view_level_class)
  then show ?thesis
    using p pp_cyc_family_at_level_class by simp
qed

corollary pp_cyc_family_value_invariant:
  assumes p: "0 < p"
  shows "pp_equivariant_operator (pp_cyc_family (pp_level_class p r)) \<and>
         pp_fun_invariant (pp_cyc_family (pp_level_class p r))"
  using assms pp_cyc_family_at_level_class
    pp_classifier_is_function_space_invariant
    pp_classifier_equivariant_operator
  by metis

theorem pp_level_partition_inj:
  assumes p: "0 < p" and q: "0 < q"
    and eq: "pp_level_partition p = pp_level_partition q"
  shows "p = q"
proof -
  have "pp_level_class p 0 \<in> pp_level_partition p"
    using p by (rule pp_level_class_in_partition)
  then have "pp_level_class p 0 \<in> pp_level_partition q"
    using eq by simp
  then obtain s where "pp_level_class p 0 = pp_level_class q s"
    unfolding pp_level_partition_def by blast
  then show ?thesis
    using pp_level_class_modulus_unique[OF p q] by simp
qed

theorem pp_cyc_family_values_pairwise_distinct:
  assumes p: "0 < p" and q: "0 < q" and pq: "p \<noteq> q"
  shows "pp_cyc_family (pp_level_class p 0) \<noteq>
         pp_cyc_family (pp_level_class q 0)"
proof
  assume "pp_cyc_family (pp_level_class p 0) =
          pp_cyc_family (pp_level_class q 0)"
  then have "pp_classifier (pp_level_partition p) =
             pp_classifier (pp_level_partition q)"
    using p q pp_cyc_family_at_level_class by metis
  then have "pp_level_partition p = pp_level_partition q"
    using pp_classifier_injective by (simp add: injD)
  then show False
    using pp_level_partition_inj p q pq by blast
qed

theorem pp_cyc_family_realises_infinitely_many_invariant_values:
  "infinite {X. \<exists>b. (\<forall>j. pp_cyc_family (pp_view j b) = X) \<and>
                    pp_fun_invariant X}"
proof -
  let ?V = "{X. \<exists>b. (\<forall>j. pp_cyc_family (pp_view j b) = X) \<and>
                    pp_fun_invariant X}"
  have mem: "pp_cyc_family (pp_level_class p 0) \<in> ?V" if "0 < p" for p
  proof -
    have "\<forall>j. pp_cyc_family (pp_view j (pp_level_class p 0)) =
              pp_cyc_family (pp_level_class p 0)"
      using that pp_cyc_family_orbit_constant by blast
    moreover have "pp_fun_invariant (pp_cyc_family (pp_level_class p 0))"
      using that pp_cyc_family_value_invariant by blast
    ultimately show ?thesis by blast
  qed
  have "inj_on (\<lambda>p. pp_cyc_family (pp_level_class p 0)) {p. 0 < p}"
    by (rule inj_onI)
      (metis mem_Collect_eq pp_cyc_family_values_pairwise_distinct)
  moreover have "infinite {p::nat. 0 < p}"
  proof
    assume "finite {p::nat. 0 < p}"
    then have "finite (insert (0::nat) {p::nat. 0 < p})" by simp
    moreover have "insert (0::nat) {p::nat. 0 < p} = UNIV" by auto
    ultimately show False by simp
  qed
  ultimately have "infinite ((\<lambda>p. pp_cyc_family (pp_level_class p 0)) ` {p. 0 < p})"
    by (simp add: finite_image_iff)
  moreover have "(\<lambda>p. pp_cyc_family (pp_level_class p 0)) ` {p. 0 < p} \<subseteq> ?V"
    using mem by blast
  ultimately show ?thesis
    using infinite_super by blast
qed

text \<open>
  Reading of the last theorem.  Each realised value is
  \<open>pp_classifier (pp_level_partition p)\<close>, an invariant element of Bacon's
  function space at type \<open>t \<rightarrow> t\<close>, orbit-constant on the whole orbit of the
  depth-class parameter \<open>b\<^sub>p\<close>, and the values for distinct \<open>p\<close> are distinct.
  In the report it is shown that each of these values is denoted by a closed
  Pure-free term (an explicit one is given for each \<open>p\<close>), and that
  \<open>pp_cyc_rel\<close> is denoted by a single closed Pure-free term.  Hence FIN-base
  fails: infinitely many members of \<open>L\<^sub>t\<^sub>\<rightarrow>\<^sub>t\<close> have a non-empty
  orbit-constant fibre for one and the same Pure-free family.
\<close>

end
