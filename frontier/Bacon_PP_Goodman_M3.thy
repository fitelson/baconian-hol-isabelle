theory Bacon_PP_Goodman_M3
  imports Bacon_PP_Goodman_M1
begin

section \<open>Goodman M3: fun-prime is algebraic freeness\<close>

subsection \<open>The no-nontrivial-law characterization\<close>

definition pp_M3_zero_operator ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M3_zero_operator = (\<lambda>P. {})"

definition pp_M3_difference_operator ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop)" where
  "pp_M3_difference_operator F G =
    (\<lambda>P. (F P - G P) \<union> (G P - F P))"

definition pp_M3_free_for_stock ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      pp_sem_prop \<Rightarrow> bool" where
  "pp_M3_free_for_stock Stock p \<longleftrightarrow>
    (\<forall>V \<in> Stock.
      V \<noteq> pp_M3_zero_operator \<longrightarrow> V p \<noteq> {})"

lemma pp_M3_difference_zero_iff:
  "pp_M3_difference_operator F G = pp_M3_zero_operator
    \<longleftrightarrow> F = G"
proof
  assume zero:
      "pp_M3_difference_operator F G = pp_M3_zero_operator"
  show "F = G"
  proof (rule ext, rule set_eqI)
    fix P x
    have empty_difference:
        "(F P - G P) \<union> (G P - F P) = {}"
    proof -
      have "pp_M3_difference_operator F G P =
          pp_M3_zero_operator P"
        using zero by (rule fun_cong)
      then show ?thesis
        by (simp add: pp_M3_difference_operator_def
            pp_M3_zero_operator_def)
    qed
    show "x \<in> F P \<longleftrightarrow> x \<in> G P"
      using empty_difference by blast
  qed
next
  assume "F = G"
  then show
      "pp_M3_difference_operator F G = pp_M3_zero_operator"
    by (simp add: pp_M3_difference_operator_def
        pp_M3_zero_operator_def)
qed

theorem pp_M3_fun_prime_iff_free:
  assumes zero_in: "pp_M3_zero_operator \<in> Stock"
    and difference_closed:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        pp_M3_difference_operator F G \<in> Stock"
  shows "pp_stock_fun_prime Stock p
    \<longleftrightarrow> pp_M3_free_for_stock Stock p"
proof
  assume fun_prime: "pp_stock_fun_prime Stock p"
  show "pp_M3_free_for_stock Stock p"
    unfolding pp_M3_free_for_stock_def
  proof (intro ballI impI)
    fix V
    assume V_stock: "V \<in> Stock"
      and V_nonzero: "V \<noteq> pp_M3_zero_operator"
    show "V p \<noteq> {}"
    proof
      assume Vp: "V p = {}"
      have agreement: "V p = pp_M3_zero_operator p"
        using Vp by (simp add: pp_M3_zero_operator_def)
      have "V = pp_M3_zero_operator"
        using fun_prime V_stock zero_in agreement
        by (rule pp_stock_fun_primeD)
      then show False
        using V_nonzero by contradiction
    qed
  qed
next
  assume free: "pp_M3_free_for_stock Stock p"
  show "pp_stock_fun_prime Stock p"
  proof (rule pp_stock_fun_primeI)
    fix F G
    assume F_stock: "F \<in> Stock"
      and G_stock: "G \<in> Stock"
      and agreement: "F p = G p"
    let ?V = "pp_M3_difference_operator F G"
    have V_stock: "?V \<in> Stock"
      using F_stock G_stock by (rule difference_closed)
    have Vp: "?V p = {}"
      using agreement
      by (simp add: pp_M3_difference_operator_def)
    have "\<not> ?V \<noteq> pp_M3_zero_operator"
      using free V_stock Vp
      unfolding pp_M3_free_for_stock_def by blast
    then have "?V = pp_M3_zero_operator" by blast
    then show "F = G"
      by (simp add: pp_M3_difference_zero_iff)
  qed
qed

subsection \<open>The constant-free logical operator stock\<close>

lemma pp_M3_zero_in_fclosure:
  "pp_M3_zero_operator \<in> pp_fclosure G"
proof -
  have empty_cone: "pp_cone_det_prop G {}"
    using pp_qclosure_empty
    by (rule pp_qclosure_cone_det)
  have "(\<lambda>P. {}) \<in> pp_fclosure G"
    using empty_cone by (rule f_const)
  then show ?thesis
    by (simp add: pp_M3_zero_operator_def)
qed

lemma pp_M3_difference_in_fclosure:
  assumes F: "F \<in> pp_fclosure G"
    and H: "H \<in> pp_fclosure G"
  shows "pp_M3_difference_operator F H \<in> pp_fclosure G"
proof -
  have not_H: "(\<lambda>P. - H P) \<in> pp_fclosure G"
    using H by (rule f_compl)
  have not_F: "(\<lambda>P. - F P) \<in> pp_fclosure G"
    using F by (rule f_compl)
  have left: "(\<lambda>P. F P \<inter> - H P) \<in> pp_fclosure G"
    using F not_H by (rule pp_fclosure_Intop)
  have right: "(\<lambda>P. H P \<inter> - F P) \<in> pp_fclosure G"
    using H not_F by (rule pp_fclosure_Intop)
  have union:
      "(\<lambda>P. (F P \<inter> - H P) \<union> (H P \<inter> - F P))
        \<in> pp_fclosure G"
    using left right by (rule pp_fclosure_Unop)
  have
      "pp_M3_difference_operator F H =
       (\<lambda>P. (F P \<inter> - H P) \<union> (H P \<inter> - F P))"
    by (rule ext)
      (auto simp: pp_M3_difference_operator_def)
  then show ?thesis
    using union by simp
qed

corollary pp_M3_logical_fun_prime_iff_free:
  "pp_stock_fun_prime (pp_fclosure G) p
    \<longleftrightarrow> pp_M3_free_for_stock (pp_fclosure G) p"
  using pp_M3_zero_in_fclosure[of G]
    pp_M3_difference_in_fclosure[of _ G]
  by (rule pp_M3_fun_prime_iff_free)

subsection \<open>Extreme views\<close>

definition pp_M3_possibly_necessary ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M3_possibly_necessary P =
    - pp_sem_box (- pp_sem_box P)"

definition pp_M3_possibly_impossible ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M3_possibly_impossible P =
    - pp_sem_box (- pp_sem_box (- P))"

lemma pp_M3_possibly_necessary_iff:
  "i \<in> pp_M3_possibly_necessary P
    \<longleftrightarrow> (\<exists>j. pp_view (j @ i) P = UNIV)"
  by (auto simp: pp_M3_possibly_necessary_def
      pp_sem_box_def pp_view_def append_assoc)

lemma pp_M3_possibly_impossible_iff:
  "i \<in> pp_M3_possibly_impossible P
    \<longleftrightarrow> (\<exists>j. pp_view (j @ i) P = {})"
  by (auto simp: pp_M3_possibly_impossible_def
      pp_sem_box_def pp_view_def append_assoc)

lemma pp_M3_possibly_necessary_nonzero:
  "pp_M3_possibly_necessary \<noteq> pp_M3_zero_operator"
proof
  assume equality:
      "pp_M3_possibly_necessary = pp_M3_zero_operator"
  have "[] \<in> pp_M3_possibly_necessary UNIV"
    by (simp add: pp_M3_possibly_necessary_iff)
  moreover have
      "pp_M3_possibly_necessary UNIV =
       pp_M3_zero_operator UNIV"
    using equality by (rule fun_cong)
  ultimately show False
    by (simp add: pp_M3_zero_operator_def)
qed

lemma pp_M3_possibly_impossible_nonzero:
  "pp_M3_possibly_impossible \<noteq> pp_M3_zero_operator"
proof
  assume equality:
      "pp_M3_possibly_impossible = pp_M3_zero_operator"
  have "[] \<in> pp_M3_possibly_impossible {}"
    by (simp add: pp_M3_possibly_impossible_iff)
  moreover have
      "pp_M3_possibly_impossible {} =
       pp_M3_zero_operator {}"
    using equality by (rule fun_cong)
  ultimately show False
    by (simp add: pp_M3_zero_operator_def)
qed

lemma pp_M3_possibly_necessary_in_fclosure:
  "pp_M3_possibly_necessary \<in> pp_fclosure G"
proof -
  have box_id: "(\<lambda>P. pp_sem_box P) \<in> pp_fclosure G"
    using f_id by (rule f_box)
  then have not_box:
      "(\<lambda>P. - pp_sem_box P) \<in> pp_fclosure G"
    by (rule f_compl)
  then have box_not_box:
      "(\<lambda>P. pp_sem_box (- pp_sem_box P)) \<in> pp_fclosure G"
    by (rule f_box)
  then have
      "(\<lambda>P. - pp_sem_box (- pp_sem_box P)) \<in> pp_fclosure G"
    by (rule f_compl)
  then show ?thesis
    unfolding pp_M3_possibly_necessary_def .
qed

lemma pp_M3_possibly_impossible_in_fclosure:
  "pp_M3_possibly_impossible \<in> pp_fclosure G"
proof -
  have neg: "(\<lambda>P. - P) \<in> pp_fclosure G"
    using f_id by (rule f_compl)
  then have box_neg:
      "(\<lambda>P. pp_sem_box (- P)) \<in> pp_fclosure G"
    by (rule f_box)
  then have not_box_neg:
      "(\<lambda>P. - pp_sem_box (- P)) \<in> pp_fclosure G"
    by (rule f_compl)
  then have box_not_box_neg:
      "(\<lambda>P. pp_sem_box (- pp_sem_box (- P))) \<in> pp_fclosure G"
    by (rule f_box)
  then have
      "(\<lambda>P. - pp_sem_box (- pp_sem_box (- P)))
        \<in> pp_fclosure G"
    by (rule f_compl)
  then show ?thesis
    unfolding pp_M3_possibly_impossible_def .
qed

theorem pp_M3_fun_prime_has_extreme_views:
  assumes fun_prime: "pp_stock_fun_prime (pp_fclosure G) p"
  shows "UNIV \<in> pp_orbit p \<and> {} \<in> pp_orbit p"
proof -
  have free: "pp_M3_free_for_stock (pp_fclosure G) p"
    using fun_prime
    by (simp add: pp_M3_logical_fun_prime_iff_free)
  have possible_necessary:
      "pp_M3_possibly_necessary p \<noteq> {}"
    using free pp_M3_possibly_necessary_in_fclosure[of G]
      pp_M3_possibly_necessary_nonzero
    unfolding pp_M3_free_for_stock_def by blast
  then obtain i j where necessary:
      "pp_view (j @ i) p = UNIV"
    using pp_M3_possibly_necessary_iff by blast
  have "UNIV \<in> pp_orbit p"
    using necessary unfolding pp_orbit_def by blast
  moreover have possible_impossible:
      "pp_M3_possibly_impossible p \<noteq> {}"
    using free pp_M3_possibly_impossible_in_fclosure[of G]
      pp_M3_possibly_impossible_nonzero
    unfolding pp_M3_free_for_stock_def by blast
  then obtain k l where impossible:
      "pp_view (l @ k) p = {}"
    using pp_M3_possibly_impossible_iff by blast
  have "{} \<in> pp_orbit p"
    using impossible unfolding pp_orbit_def by blast
  ultimately show ?thesis by blast
qed

text \<open>
  We have therefore proved the algebraic content of M3 exactly.  For every
  Boolean-closed certified stock, fun-prime is equivalent to satisfying no
  nonzero unary law.  For the constant-free logical closure this forces both
  a necessary and an impossible view.  The countable gluing construction and
  the topological claim, with meagerness stated using explicit finite-cylinder
  bases for \<open>2\<^sup>M\<close>, are proved in
  \<open>Bacon_PP_Goodman_M3_Complete\<close>.
\<close>

end
