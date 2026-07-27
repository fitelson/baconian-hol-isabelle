theory Bacon_PP_Goodman_M4
  imports Bacon_PP_Goodman_M3
begin

section \<open>Goodman M4: fun-prime outruns the fundamental orbit\<close>

subsection \<open>Preimage heredity\<close>

theorem pp_M4_fun_prime_preimage:
  assumes viewed_free:
      "pp_stock_fun_prime Stock (pp_view i p)"
    and pure_member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and pure_invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
  shows "pp_stock_fun_prime Stock p"
proof (rule pp_stock_fun_primeI)
  fix F G
  assume F_stock: "F \<in> Stock"
    and G_stock: "G \<in> Stock"
    and agreement: "F p = G p"
  have F_action:
      "F (pp_view i p) = pp_view i (F p)"
  proof -
    have
        "pp_fun_view i F (pp_view i p) = pp_view i (F p)"
      using pure_member[OF F_stock]
      by (rule pp_fun_view_preimage_independent) simp
    moreover have "pp_fun_view i F = F"
      using pure_invariant[OF F_stock]
      unfolding pp_fun_invariant_def by blast
    ultimately show ?thesis by simp
  qed
  have G_action:
      "G (pp_view i p) = pp_view i (G p)"
  proof -
    have
        "pp_fun_view i G (pp_view i p) = pp_view i (G p)"
      using pure_member[OF G_stock]
      by (rule pp_fun_view_preimage_independent) simp
    moreover have "pp_fun_view i G = G"
      using pure_invariant[OF G_stock]
      unfolding pp_fun_invariant_def by blast
    ultimately show ?thesis by simp
  qed
  have viewed_agreement:
      "F (pp_view i p) = G (pp_view i p)"
    using F_action G_action agreement by simp
  show "F = G"
    using viewed_free F_stock G_stock viewed_agreement
    by (rule pp_stock_fun_primeD)
qed

subsection \<open>Reversible certified operators\<close>

definition pp_M4_reversible_in_stock ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_M4_reversible_in_stock Stock Z \<longleftrightarrow>
    Z \<in> Stock \<and>
    (\<exists>W \<in> Stock.
      (\<forall>P. W (Z P) = P) \<and>
      (\<forall>P. Z (W P) = P))"

definition pp_M4_pure_orbit ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_M4_pure_orbit Stock r =
    {p. \<exists>Z. pp_M4_reversible_in_stock Stock Z \<and> p = Z r}"

lemma pp_M4_fun_prime_not_empty:
  assumes free: "pp_stock_fun_prime Stock q"
    and identity: "(\<lambda>P :: pp_sem_prop. P) \<in> Stock"
    and zero: "(\<lambda>P :: pp_sem_prop. {}) \<in> Stock"
  shows "q \<noteq> {}"
proof
  assume "q = {}"
  then have agreement:
      "(\<lambda>P :: pp_sem_prop. P) q =
       (\<lambda>P :: pp_sem_prop. {}) q"
    by simp
  have "(\<lambda>P :: pp_sem_prop. P) =
      (\<lambda>P :: pp_sem_prop. {})"
    by (rule pp_stock_fun_primeD[
          OF free identity zero agreement])
  then show False
    by (metis UNIV_not_empty fun_cong)
qed

lemma pp_M4_fun_prime_not_UNIV:
  assumes free: "pp_stock_fun_prime Stock q"
    and identity: "(\<lambda>P :: pp_sem_prop. P) \<in> Stock"
    and one: "(\<lambda>P :: pp_sem_prop. UNIV) \<in> Stock"
  shows "q \<noteq> UNIV"
proof
  assume "q = UNIV"
  then have agreement:
      "(\<lambda>P :: pp_sem_prop. P) q =
       (\<lambda>P :: pp_sem_prop. UNIV) q"
    by simp
  have "(\<lambda>P :: pp_sem_prop. P) =
      (\<lambda>P :: pp_sem_prop. UNIV)"
    by (rule pp_stock_fun_primeD[
          OF free identity one agreement])
  then have "({} :: pp_sem_prop) = UNIV"
    by (rule fun_cong)
  then show False by simp
qed

lemma pp_M4_view_lift_other_branch:
  "pp_view [Suc n] (pp_lift [n] P) = {}"
  by (auto simp: pp_view_def pp_lift_def append_singleton_eq_iff)

lemma pp_M4_invariant_maps_extreme_to_extreme:
  assumes member: "pp_function_space_member F"
    and invariant: "pp_fun_invariant F"
    and extreme: "P = {} \<or> P = UNIV"
  shows "F P = {} \<or> F P = UNIV"
proof -
  have equivariant: "pp_equivariant_operator F"
    using member invariant
    by (simp add: pp_fun_invariant_iff_equivariant)
  have P_invariant: "pp_invariant_proposition P"
    using extreme by (simp add: pp_invariant_proposition_iff_extreme)
  have FP_invariant: "pp_invariant_proposition (F P)"
    unfolding pp_invariant_proposition_def
  proof
    fix i
    have "pp_view i (F P) = F (pp_view i P)"
      using equivariant
      unfolding pp_equivariant_operator_def by blast
    also have "... = F P"
      using P_invariant
      unfolding pp_invariant_proposition_def by simp
    finally show "pp_view i (F P) = F P" .
  qed
  show ?thesis
    using FP_invariant
    by (simp add: pp_invariant_proposition_iff_extreme)
qed

theorem pp_M4_explicit_fun_prime_outside_fundamental_orbit:
  assumes qss:
      "pp_stock_necessitated_QSS Stock r"
    and pure_member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and pure_invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
    and identity: "(\<lambda>P :: pp_sem_prop. P) \<in> Stock"
    and zero: "(\<lambda>P :: pp_sem_prop. {}) \<in> Stock"
    and one: "(\<lambda>P :: pp_sem_prop. UNIV) \<in> Stock"
  defines "p \<equiv> pp_lift [0] r"
  shows "pp_stock_fun_prime Stock p
    \<and> p \<notin> pp_M4_pure_orbit Stock r"
proof
  have r_free: "pp_stock_fun_prime Stock r"
  proof -
    have "pp_stock_fun_prime Stock (pp_view [] r)"
      using qss
      unfolding pp_stock_necessitated_QSS_def by blast
    then show ?thesis by simp
  qed
  have view_p: "pp_view [0] p = r"
    unfolding p_def by simp
  show p_free: "pp_stock_fun_prime Stock p"
  proof -
    have "pp_stock_fun_prime Stock (pp_view [0] p)"
      using r_free view_p by simp
    then show ?thesis
      using pure_member pure_invariant
      by (rule pp_M4_fun_prime_preimage)
  qed
next
  show "p \<notin> pp_M4_pure_orbit Stock r"
  proof
    assume orbit: "p \<in> pp_M4_pure_orbit Stock r"
    then obtain Z W where
        Z_rev: "pp_M4_reversible_in_stock Stock Z"
      and pZ: "p = Z r"
      and W_stock: "W \<in> Stock"
      and WZ: "\<forall>P. W (Z P) = P"
      unfolding pp_M4_pure_orbit_def
        pp_M4_reversible_in_stock_def
      by blast
    have rWp: "r = W p"
      using pZ WZ by simp
    have p_empty: "pp_view [1] p = {}"
      unfolding p_def
      using pp_M4_view_lift_other_branch[of 0 r] by simp
    have W_equivariant: "pp_equivariant_operator W"
      using pure_member[OF W_stock] pure_invariant[OF W_stock]
      by (simp add: pp_fun_invariant_iff_equivariant)
    have r_view:
        "pp_view [1] r = W {}"
    proof -
      have "pp_view [1] r = pp_view [1] (W p)"
        using rWp by simp
      also have "... = W (pp_view [1] p)"
        using W_equivariant
        unfolding pp_equivariant_operator_def by blast
      also have "... = W {}"
        using p_empty by simp
      finally show ?thesis .
    qed
    have W_empty_extreme: "W {} = {} \<or> W {} = UNIV"
      using pure_member[OF W_stock] pure_invariant[OF W_stock]
      by (rule pp_M4_invariant_maps_extreme_to_extreme) simp
    have view_free:
        "pp_stock_fun_prime Stock (pp_view [1] r)"
      using qss
      unfolding pp_stock_necessitated_QSS_def by blast
    have view_nonempty: "pp_view [1] r \<noteq> {}"
      using view_free identity zero
      by (rule pp_M4_fun_prime_not_empty)
    have view_nonuniversal: "pp_view [1] r \<noteq> UNIV"
      using view_free identity one
      by (rule pp_M4_fun_prime_not_UNIV)
    show False
      using r_view W_empty_extreme view_nonempty view_nonuniversal
      by blast
  qed
qed

text \<open>
  The witness is exactly Goodman's: place the pattern of \<open>r\<close> above the
  branch \<open>[0]\<close> and leave the disjoint branch \<open>[1]\<close> empty.  Its
  \<open>[0]\<close>-view is \<open>r\<close>, so preimage heredity makes it fun-prime.  If it
  were a reversible pure image of \<open>r\<close>, the invariant pure inverse would
  recover a nonextreme view of \<open>r\<close> from the empty proposition.  Equivariance
  forces the image of an invariant proposition to remain invariant, hence
  extreme, which is the required contradiction.
\<close>

end
