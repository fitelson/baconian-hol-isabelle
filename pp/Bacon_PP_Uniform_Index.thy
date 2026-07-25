theory Bacon_PP_Uniform_Index
  imports Bacon_PP_LevelClasses
begin

section \<open>The range condition does not express invariance\<close>

text \<open>
  A proposed replacement for FIN-base was to require the invariant logical
  values of a Pure-free family \<open>Y\<close> to lie in the range of one Pure-free family
  \<open>K\<close>, and then to express stock membership by

    \<open>\<exists>a. \<box> Eq (Y b) (K a)\<close>.

  The range condition alone is insufficient.  Equality with some value of
  \<open>K\<close> does not say that this value is invariant.  The constant-operator
  family gives the smallest counterexample.
\<close>

definition pp_constant_operator_family ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_constant_operator_family b c = b"

lemma pp_constant_operator_family_equivariant:
  "pp_view i (pp_constant_operator_family b c) =
    pp_constant_operator_family (pp_view i b) (pp_view i c)"
  by (simp add: pp_constant_operator_family_def)

lemma pp_constant_operator_member:
  "pp_function_space_member (pp_constant_operator_family b)"
  unfolding pp_function_space_member_def
    pp_constant_operator_family_def
  by simp

lemma pp_constant_operator_equivariant_iff:
  "pp_equivariant_operator (pp_constant_operator_family b) \<longleftrightarrow>
    pp_invariant_proposition b"
proof
  assume operator: "pp_equivariant_operator (pp_constant_operator_family b)"
  show "pp_invariant_proposition b"
  proof (unfold pp_invariant_proposition_def, intro allI)
    fix i
    have "pp_view i
        (pp_constant_operator_family b {}) =
      pp_constant_operator_family b (pp_view i {})"
      using operator unfolding pp_equivariant_operator_def by blast
    then show "pp_view i b = b"
      by (simp add: pp_constant_operator_family_def)
  qed
next
  assume invariant_b: "pp_invariant_proposition b"
  show "pp_equivariant_operator (pp_constant_operator_family b)"
  proof (unfold pp_equivariant_operator_def, intro allI)
    fix i P
    have "pp_view i b = b"
      using invariant_b unfolding pp_invariant_proposition_def by blast
    then show
      "pp_view i (pp_constant_operator_family b P) =
       pp_constant_operator_family b (pp_view i P)"
      by (simp add: pp_constant_operator_family_def)
  qed
qed

theorem pp_constant_operator_invariant_iff_extreme:
  "pp_fun_invariant (pp_constant_operator_family b) \<longleftrightarrow>
    b = {} \<or> b = UNIV"
proof -
  have "pp_fun_invariant (pp_constant_operator_family b) \<longleftrightarrow>
      pp_equivariant_operator (pp_constant_operator_family b)"
    using pp_constant_operator_member
    by (rule pp_fun_invariant_iff_equivariant)
  also have "... \<longleftrightarrow> pp_invariant_proposition b"
    by (rule pp_constant_operator_equivariant_iff)
  also have "... \<longleftrightarrow> b = {} \<or> b = UNIV"
    by (rule pp_invariant_proposition_iff_extreme)
  finally show ?thesis .
qed

definition pp_fun_local_equal ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_fun_local_equal F G =
    {i. pp_fun_view i F = pp_fun_view i G}"

lemma pp_fun_local_equal_refl[simp]:
  "pp_fun_local_equal F F = UNIV"
  by (simp add: pp_fun_local_equal_def)

definition pp_uniform_range_test ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> bool" where
  "pp_uniform_range_test Y K b \<longleftrightarrow>
    (\<exists>a. pp_root_true
      (pp_sem_box (pp_fun_local_equal (Y b) (K a))))"

lemma pp_uniform_range_test_self:
  "pp_uniform_range_test Y Y b"
proof -
  have "pp_root_true
      (pp_sem_box (pp_fun_local_equal (Y b) (Y b)))"
    by (simp add: pp_root_true_def pp_sem_box_def)
  then show ?thesis
    unfolding pp_uniform_range_test_def by blast
qed

theorem pp_naive_IDX_base_counterexample:
  "{b. pp_fun_invariant (pp_constant_operator_family b)}
    \<noteq>
   {b. pp_uniform_range_test
      pp_constant_operator_family pp_constant_operator_family b}"
proof -
  have left:
      "{b. pp_fun_invariant (pp_constant_operator_family b)}
       = {{}, UNIV}"
    by (auto simp: pp_constant_operator_invariant_iff_extreme)
  have right:
      "{b. pp_uniform_range_test
        pp_constant_operator_family pp_constant_operator_family b}
       = UNIV"
    using pp_uniform_range_test_self by blast
  have "{{} :: pp_sem_prop, UNIV} \<noteq> UNIV"
  proof
    assume equality: "{{} :: pp_sem_prop, UNIV} = UNIV"
    have subset:
        "(UNIV :: pp_sem_prop set) \<subseteq>
         {{}, (UNIV :: pp_sem_prop)}"
      using equality by blast
    have "{[]} \<in> (UNIV :: pp_sem_prop set)"
      by simp
    then have "{[]} \<in> {{}, (UNIV :: pp_sem_prop)}"
      using subset by blast
    then have "{[]} = ({} :: pp_sem_prop) \<or>
        {[]} = UNIV"
      by blast
    moreover have "{[]} \<noteq> ({} :: pp_sem_prop)"
      by simp
    moreover have "{[]} \<noteq> (UNIV :: pp_sem_prop)"
    proof
      assume singleton: "{[]} = (UNIV :: pp_sem_prop)"
      have "[0] \<in> (UNIV :: pp_sem_prop)"
        by simp
      then have "[0] \<in> {[] :: pp_word}"
        using singleton by simp
      then show False
        by simp
    qed
    ultimately show False
      by blast
  qed
  then show ?thesis
    using left right by simp
qed

subsection \<open>A root-empty fibre need not give the false invariant operator\<close>

definition pp_lifted_universal :: pp_sem_prop where
  "pp_lifted_universal = pp_lift [0] UNIV"

lemma pp_lifted_universal_view[simp]:
  "pp_view [0] pp_lifted_universal = UNIV"
  by (simp add: pp_lifted_universal_def)

lemma pp_lifted_universal_not_level_class:
  assumes p: "0 < p"
  shows "pp_lifted_universal \<noteq> pp_level_class p r"
proof
  assume equality:
      "pp_lifted_universal = pp_level_class p r"
  have zero_mem: "[0] \<in> pp_lifted_universal"
    by (auto simp: pp_lifted_universal_def pp_lift_def)
  have one_not_mem: "[1] \<notin> pp_lifted_universal"
    by (auto simp: pp_lifted_universal_def pp_lift_def)
  have "[0] \<in> pp_level_class p r"
    using zero_mem equality by simp
  then have "[1] \<in> pp_level_class p r"
    by (simp add: pp_level_class_def)
  then show False
    using one_not_mem equality by simp
qed

lemma pp_cyc_rel_lifted_universal_false:
  "\<not> pp_cyc_rel pp_lifted_universal c"
proof
  assume relation: "pp_cyc_rel pp_lifted_universal c"
  then obtain Z where
      cyclic: "pp_cyclic_level_partition Z"
      and lifted_mem: "pp_lifted_universal \<in> Z"
    unfolding pp_cyc_rel_def by blast
  obtain p where p: "0 < p"
      and Z: "Z = pp_level_partition p"
    using cyclic pp_cyclic_level_partition_iff by blast
  obtain r where r: "r < p"
      and lifted: "pp_lifted_universal = pp_level_class p r"
    using lifted_mem Z unfolding pp_level_partition_def by blast
  show False
    using pp_lifted_universal_not_level_class[OF p] lifted by blast
qed

lemma pp_cyc_rel_universal:
  "pp_cyc_rel UNIV UNIV"
proof -
  show ?thesis
    unfolding pp_cyc_rel_def
  proof (rule exI[of _ "pp_level_partition 1"])
    show "pp_cyclic_level_partition (pp_level_partition 1) \<and>
          UNIV \<in> pp_level_partition 1 \<and>
          UNIV \<in> pp_level_partition 1"
      using pp_level_partition_cyclic[of 1]
      by (simp add: pp_level_partition_def pp_level_class_def)
  qed
qed

lemma pp_cyc_family_member:
  "pp_function_space_member (pp_cyc_family b)"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix i P Q
  assume views: "pp_view i P = pp_view i Q"
  have "pp_view i (pp_cyc_family b P) =
      pp_cyc_family (pp_view i b) (pp_view i P)"
    by (rule pp_cyc_family_equivariant)
  also have "... =
      pp_cyc_family (pp_view i b) (pp_view i Q)"
    using views by simp
  also have "... = pp_view i (pp_cyc_family b Q)"
    by (rule pp_cyc_family_equivariant[symmetric])
  finally show
      "pp_view i (pp_cyc_family b P) =
       pp_view i (pp_cyc_family b Q)" .
qed

theorem pp_cyc_family_lifted_universal_not_invariant:
  "\<not> pp_fun_invariant
    (pp_cyc_family pp_lifted_universal)"
proof
  assume invariant:
      "pp_fun_invariant
        (pp_cyc_family pp_lifted_universal)"
  have equivariant:
      "pp_equivariant_operator
        (pp_cyc_family pp_lifted_universal)"
    using pp_fun_invariant_iff_equivariant[
        OF pp_cyc_family_member, of pp_lifted_universal]
      invariant by blast
  have action:
      "pp_view [0]
        (pp_cyc_family pp_lifted_universal
          pp_lifted_universal) =
       pp_cyc_family pp_lifted_universal
         (pp_view [0] pp_lifted_universal)"
    using equivariant
    unfolding pp_equivariant_operator_def by blast
  have left_root:
      "[] \<in> pp_view [0]
        (pp_cyc_family pp_lifted_universal
          pp_lifted_universal)"
    by (simp add: pp_view_membership_at_root
        pp_cyc_family_def pp_cyc_rel_universal)
  have right_not_root:
      "[] \<notin> pp_cyc_family pp_lifted_universal
        (pp_view [0] pp_lifted_universal)"
    by (simp add: pp_cyc_family_def
        pp_cyc_rel_lifted_universal_false)
  show False
    using action left_root right_not_root by simp
qed

subsection \<open>The exact invariant base of the cyclic family\<close>

definition pp_cyc_carrier :: "pp_sem_prop \<Rightarrow> bool" where
  "pp_cyc_carrier b \<longleftrightarrow> pp_cyc_rel b b"

lemma pp_cyc_rel_left_implies_carrier:
  assumes "pp_cyc_rel b c"
  shows "pp_cyc_carrier b"
  using assms unfolding pp_cyc_rel_def pp_cyc_carrier_def by blast

lemma pp_cyc_carrier_iff_level_class:
  "pp_cyc_carrier b \<longleftrightarrow>
    (\<exists>p r. 0 < p \<and> b = pp_level_class p r)"
proof
  assume carrier: "pp_cyc_carrier b"
  then obtain Z where
      cyclic: "pp_cyclic_level_partition Z"
      and b_mem: "b \<in> Z"
    unfolding pp_cyc_carrier_def pp_cyc_rel_def by blast
  obtain p where p: "0 < p"
      and Z: "Z = pp_level_partition p"
    using cyclic pp_cyclic_level_partition_iff by blast
  obtain r where "b = pp_level_class p r"
    using b_mem Z unfolding pp_level_partition_def by blast
  then show "\<exists>p r. 0 < p \<and> b = pp_level_class p r"
    using p by blast
next
  assume "\<exists>p r. 0 < p \<and> b = pp_level_class p r"
  then obtain p r where p: "0 < p"
      and b: "b = pp_level_class p r"
    by blast
  have cyclic:
      "pp_cyclic_level_partition (pp_level_partition p)"
    using p by (rule pp_level_partition_cyclic)
  have member:
      "b \<in> pp_level_partition p"
    using p b pp_level_class_in_partition by blast
  show "pp_cyc_carrier b"
    unfolding pp_cyc_carrier_def pp_cyc_rel_def
    using cyclic member by blast
qed

lemma pp_cyc_family_empty_if_orbit_avoids_carrier:
  assumes avoids:
      "\<And>i. \<not> pp_cyc_carrier (pp_view i b)"
  shows "pp_cyc_family b c = {}"
proof (rule set_eqI)
  fix i
  have "\<not> pp_cyc_rel (pp_view i b) (pp_view i c)"
    using avoids[of i] pp_cyc_rel_left_implies_carrier by blast
  then show "i \<in> pp_cyc_family b c \<longleftrightarrow> i \<in> {}"
    by (simp add: pp_cyc_family_def)
qed

theorem pp_cyc_family_invariant_iff:
  "pp_fun_invariant (pp_cyc_family b) \<longleftrightarrow>
    pp_cyc_carrier b \<or>
    (\<forall>i. \<not> pp_cyc_carrier (pp_view i b))"
proof
  assume invariant: "pp_fun_invariant (pp_cyc_family b)"
  show "pp_cyc_carrier b \<or>
      (\<forall>i. \<not> pp_cyc_carrier (pp_view i b))"
  proof (cases "pp_cyc_carrier b")
    case True
    then show ?thesis by blast
  next
    case False
    have equivariant:
        "pp_equivariant_operator (pp_cyc_family b)"
      using pp_fun_invariant_iff_equivariant[
          OF pp_cyc_family_member, of b]
        invariant by blast
    have no_root_relation:
        "\<And>c. \<not> pp_cyc_rel b c"
      using False pp_cyc_rel_left_implies_carrier by blast
    have "\<not> pp_cyc_carrier (pp_view i b)" for i
    proof
      assume future: "pp_cyc_carrier (pp_view i b)"
      let ?d = "pp_view i b"
      let ?c = "pp_lift i ?d"
      have future_relation:
          "pp_cyc_rel (pp_view i b) (pp_view i ?c)"
        using future
        by (simp add: pp_cyc_carrier_def)
      then have future_truth:
          "[] \<in> pp_view i (pp_cyc_family b ?c)"
        by (simp add: pp_view_membership_at_root
            pp_cyc_family_def)
      have action:
          "pp_view i (pp_cyc_family b ?c) =
           pp_cyc_family b (pp_view i ?c)"
        using equivariant
        unfolding pp_equivariant_operator_def by blast
      have "[] \<notin> pp_cyc_family b (pp_view i ?c)"
        using no_root_relation[of "pp_view i ?c"]
        by (simp add: pp_cyc_family_def)
      then show False
        using action future_truth by simp
    qed
    then show ?thesis by blast
  qed
next
  assume condition:
      "pp_cyc_carrier b \<or>
       (\<forall>i. \<not> pp_cyc_carrier (pp_view i b))"
  then show "pp_fun_invariant (pp_cyc_family b)"
  proof
    assume carrier: "pp_cyc_carrier b"
    obtain p r where p: "0 < p"
        and b: "b = pp_level_class p r"
      using carrier pp_cyc_carrier_iff_level_class by blast
    show ?thesis
      using p b pp_cyc_family_value_invariant by blast
  next
    assume avoids:
        "\<forall>i. \<not> pp_cyc_carrier (pp_view i b)"
    have empty: "pp_cyc_family b c = {}" for c
      using avoids pp_cyc_family_empty_if_orbit_avoids_carrier
      by blast
    have equivariant:
        "pp_equivariant_operator (pp_cyc_family b)"
      unfolding pp_equivariant_operator_def
      using empty by (simp add: pp_view_def)
    show ?thesis
      using pp_fun_invariant_iff_equivariant[
          OF pp_cyc_family_member, of b]
        equivariant by blast
  qed
qed

text \<open>
  The right-hand side is the semantic reading of the Pure-free formula

    \<open>CycCarrier(b) \<or> \<box> \<not> CycCarrier(b)\<close>,

  where \<open>CycCarrier(b)\<close> abbreviates
  \<open>\<exists>Z. CycPart(Z) \<and> Z b\<close>.  Thus the cyclic family refutes FIN-base,
  but it is not a counterexample to the desired base-definability claim: its
  invariant base is itself Pure-free definable.  What failed was only the
  stronger identification of that base with the level classes alone.
\<close>

text \<open>
  Thus a sound uniform-index lemma needs a further range condition: every
  value \<open>K a\<close> admitted by the existential must already be an invariant member
  of the intended logical stock (or the formula must separately express that
  condition).  Merely exhausting the invariant logical values of \<open>Y\<close> is not
  enough.
\<close>

end
