theory Bacon_PP_ZF_Tree_Quotient_Diagonal
  imports Bacon_PP_ZF_Tree_Ambient_Inverse
begin

section \<open>The root-semantic quotient diagonal\<close>

text \<open>
  This section isolates the combinatorial core of the proposed quotient
  diagonal.  The proposition type, operator type, application operation, and
  root-truth predicate remain parameters.  In the tree model they are
  instantiated by the root quotients of @{term "pp_t_domain Prop"} and
  @{term "pp_t_domain pp_t_unary_type"}.
\<close>

definition pp_qd_separator ::
  "('i \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> bool"
where
  "pp_qd_separator E ap p \<longleftrightarrow>
    (\<forall>x y. E x \<noteq> E y \<longrightarrow> ap (E x) p \<noteq> ap (E y) p)"

definition pp_qd_representation ::
  "('i \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'i \<Rightarrow> bool"
where
  "pp_qd_representation E ap H q p x \<longleftrightarrow>
    pp_qd_separator E ap p \<and> q = H p (ap (E x) p)"

definition pp_qd_truth_congruent ::
  "('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow>
    ('p \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_qd_truth_congruent ap truth R \<longleftrightarrow>
    (\<forall>q F G. R q F G \<longrightarrow>
      truth (ap F q) = truth (ap G q))"

definition pp_qd_diagonal ::
  "('i \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
    ('p \<Rightarrow> bool) \<Rightarrow> 'f \<Rightarrow> bool"
where
  "pp_qd_diagonal E ap H R truth D \<longleftrightarrow>
    (\<forall>q. truth (ap D q) =
      (\<forall>p x.
        (pp_qd_representation E ap H q p x \<and>
          (\<forall>r y. pp_qd_representation E ap H q r y
            \<longrightarrow> R q (E y) (E x)))
        \<longrightarrow> \<not> truth (ap (E x) q)))"

definition pp_qd_tag ::
  "('i \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'i \<Rightarrow> 'p"
where
  "pp_qd_tag E ap H p x = H p (ap (E x) p)"

definition pp_qd_tag_homogeneous ::
  "('i \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
    ('p \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
    'p \<Rightarrow> 'i \<Rightarrow> bool"
where
  "pp_qd_tag_homogeneous E ap H R p x \<longleftrightarrow>
    (\<forall>r y.
      pp_qd_representation E ap H (pp_qd_tag E ap H p x) r y
      \<longrightarrow> R (pp_qd_tag E ap H p x) (E y) (E x))"

lemma pp_qd_own_representation:
  assumes sep: "pp_qd_separator E ap p"
  shows "pp_qd_representation E ap H
    (pp_qd_tag E ap H p x) p x"
  using sep
  by (simp add: pp_qd_representation_def pp_qd_tag_def)

theorem pp_qd_absorption_forces_tag_heterogeneity:
  assumes diagonal: "pp_qd_diagonal E ap H R truth D"
    and congruent: "pp_qd_truth_congruent ap truth R"
    and absorbed: "E k = D"
    and separator: "pp_qd_separator E ap p"
  shows "\<not> pp_qd_tag_homogeneous E ap H R p k"
proof
  assume homogeneous: "pp_qd_tag_homogeneous E ap H R p k"
  let ?q = "pp_qd_tag E ap H p k"
  have own: "pp_qd_representation E ap H ?q p k"
    using pp_qd_own_representation[OF separator] .
  have relation_class:
      "\<forall>r y. pp_qd_representation E ap H ?q r y
        \<longrightarrow> R ?q (E y) (E k)"
    using homogeneous
    by (simp add: pp_qd_tag_homogeneous_def)
  have diagonal_at:
      "truth (ap D ?q) =
        (\<forall>r x.
          (pp_qd_representation E ap H ?q r x \<and>
            (\<forall>s y. pp_qd_representation E ap H ?q s y
              \<longrightarrow> R ?q (E y) (E x)))
          \<longrightarrow> \<not> truth (ap (E x) ?q))"
    using diagonal
    by (simp add: pp_qd_diagonal_def)
  have truth_congruence:
      "\<And>F G. R ?q F G \<Longrightarrow>
        truth (ap F ?q) = truth (ap G ?q)"
    using congruent
    by (simp add: pp_qd_truth_congruent_def)
  show False
  proof (cases "truth (ap (E k) ?q)")
    case True
    have rhs:
        "\<forall>r x.
          (pp_qd_representation E ap H ?q r x \<and>
            (\<forall>s y. pp_qd_representation E ap H ?q s y
              \<longrightarrow> R ?q (E y) (E x)))
          \<longrightarrow> \<not> truth (ap (E x) ?q)"
      using diagonal_at absorbed True by simp
    then have "\<not> truth (ap (E k) ?q)"
      using own relation_class by blast
    then show False using True by contradiction
  next
    case False
    have every_rep_false:
        "\<And>r x. pp_qd_representation E ap H ?q r x
          \<Longrightarrow> \<not> truth (ap (E x) ?q)"
    proof -
      fix r x
      assume rep: "pp_qd_representation E ap H ?q r x"
      have related: "R ?q (E x) (E k)"
        using relation_class rep by blast
      have "truth (ap (E x) ?q) = truth (ap (E k) ?q)"
        by (rule truth_congruence[OF related])
      then show "\<not> truth (ap (E x) ?q)"
        using False by simp
    qed
    have rhs:
        "\<forall>r x.
          (pp_qd_representation E ap H ?q r x \<and>
            (\<forall>s y. pp_qd_representation E ap H ?q s y
              \<longrightarrow> R ?q (E y) (E x)))
          \<longrightarrow> \<not> truth (ap (E x) ?q)"
      using every_rep_false by blast
    have "truth (ap (E k) ?q)"
      using diagonal_at absorbed rhs by simp
    then show False using False by contradiction
  qed
qed

corollary pp_qd_no_homogeneous_absorbed_diagonal:
  assumes diagonal: "pp_qd_diagonal E ap H R truth D"
    and congruent: "pp_qd_truth_congruent ap truth R"
    and absorbed: "E k = D"
    and separator: "pp_qd_separator E ap p"
    and homogeneous: "pp_qd_tag_homogeneous E ap H R p k"
  shows False
  using pp_qd_absorption_forces_tag_heterogeneity[
    OF diagonal congruent absorbed separator] homogeneous by blast

section \<open>Finite-observational relations\<close>

definition pp_qd_finite_observational ::
  "('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow>
    ('p \<Rightarrow> 'p set) \<Rightarrow> 'p \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
where
  "pp_qd_finite_observational ap truth Obs q F G \<longleftrightarrow>
    (\<forall>r \<in> Obs q. truth (ap F r) = truth (ap G r))"

lemma pp_qd_finite_observational_truth_congruent:
  assumes self_observed: "\<And>q. q \<in> Obs q"
  shows "pp_qd_truth_congruent ap truth
    (pp_qd_finite_observational ap truth Obs)"
  using self_observed
  by (auto simp: pp_qd_truth_congruent_def
      pp_qd_finite_observational_def)

lemma pp_qd_finite_observational_is_finite:
  assumes finite: "\<And>q. finite (Obs q)"
  shows "finite (Obs q)"
  using finite .

section \<open>Stabilizer-orbit relations\<close>

definition pp_qd_stabilizer_orbit ::
  "('f \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
where
  "pp_qd_stabilizer_orbit ap q F G \<longleftrightarrow>
    (\<exists>\<psi>. bij \<psi> \<and> \<psi> q = q \<and> (\<forall>r. ap F r = ap G (\<psi> r)))"

lemma pp_qd_stabilizer_orbit_truth_congruent:
  "pp_qd_truth_congruent ap truth (pp_qd_stabilizer_orbit ap)"
  by (auto simp: pp_qd_truth_congruent_def
      pp_qd_stabilizer_orbit_def)

section \<open>A concrete two-point tag test\<close>

definition pp_qd_bool_E :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "pp_qd_bool_E i p = (if i then \<not> p else p)"

definition pp_qd_bool_H :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "pp_qd_bool_H p z = z"

definition pp_qd_bool_Obs :: "bool \<Rightarrow> bool set"
where
  "pp_qd_bool_Obs q = {q}"

lemma pp_qd_bool_separator:
  "pp_qd_separator pp_qd_bool_E (\<lambda>F p. F p) p"
  by (auto simp: pp_qd_separator_def pp_qd_bool_E_def
      fun_eq_iff split: if_splits)

lemma pp_qd_bool_base_tag:
  "pp_qd_tag pp_qd_bool_E (\<lambda>F p. F p)
      pp_qd_bool_H False False = False"
  by (simp add: pp_qd_tag_def pp_qd_bool_E_def pp_qd_bool_H_def)

lemma pp_qd_bool_alternate_representation:
  "pp_qd_representation pp_qd_bool_E (\<lambda>F p. F p)
    pp_qd_bool_H False True True"
  using pp_qd_bool_separator[of True]
  by (simp add: pp_qd_representation_def pp_qd_bool_E_def
      pp_qd_bool_H_def)

lemma pp_qd_bool_observational_relation_separates_representatives:
  "\<not> pp_qd_finite_observational (\<lambda>F p. F p) id
    pp_qd_bool_Obs False
    (pp_qd_bool_E True) (pp_qd_bool_E False)"
  by (simp add: pp_qd_finite_observational_def pp_qd_bool_Obs_def
      pp_qd_bool_E_def)

theorem pp_qd_bool_observational_tag_not_homogeneous:
  "\<not> pp_qd_tag_homogeneous pp_qd_bool_E (\<lambda>F p. F p)
    pp_qd_bool_H
    (pp_qd_finite_observational (\<lambda>F p. F p) id
      pp_qd_bool_Obs)
    False False"
  using pp_qd_bool_alternate_representation
    pp_qd_bool_observational_relation_separates_representatives
  by (auto simp: pp_qd_tag_homogeneous_def pp_qd_bool_base_tag)

lemma pp_qd_bool_stabilizer_relation_separates_representatives:
  "\<not> pp_qd_stabilizer_orbit (\<lambda>F p. F p) False
    (pp_qd_bool_E True) (pp_qd_bool_E False)"
proof
  assume orbit:
      "pp_qd_stabilizer_orbit (\<lambda>F p. F p) False
        (pp_qd_bool_E True) (pp_qd_bool_E False)"
  then obtain \<psi> where fixed: "\<psi> False = False"
    and action:
      "\<forall>r. pp_qd_bool_E True r = pp_qd_bool_E False (\<psi> r)"
    by (auto simp: pp_qd_stabilizer_orbit_def)
  have "pp_qd_bool_E True False =
      pp_qd_bool_E False (\<psi> False)"
    using action by blast
  then show False
    using fixed by (simp add: pp_qd_bool_E_def)
qed

theorem pp_qd_bool_stabilizer_tag_not_homogeneous:
  "\<not> pp_qd_tag_homogeneous pp_qd_bool_E (\<lambda>F p. F p)
    pp_qd_bool_H
    (pp_qd_stabilizer_orbit (\<lambda>F p. F p))
    False False"
  using pp_qd_bool_alternate_representation
    pp_qd_bool_stabilizer_relation_separates_representatives
  by (auto simp: pp_qd_tag_homogeneous_def pp_qd_bool_base_tag)

end
