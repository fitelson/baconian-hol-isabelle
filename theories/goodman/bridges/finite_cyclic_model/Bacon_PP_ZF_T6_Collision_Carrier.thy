theory Bacon_PP_ZF_T6_Collision_Carrier
  imports
    Bacon_PP_ZF_Two_Component_Assembly
    Higher_Order_Metaphysics_PP_ZF_T6_Diagonal.Bacon_PP_ZF_T6_Builder_Enlargement
begin

section \<open>Iterating the T6 classifier-bearing component\<close>

text \<open>
  The old T6 calculation asks whether the value of the logical purity
  builder at the ten-class classifier is already represented by one of
  those ten classes.  Failure of that equation does not by itself refute a
  model construction: one may add the new value, rebuild the classifier,
  and repeat.  The following recursion states that enlargement exactly.
\<close>

primrec pp_t_T6_iterated_unary_pure ::
    "nat \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_T6_iterated_unary_pure 0 =
    pp_t_T6_diagonal_unary_pure"
| "pp_t_T6_iterated_unary_pure (Suc n) =
    (\<lambda>w X.
      pp_t_T6_iterated_unary_pure n w X
      \<or> pp_t_eqv pp_t_constants_unary_type w
        (pp_t_T6_purity_builder_den \<acute>
          pp_t_classifier pp_t_constants_unary_type
            (pp_t_T6_iterated_unary_pure n))
        X)"

definition pp_t_T6_iterated_classifier :: "nat \<Rightarrow> ZF"
where
  "pp_t_T6_iterated_classifier n =
    pp_t_classifier pp_t_constants_unary_type
      (pp_t_T6_iterated_unary_pure n)"

definition pp_t_T6_iterated_diagonal :: "nat \<Rightarrow> ZF"
where
  "pp_t_T6_iterated_diagonal n =
    pp_t_T6_purity_builder_den \<acute>
      pp_t_T6_iterated_classifier n"

lemma pp_t_T6_iterated_unary_pure_Suc:
  "pp_t_T6_iterated_unary_pure (Suc n) w X
    \<longleftrightarrow>
    pp_t_T6_iterated_unary_pure n w X
    \<or> pp_t_eqv pp_t_constants_unary_type w
      (pp_t_T6_iterated_diagonal n) X"
  unfolding pp_t_T6_iterated_diagonal_def
    pp_t_T6_iterated_classifier_def
  by simp

theorem pp_t_T6_iterated_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    (pp_t_T6_iterated_unary_pure n)"
proof (induction n)
  case 0
  show ?case
    by simp (rule pp_t_T6_diagonal_unary_pure_admissible)
next
  case (Suc n)
  have classifier:
      "Elem (pp_t_T6_iterated_classifier n)
        (pp_t_domain pp_t_constants_classifier_type)"
    unfolding pp_t_T6_iterated_classifier_def
    by (rule pp_t_classifier_in_domain) (rule Suc.IH)
  have diagonal:
      "Elem (pp_t_T6_iterated_diagonal n)
        (pp_t_domain pp_t_constants_unary_type)"
    unfolding pp_t_T6_iterated_diagonal_def
    by (rule pp_t_app_closed[
      OF pp_t_T6_purity_builder_den_in_domain classifier])
  have added:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_constants_unary_type w
          (pp_t_T6_iterated_diagonal n) X)"
    by (rule pp_t_eqv_classifier_admissible[OF diagonal])
  show ?case
    unfolding pp_t_predicate_admissible_def
      pp_t_T6_iterated_unary_pure_Suc
    using Suc.IH added
    unfolding pp_t_predicate_admissible_def
    by blast
qed

lemma pp_t_T6_iterated_classifier_in_domain:
  "Elem (pp_t_T6_iterated_classifier n)
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_T6_iterated_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_T6_iterated_unary_pure_admissible)

lemma pp_t_T6_iterated_classifier_holds:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
  shows "pp_t_holds
      (pp_t_T6_iterated_classifier n \<acute> X) w
    \<longleftrightarrow>
    pp_t_T6_iterated_unary_pure n w X"
  unfolding pp_t_T6_iterated_classifier_def
  by (rule pp_t_classifier_holds[OF X])

lemma pp_t_T6_iterated_diagonal_in_domain:
  "Elem (pp_t_T6_iterated_diagonal n)
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_T6_iterated_diagonal_def
  by (rule pp_t_app_closed[
    OF pp_t_T6_purity_builder_den_in_domain
      pp_t_T6_iterated_classifier_in_domain])

lemma pp_t_T6_iterated_unary_pure_mono:
  "pp_t_T6_iterated_unary_pure n w X
    \<Longrightarrow> pp_t_T6_iterated_unary_pure (Suc n) w X"
  unfolding pp_t_T6_iterated_unary_pure_Suc
  by blast

lemma pp_t_T6_iterated_diagonal_added:
  "pp_t_T6_iterated_unary_pure (Suc n) w
    (pp_t_T6_iterated_diagonal n)"
  unfolding pp_t_T6_iterated_unary_pure_Suc
  using pp_t_eqv_reflexive[
    OF pp_t_T6_iterated_diagonal_in_domain, of w]
  by blast

subsection \<open>Finite representatives at every finite stage\<close>

primrec pp_t_T6_iterated_representatives :: "nat \<Rightarrow> ZF set"
where
  "pp_t_T6_iterated_representatives 0 =
    pp_t_T6_ten_representatives"
| "pp_t_T6_iterated_representatives (Suc n) =
    insert (pp_t_T6_iterated_diagonal n)
      (pp_t_T6_iterated_representatives n)"

lemma pp_t_T6_iterated_representatives_finite:
  "finite (pp_t_T6_iterated_representatives n)"
  by (induction n)
    (simp_all add: pp_t_T6_ten_representatives_finite)

lemma pp_t_T6_iterated_representative_in_domain:
  assumes "A \<in> pp_t_T6_iterated_representatives n"
  shows "Elem A (pp_t_domain pp_t_constants_unary_type)"
proof -
  have all:
      "\<forall>A \<in> pp_t_T6_iterated_representatives n.
        Elem A (pp_t_domain pp_t_constants_unary_type)"
  proof (induction n)
    case 0
    show ?case
      using pp_t_T6_ten_representative_in_domain
      by simp
  next
    case (Suc n)
    show ?case
      using Suc.IH
        pp_t_T6_iterated_diagonal_in_domain[of n]
      by auto
  qed
  show ?thesis using all assms by blast
qed

theorem pp_t_T6_iterated_unary_pure_iff_represented:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
  shows "pp_t_T6_iterated_unary_pure n w X
    \<longleftrightarrow>
    (\<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_eqv pp_t_constants_unary_type w A X)"
proof (induction n)
  case 0
  show ?case
  proof
    assume pure:
        "pp_t_T6_iterated_unary_pure 0 w X"
    then have old:
        "pp_t_T6_diagonal_unary_pure w X"
      by simp
    obtain A where
        A: "A \<in> pp_t_T6_ten_representatives"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type w A X"
      using pp_t_T6_ten_representative[OF old]
      by blast
    show "\<exists>A \<in> pp_t_T6_iterated_representatives 0.
        pp_t_eqv pp_t_constants_unary_type w A X"
    proof (rule bexI[of _ A])
      show "pp_t_eqv pp_t_constants_unary_type w A X"
        by (rule AX)
      show "A \<in> pp_t_T6_iterated_representatives 0"
        using A by simp
    qed
  next
    assume represented:
        "\<exists>A \<in> pp_t_T6_iterated_representatives 0.
          pp_t_eqv pp_t_constants_unary_type w A X"
    then obtain A where
        A: "A \<in> pp_t_T6_ten_representatives"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type w A X"
      by auto
    have A_domain:
        "Elem A (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_T6_ten_representative_in_domain[OF A])
    have AA:
        "pp_t_eqv pp_t_constants_unary_type w A A"
      by (rule pp_t_eqv_reflexive[OF A_domain])
    have pure_A:
        "pp_t_T6_diagonal_unary_pure w A"
      using A AA
      unfolding pp_t_T6_ten_representatives_def
        pp_t_T6_diagonal_unary_pure_def
        pp_t_fun_prime_unary_pure_def
        pp_t_quantified_unary_pure_classes
      by blast
    have transfer:
        "pp_t_T6_diagonal_unary_pure w A
          = pp_t_T6_diagonal_unary_pure w X"
      using pp_t_T6_diagonal_unary_pure_admissible
        A_domain X AX
      unfolding pp_t_predicate_admissible_def
      by blast
    show "pp_t_T6_iterated_unary_pure 0 w X"
      using pure_A transfer by simp
  qed
next
  case (Suc n)
  show ?case
    unfolding pp_t_T6_iterated_unary_pure_Suc
  proof
    assume new:
        "pp_t_T6_iterated_unary_pure n w X
        \<or> pp_t_eqv pp_t_constants_unary_type w
          (pp_t_T6_iterated_diagonal n) X"
    show "\<exists>A \<in> pp_t_T6_iterated_representatives (Suc n).
        pp_t_eqv pp_t_constants_unary_type w A X"
      using new
    proof
      assume old:
          "pp_t_T6_iterated_unary_pure n w X"
      obtain A where
          A: "A \<in> pp_t_T6_iterated_representatives n"
        and AX:
          "pp_t_eqv pp_t_constants_unary_type w A X"
        using Suc.IH old by blast
      show ?thesis
      proof (rule bexI[of _ A])
        show "pp_t_eqv pp_t_constants_unary_type w A X"
          by (rule AX)
        show "A \<in> pp_t_T6_iterated_representatives (Suc n)"
          using A by simp
      qed
    next
      assume added:
          "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_T6_iterated_diagonal n) X"
      show ?thesis
      proof (rule bexI[of _ "pp_t_T6_iterated_diagonal n"])
        show "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_T6_iterated_diagonal n) X"
          by (rule added)
        show "pp_t_T6_iterated_diagonal n
            \<in> pp_t_T6_iterated_representatives (Suc n)"
          by simp
      qed
    qed
  next
    assume represented:
        "\<exists>A \<in> pp_t_T6_iterated_representatives (Suc n).
          pp_t_eqv pp_t_constants_unary_type w A X"
    then obtain A where
        A: "A \<in> pp_t_T6_iterated_representatives (Suc n)"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type w A X"
      by blast
    have alternatives:
        "A = pp_t_T6_iterated_diagonal n
          \<or> A \<in> pp_t_T6_iterated_representatives n"
      using A by simp
    show "pp_t_T6_iterated_unary_pure n w X
      \<or> pp_t_eqv pp_t_constants_unary_type w
        (pp_t_T6_iterated_diagonal n) X"
      using alternatives
    proof
      assume equality: "A = pp_t_T6_iterated_diagonal n"
      then show ?thesis using AX by simp
    next
      assume member:
          "A \<in> pp_t_T6_iterated_representatives n"
      have "pp_t_T6_iterated_unary_pure n w X"
        using Suc.IH member AX by blast
      then show ?thesis by blast
    qed
  qed
qed

subsection \<open>The exact finite-stage stopping test\<close>

definition pp_t_T6_stage_stable :: "nat \<Rightarrow> bool"
where
  "pp_t_T6_stage_stable n \<longleftrightarrow>
    (\<forall>w X.
      Elem X (pp_t_domain pp_t_constants_unary_type)
      \<longrightarrow>
      (pp_t_T6_iterated_unary_pure (Suc n) w X
        \<longleftrightarrow>
       pp_t_T6_iterated_unary_pure n w X))"

theorem pp_t_T6_stage_stable_iff_diagonal_absorbed:
  "pp_t_T6_stage_stable n
    \<longleftrightarrow>
    (\<forall>w. pp_t_T6_iterated_unary_pure n w
      (pp_t_T6_iterated_diagonal n))"
proof
  assume stable: "pp_t_T6_stage_stable n"
  show "\<forall>w. pp_t_T6_iterated_unary_pure n w
      (pp_t_T6_iterated_diagonal n)"
  proof
    fix w
    have next_stage:
        "pp_t_T6_iterated_unary_pure (Suc n) w
          (pp_t_T6_iterated_diagonal n)"
      by (rule pp_t_T6_iterated_diagonal_added)
    show "pp_t_T6_iterated_unary_pure n w
        (pp_t_T6_iterated_diagonal n)"
      using stable next_stage pp_t_T6_iterated_diagonal_in_domain
      unfolding pp_t_T6_stage_stable_def
      by blast
  qed
next
  assume absorbed:
      "\<forall>w. pp_t_T6_iterated_unary_pure n w
        (pp_t_T6_iterated_diagonal n)"
  show "pp_t_T6_stage_stable n"
    unfolding pp_t_T6_stage_stable_def
  proof (intro allI impI)
    fix w X
    assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    show "pp_t_T6_iterated_unary_pure (Suc n) w X
      \<longleftrightarrow>
      pp_t_T6_iterated_unary_pure n w X"
    proof
      assume at_next_stage:
          "pp_t_T6_iterated_unary_pure (Suc n) w X"
      then consider
          (old) "pp_t_T6_iterated_unary_pure n w X"
        | (added) "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_T6_iterated_diagonal n) X"
        unfolding pp_t_T6_iterated_unary_pure_Suc
        by blast
      then show "pp_t_T6_iterated_unary_pure n w X"
      proof cases
        case old
        then show ?thesis .
      next
        case added
        have equality:
            "pp_t_T6_iterated_unary_pure n w
                (pp_t_T6_iterated_diagonal n)
              =
             pp_t_T6_iterated_unary_pure n w X"
          using pp_t_T6_iterated_unary_pure_admissible[of n]
            pp_t_T6_iterated_diagonal_in_domain X added
          unfolding pp_t_predicate_admissible_def
          by blast
        show ?thesis using absorbed[rule_format, of w] equality
          by simp
      qed
    next
      assume old: "pp_t_T6_iterated_unary_pure n w X"
      show "pp_t_T6_iterated_unary_pure (Suc n) w X"
        by (rule pp_t_T6_iterated_unary_pure_mono[OF old])
    qed
  qed
qed

corollary pp_t_T6_stage_stable_iff_represented:
  "pp_t_T6_stage_stable n
    \<longleftrightarrow>
    (\<forall>w. \<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_eqv pp_t_constants_unary_type w A
        (pp_t_T6_iterated_diagonal n))"
  unfolding pp_t_T6_stage_stable_iff_diagonal_absorbed
  using pp_t_T6_iterated_unary_pure_iff_represented[
    OF pp_t_T6_iterated_diagonal_in_domain]
  by blast

lemma pp_t_T6_iterated_classifier_zero:
  "pp_t_T6_iterated_classifier 0 =
    pp_t_T6_diagonal_stock_classifier"
  unfolding pp_t_T6_iterated_classifier_def
    pp_t_T6_diagonal_stock_classifier_def
  by simp

lemma pp_t_T6_iterated_diagonal_zero:
  "pp_t_T6_iterated_diagonal 0 =
    pp_t_T6_diagonal_T6_operator"
  unfolding pp_t_T6_iterated_diagonal_def
    pp_t_T6_iterated_classifier_zero
  by (rule pp_t_T6_purity_builder_applied_to_classifier)

theorem pp_t_T6_stage_zero_is_old_single_equation:
  "pp_t_T6_stage_stable 0
    \<longleftrightarrow>
    pp_t_T6_diagonal_T6_operator =
      pp_t_fun_prime_T6_operator"
proof -
  have absorption:
      "pp_t_T6_stage_stable 0
        \<longleftrightarrow>
       pp_t_T6_recomputed_diagonal_absorbed"
    unfolding pp_t_T6_stage_stable_iff_diagonal_absorbed
      pp_t_T6_recomputed_diagonal_absorbed_def
      pp_t_T6_iterated_diagonal_zero
    using pp_t_T6_diagonal_pure_unary_iff
    by simp
  show ?thesis
    using absorption
      pp_t_T6_recomputed_diagonal_absorbed_iff_old_diagonal
    by blast
qed

theorem pp_t_T6_unstable_stage_strictly_enlarges_representatives:
  assumes unstable: "\<not> pp_t_T6_stage_stable n"
  shows "pp_t_T6_iterated_representatives n
    \<subset> pp_t_T6_iterated_representatives (Suc n)"
proof -
  have not_member:
      "pp_t_T6_iterated_diagonal n
        \<notin> pp_t_T6_iterated_representatives n"
  proof
    assume member:
        "pp_t_T6_iterated_diagonal n
          \<in> pp_t_T6_iterated_representatives n"
    have absorbed:
        "\<forall>w. pp_t_T6_iterated_unary_pure n w
          (pp_t_T6_iterated_diagonal n)"
    proof
      fix w
      show "pp_t_T6_iterated_unary_pure n w
          (pp_t_T6_iterated_diagonal n)"
        unfolding pp_t_T6_iterated_unary_pure_iff_represented[
          OF pp_t_T6_iterated_diagonal_in_domain]
        using member pp_t_eqv_reflexive[
          OF pp_t_T6_iterated_diagonal_in_domain, of w]
        by blast
    qed
    have stable: "pp_t_T6_stage_stable n"
      using absorbed
        pp_t_T6_stage_stable_iff_diagonal_absorbed
      by blast
    show False using unstable stable by blast
  qed
  have subset:
      "pp_t_T6_iterated_representatives n
        \<subseteq> pp_t_T6_iterated_representatives (Suc n)"
    unfolding pp_t_T6_iterated_representatives.simps
    by (rule subset_insertI)
  have unequal:
      "pp_t_T6_iterated_representatives n
        \<noteq> pp_t_T6_iterated_representatives (Suc n)"
    using not_member by auto
  show ?thesis
    using subset unequal by blast
qed

corollary pp_t_T6_unstable_stage_cardinality_increases:
  assumes "\<not> pp_t_T6_stage_stable n"
  shows "card (pp_t_T6_iterated_representatives (Suc n))
    = Suc (card (pp_t_T6_iterated_representatives n))"
proof -
  have proper:
      "pp_t_T6_iterated_representatives n
        \<subset> pp_t_T6_iterated_representatives (Suc n)"
    by (rule
      pp_t_T6_unstable_stage_strictly_enlarges_representatives[
        OF assms])
  have not_member:
      "pp_t_T6_iterated_diagonal n
        \<notin> pp_t_T6_iterated_representatives n"
    using proper by auto
  show ?thesis
    using pp_t_T6_iterated_representatives_finite[of n]
      not_member
    by simp
qed

section \<open>The full finite-stage purity interpretation\<close>

definition pp_t_T6_iterated_fragment_pure ::
    "nat \<Rightarrow> otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_T6_iterated_fragment_pure n \<sigma> w x \<longleftrightarrow>
    (pp_t_T6_diagonal_fragment_pure \<sigma> w x
      \<and> \<sigma> \<noteq> pp_t_constants_unary_type
      \<and> \<sigma> \<noteq> pp_t_constants_classifier_type)
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> pp_t_T6_iterated_unary_pure n w x)
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type w
        (pp_t_T6_iterated_classifier n) x)"

theorem pp_t_T6_iterated_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_T6_iterated_fragment_pure n \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_T6_diagonal_fragment_pure \<sigma>)"
    by (rule pp_t_T6_diagonal_fragment_pure_admissible)
  have unary:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (pp_t_T6_iterated_unary_pure n)"
    by (rule pp_t_T6_iterated_unary_pure_admissible)
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type w
          (pp_t_T6_iterated_classifier n) x)"
    by (rule pp_t_eqv_classifier_admissible[
      OF pp_t_T6_iterated_classifier_in_domain])
  show ?thesis
    unfolding pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_eqv \<sigma> w x y"
      and future: "prefix w v"
    have old_iff:
        "pp_t_T6_diagonal_fragment_pure \<sigma> v x
          =
         pp_t_T6_diagonal_fragment_pure \<sigma> v y"
      using old x y xy future
      unfolding pp_t_predicate_admissible_def
      by blast
    have unary_iff:
        "\<sigma> = pp_t_constants_unary_type
        \<Longrightarrow>
        pp_t_T6_iterated_unary_pure n v x
          = pp_t_T6_iterated_unary_pure n v y"
      using unary x y xy future
      unfolding pp_t_predicate_admissible_def
      by blast
    have classifier_iff:
        "\<sigma> = pp_t_constants_classifier_type
        \<Longrightarrow>
        pp_t_eqv pp_t_constants_classifier_type v
            (pp_t_T6_iterated_classifier n) x
          =
        pp_t_eqv pp_t_constants_classifier_type v
            (pp_t_T6_iterated_classifier n) y"
      using classifier x y xy future
      unfolding pp_t_predicate_admissible_def
      by blast
    show "pp_t_T6_iterated_fragment_pure n \<sigma> v x
      = pp_t_T6_iterated_fragment_pure n \<sigma> v y"
      unfolding pp_t_T6_iterated_fragment_pure_def
      using old_iff unary_iff classifier_iff
      by blast
  qed
qed

lemma pp_t_T6_iterated_fragment_pure_unary_iff:
  "pp_t_T6_iterated_fragment_pure n
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_T6_iterated_unary_pure n w X"
  unfolding pp_t_T6_iterated_fragment_pure_def
  by simp

lemma pp_t_T6_iterated_fragment_pure_classifier_iff:
  "pp_t_T6_iterated_fragment_pure n
      pp_t_constants_classifier_type w C
    \<longleftrightarrow>
    pp_t_eqv pp_t_constants_classifier_type w
      (pp_t_T6_iterated_classifier n) C"
  unfolding pp_t_T6_iterated_fragment_pure_def
  by simp

theorem pp_t_T6_every_finite_stage_satisfies_PP:
  "pp_t_stock_self_classifies
    (pp_t_T6_iterated_fragment_pure n)"
proof -
  have unary:
      "pp_t_T6_iterated_fragment_pure n
          pp_t_constants_unary_type
        = pp_t_T6_iterated_unary_pure n"
    by (rule ext)+
      (simp add: pp_t_T6_iterated_fragment_pure_unary_iff)
  have classifier:
      "pp_t_classifier pp_t_constants_unary_type
          (pp_t_T6_iterated_fragment_pure n
            pp_t_constants_unary_type)
        = pp_t_T6_iterated_classifier n"
    unfolding unary pp_t_T6_iterated_classifier_def ..
  show ?thesis
    unfolding pp_t_stock_self_classifies_def
      pp_t_T6_iterated_fragment_pure_classifier_iff
      classifier
    using pp_t_eqv_reflexive[
      OF pp_t_T6_iterated_classifier_in_domain]
    by blast
qed

definition pp_t_T6_iterated_builder_application_closed ::
    "nat \<Rightarrow> bool"
where
  "pp_t_T6_iterated_builder_application_closed n
    \<longleftrightarrow>
    (\<forall>w f C.
      Elem f (pp_t_domain pp_t_T6_builder_type)
      \<longrightarrow>
      Elem C (pp_t_domain pp_t_constants_classifier_type)
      \<longrightarrow>
      pp_t_eqv pp_t_T6_builder_type w
        pp_t_T6_purity_builder_den f
      \<longrightarrow>
      pp_t_T6_iterated_fragment_pure n
        pp_t_constants_classifier_type w C
      \<longrightarrow>
      pp_t_T6_iterated_fragment_pure n
        pp_t_constants_unary_type w (f \<acute> C))"

theorem pp_t_T6_iterated_builder_application_closed_iff_stage_stable:
  "pp_t_T6_iterated_builder_application_closed n
    \<longleftrightarrow>
    pp_t_T6_stage_stable n"
proof
  assume closed:
      "pp_t_T6_iterated_builder_application_closed n"
  have absorbed:
      "\<forall>w. pp_t_T6_iterated_unary_pure n w
        (pp_t_T6_iterated_diagonal n)"
  proof
    fix w
    have builder_refl:
        "pp_t_eqv pp_t_T6_builder_type w
          pp_t_T6_purity_builder_den
          pp_t_T6_purity_builder_den"
      by (rule pp_t_eqv_reflexive[
        OF pp_t_T6_purity_builder_den_in_domain])
    have classifier_pure:
        "pp_t_T6_iterated_fragment_pure n
          pp_t_constants_classifier_type w
          (pp_t_T6_iterated_classifier n)"
      unfolding pp_t_T6_iterated_fragment_pure_classifier_iff
      by (rule pp_t_eqv_reflexive[
        OF pp_t_T6_iterated_classifier_in_domain])
    have application:
        "pp_t_T6_iterated_fragment_pure n
          pp_t_constants_unary_type w
          (pp_t_T6_purity_builder_den \<acute>
            pp_t_T6_iterated_classifier n)"
      using closed pp_t_T6_purity_builder_den_in_domain
        pp_t_T6_iterated_classifier_in_domain builder_refl
        classifier_pure
      unfolding
        pp_t_T6_iterated_builder_application_closed_def
      by blast
    show "pp_t_T6_iterated_unary_pure n w
        (pp_t_T6_iterated_diagonal n)"
      using application
      unfolding
        pp_t_T6_iterated_fragment_pure_unary_iff
        pp_t_T6_iterated_diagonal_def .
  qed
  show "pp_t_T6_stage_stable n"
    using absorbed pp_t_T6_stage_stable_iff_diagonal_absorbed
    by blast
next
  assume stable: "pp_t_T6_stage_stable n"
  have absorbed:
      "\<forall>w. pp_t_T6_iterated_unary_pure n w
        (pp_t_T6_iterated_diagonal n)"
    using stable pp_t_T6_stage_stable_iff_diagonal_absorbed
    by blast
  show "pp_t_T6_iterated_builder_application_closed n"
    unfolding
      pp_t_T6_iterated_builder_application_closed_def
  proof (intro allI impI)
    fix w f C
    assume f: "Elem f (pp_t_domain pp_t_T6_builder_type)"
      and C:
        "Elem C (pp_t_domain pp_t_constants_classifier_type)"
      and builder:
        "pp_t_eqv pp_t_T6_builder_type w
          pp_t_T6_purity_builder_den f"
      and pure_C:
        "pp_t_T6_iterated_fragment_pure n
          pp_t_constants_classifier_type w C"
    have classifier_rep:
        "pp_t_eqv pp_t_constants_classifier_type w
          (pp_t_T6_iterated_classifier n) C"
      using pure_C
      unfolding pp_t_T6_iterated_fragment_pure_classifier_iff .
    have applications:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_T6_purity_builder_den \<acute>
            pp_t_T6_iterated_classifier n)
          (f \<acute> C)"
      by (rule pp_t_app_respects[
        OF builder pp_t_T6_iterated_classifier_in_domain
          C classifier_rep])
    have result:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_T6_iterated_diagonal n) (f \<acute> C)"
      using applications
      unfolding pp_t_T6_iterated_diagonal_def .
    have fC:
        "Elem (f \<acute> C)
          (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_app_closed[OF f C])
    have transfer:
        "pp_t_T6_iterated_unary_pure n w
            (pp_t_T6_iterated_diagonal n)
          =
         pp_t_T6_iterated_unary_pure n w (f \<acute> C)"
      using pp_t_T6_iterated_unary_pure_admissible[of n]
        pp_t_T6_iterated_diagonal_in_domain fC result
      unfolding pp_t_predicate_admissible_def
      by blast
    show "pp_t_T6_iterated_fragment_pure n
        pp_t_constants_unary_type w (f \<acute> C)"
      unfolding pp_t_T6_iterated_fragment_pure_unary_iff
      using absorbed[rule_format, of w] transfer
      by simp
  qed
qed

corollary pp_t_T6_finite_stage_model_checkpoint:
  "pp_t_T6_iterated_builder_application_closed n
    \<longleftrightarrow>
    (pp_t_stock_self_classifies
        (pp_t_T6_iterated_fragment_pure n)
      \<and> pp_t_T6_stage_stable n)"
  using pp_t_T6_every_finite_stage_satisfies_PP
    pp_t_T6_iterated_builder_application_closed_iff_stage_stable
  by blast

section \<open>A stage-uniform truth condition for the generated diagonal\<close>

lemma pp_t_four_extensions_index_three[simp]:
  "extend_env a
      (extend_env b
        (extend_env c
          (extend_env d \<rho>))) 3 = d"
  by (simp add: eval_nat_numeral)

lemma pp_t_six_extensions_index_five[simp]:
  "extend_env a
      (extend_env b
        (extend_env c
          (extend_env d
            (extend_env e
              (extend_env f \<rho>))))) 5 = f"
  by (simp add: eval_nat_numeral)

lemma pp_t_T6_iterated_diagonal_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_T6_iterated_diagonal n \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type)
      \<longrightarrow>
      (\<forall>q.
        Elem q (pp_t_domain Prop)
        \<longrightarrow>
        (pp_t_T6_iterated_unary_pure n w X
          \<and> pp_t_fun_prime_predicate
            (pp_t_T6_iterated_unary_pure n) w q
          \<and> pp_t_eqv Prop w p (X \<acute> q))
        \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
proof -
  let ?C = "pp_t_T6_iterated_classifier n"
  let ?D = "pp_t_T6_diagonal_fragment_constants"
  have C:
      "Elem ?C (pp_t_domain pp_t_constants_classifier_type)"
    by (rule pp_t_T6_iterated_classifier_in_domain)
  have beta_classifier:
      "pp_t_T6_purity_builder_den \<acute> ?C
       =
       pp_t_eval ?D
         (extend_env ?C pp_t_closed_env)
         pp_T6_abstract_body"
    unfolding pp_t_T6_purity_builder_den_def
      pp_T6_purity_builder_def
    using C
    by (simp add: Lambda_app pp_t_dom_def pp_unary_ty_def)
  have beta_p:
      "pp_t_eval ?D
          (extend_env ?C pp_t_closed_env)
          pp_T6_abstract_body \<acute> p
       =
       pp_t_eval ?D
          (extend_env p
            (extend_env ?C pp_t_closed_env))
          (Forall pp_t_constants_unary_type
            (Forall Prop
              (Imp
                (Conj
                  (App (Var 3) (Var 1))
                  (Conj
                    (Forall pp_t_constants_unary_type
                      (Forall pp_t_constants_unary_type
                        (Imp
                          (Conj
                            (App (Var 5) (Var 1))
                            (App (Var 5) (Var 0)))
                          (Imp
                            (Eq Prop
                              (App (Var 1) (Var 2))
                              (App (Var 0) (Var 2)))
                            (Eq pp_t_constants_unary_type
                              (Var 1) (Var 0))))))
                    (Eq Prop
                      (Var 2) (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))"
    unfolding pp_T6_abstract_body_def pp_unary_ty_def
    apply (simp only: pp_t_eval.simps(4))
    by (rule Lambda_app[OF p])
  show ?thesis
    unfolding pp_t_T6_iterated_diagonal_def
      beta_classifier beta_p
      pp_t_fun_prime_predicate_def
    apply (simp only: pp_t_eval_Forall_holds
      pp_t_eval_Imp_holds pp_t_eval_Conj_holds
      pp_t_eval_Neg_holds pp_t_eval_Eq_holds)
    apply (simp del: pp_t_eqv.simps
      add: pp_t_classifier_holds extend_env.simps
      pp_t_three_extensions_index_two
      pp_t_four_extensions_index_three
      pp_t_six_extensions_index_five
      pp_t_T6_iterated_classifier_holds)
    done
qed

subsection \<open>Settled inputs at every finite stage\<close>

lemma pp_t_T6_constant_representative_at_every_stage:
  "pp_t_constant_operator b
    \<in> pp_t_T6_iterated_representatives n"
proof (induction n)
  case 0
  show ?case
    by (cases b;
      simp add: pp_t_T6_ten_representatives_def)
next
  case (Suc n)
  then show ?case by simp
qed

lemma pp_t_T6_iterated_constant_operator_is_pure:
  "pp_t_T6_iterated_unary_pure n w
    (pp_t_constant_operator b)"
  unfolding pp_t_T6_iterated_unary_pure_iff_represented[
    OF pp_t_constant_operator_in_domain]
  using pp_t_T6_constant_representative_at_every_stage
    pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain, of w b]
  by blast

lemma pp_t_T6_iterated_representation_at_fun_prime:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
    and pure_X:
      "pp_t_T6_iterated_unary_pure n w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_eqv pp_t_constants_unary_type w
    X (pp_t_constant_operator b)"
proof -
  have Kq:
      "pp_t_constant_operator b \<acute> q = pp_zf_truth b"
    by (rule pp_t_constant_operator_apply[OF q])
  have Xq: "Elem (X \<acute> q) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF X q])
  have agreement:
      "pp_t_eqv Prop w
        (X \<acute> q) (pp_t_constant_operator b \<acute> q)"
    unfolding Kq
    using Xq p pp_t_truth_in_domain p_as_Xq p_as_b
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    using Jq X pp_t_constant_operator_in_domain
      pure_X pp_t_T6_iterated_constant_operator_is_pure
      agreement
    unfolding pp_t_fun_prime_predicate_def
    by blast
qed

lemma pp_t_T6_iterated_representation_value:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
    and pure_X:
      "pp_t_T6_iterated_unary_pure n w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_holds (X \<acute> p) w = b"
proof -
  have operators:
      "pp_t_eqv pp_t_constants_unary_type w
        X (pp_t_constant_operator b)"
    by (rule pp_t_T6_iterated_representation_at_fun_prime[
      OF p q X Jq pure_X p_as_Xq p_as_b])
  have applications:
      "pp_t_eqv Prop w
        (X \<acute> p) (pp_t_constant_operator b \<acute> p)"
    by (rule pp_t_app_respects[
      OF operators p p pp_t_eqv_reflexive[OF p]])
  have at_w:
      "pp_t_holds (X \<acute> p) w
       = pp_t_holds (pp_t_constant_operator b \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w]
    by simp
  show ?thesis
    using at_w pp_t_constant_operator_holds[OF p, of b w]
    by simp
qed

lemma pp_t_T6_iterated_diagonal_false_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and false_p:
      "pp_t_eqv Prop w p (pp_zf_truth False)"
  shows "pp_t_holds
    (pp_t_T6_iterated_diagonal n \<acute> p) w"
  unfolding pp_t_T6_iterated_diagonal_holds[OF p]
proof (intro allI impI)
  fix X q
  assume X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and q: "Elem q (pp_t_domain Prop)"
    and antecedent:
      "pp_t_T6_iterated_unary_pure n w X
        \<and> pp_t_fun_prime_predicate
          (pp_t_T6_iterated_unary_pure n) w q
        \<and> pp_t_eqv Prop w p (X \<acute> q)"
  have pure_X:
      "pp_t_T6_iterated_unary_pure n w X"
    using antecedent by blast
  have Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
    using antecedent by blast
  have p_as_Xq:
      "pp_t_eqv Prop w p (X \<acute> q)"
    using antecedent by blast
  have false_value: "pp_t_holds (X \<acute> p) w = False"
    by (rule pp_t_T6_iterated_representation_value[
      OF p q X Jq pure_X p_as_Xq false_p])
  show "\<not> pp_t_holds (X \<acute> p) w"
    using false_value by simp
qed

lemma pp_t_T6_iterated_diagonal_true_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and true_p:
      "pp_t_eqv Prop w p (pp_zf_truth True)"
    and witness:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_fun_prime_predicate
          (pp_t_T6_iterated_unary_pure n) w q"
  shows "\<not> pp_t_holds
    (pp_t_T6_iterated_diagonal n \<acute> p) w"
proof
  assume Dp:
      "pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> p) w"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
    using witness by blast
  let ?K = "pp_t_constant_operator True"
  have Kq: "?K \<acute> q = pp_zf_truth True"
    by (rule pp_t_constant_operator_apply[OF q])
  have antecedent:
      "pp_t_T6_iterated_unary_pure n w ?K
        \<and> pp_t_fun_prime_predicate
          (pp_t_T6_iterated_unary_pure n) w q
        \<and> pp_t_eqv Prop w p (?K \<acute> q)"
    using pp_t_T6_iterated_constant_operator_is_pure
      Jq true_p
    unfolding Kq by blast
  have not_Kp: "\<not> pp_t_holds (?K \<acute> p) w"
    using pp_t_T6_iterated_diagonal_holds[OF p, of n w]
      Dp pp_t_constant_operator_in_domain q antecedent
    by blast
  show False
    using not_Kp
      pp_t_constant_operator_holds[OF p, of True w]
    by simp
qed

theorem pp_t_T6_iterated_diagonal_on_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
    and witness:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_fun_prime_predicate
          (pp_t_T6_iterated_unary_pure n) w q"
  shows "pp_t_holds
      (pp_t_T6_iterated_diagonal n \<acute> p) w
    = (\<not> b)"
proof (cases b)
  case False
  have settled_false:
      "pp_t_eqv Prop w p (pp_zf_truth False)"
    using settled False by simp
  have Dp:
      "pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> p) w"
    by (rule pp_t_T6_iterated_diagonal_false_input[
      OF p settled_false])
  show ?thesis
    using Dp False by simp
next
  case True
  have settled_true:
      "pp_t_eqv Prop w p (pp_zf_truth True)"
    using settled True by simp
  have not_Dp:
      "\<not> pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> p) w"
    by (rule pp_t_T6_iterated_diagonal_true_input[
      OF p settled_true witness])
  show ?thesis
    using not_Dp True by simp
qed

section \<open>Finite-stage fun-prime witnesses from equivariance\<close>

theorem pp_t_finite_equivariant_stock_has_fun_prime_witness_with_value:
  fixes V :: "ZF set"
    and U :: "bool list \<Rightarrow> ZF \<Rightarrow> bool"
  assumes finite: "finite V"
    and domain:
      "\<And>A. A \<in> V
        \<Longrightarrow> Elem A
          (pp_t_domain pp_t_constants_unary_type)"
    and equivariant:
      "\<And>A. A \<in> V
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of A)"
    and represented:
      "\<And>w X.
        Elem X (pp_t_domain pp_t_constants_unary_type)
        \<Longrightarrow>
        (U w X
          \<longleftrightarrow>
          (\<exists>A \<in> V.
            pp_t_eqv pp_t_constants_unary_type w A X))"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds q w = b
    \<and> pp_t_fun_prime_predicate U w q"
proof -
  let ?Stock = "pp_b_operator_of ` V"
  have countable: "countable ?Stock"
  proof (rule countable_image)
    show "countable V"
      using finite by (rule countable_finite)
  qed
  have stock_equivariant:
      "\<And>F. F \<in> ?Stock \<Longrightarrow> pp_b_equivariant F"
    using equivariant by blast
  obtain R where root: "([] \<in> R) = b"
    and separator:
      "\<forall>F \<in> ?Stock. \<forall>G \<in> ?Stock.
        (F R = G R \<longleftrightarrow> F = G)"
    using pp_b_generic_separator_for_countable_stock_with_root[
      OF countable stock_equivariant, of b]
    by blast
  let ?q = "pp_zf_of_b (pp_b_lift w R)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have q_value: "pp_t_holds ?q w = b"
    using root
    by (simp add: pp_b_lift_def)
  have separated:
      "A \<in> V \<Longrightarrow>
       B \<in> V \<Longrightarrow>
       pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)
       \<Longrightarrow> A = B"
    for A B
  proof -
    assume A: "A \<in> V"
      and B: "B \<in> V"
      and agreement:
        "pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)"
    have view_outputs:
        "pp_b_view w
            (pp_b_operator_of A (pp_b_lift w R))
         =
         pp_b_view w
            (pp_b_operator_of B (pp_b_lift w R))"
      using agreement
      unfolding pp_t_eqv.simps pp_b_view_def
        pp_b_operator_of_def pp_b_of_zf_def
      by auto
    have outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
      using view_outputs equivariant[OF A] equivariant[OF B]
      unfolding pp_b_equivariant_def
      by simp
    have operators:
        "pp_b_operator_of A = pp_b_operator_of B"
      using separator A B outputs by blast
    show "A = B"
      by (rule pp_b_operator_of_injective_on_unary_domain[
        OF domain[OF A] domain[OF B] operators])
  qed
  have predicate: "pp_t_fun_prime_predicate U w ?q"
  proof (unfold pp_t_fun_prime_predicate_def,
      intro allI impI)
    fix X Y
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and Y:
        "Elem Y (pp_t_domain pp_t_constants_unary_type)"
      and pure: "U w X \<and> U w Y"
      and agreement:
        "pp_t_eqv Prop w (X \<acute> ?q) (Y \<acute> ?q)"
    obtain A where A: "A \<in> V"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type w A X"
      using represented[OF X] pure by blast
    obtain B where B: "B \<in> V"
      and BY:
        "pp_t_eqv pp_t_constants_unary_type w B Y"
      using represented[OF Y] pure by blast
    have A_X:
        "pp_t_eqv Prop w (A \<acute> ?q) (X \<acute> ?q)"
      by (rule pp_t_app_respects[
        OF AX q q pp_t_eqv_reflexive[OF q]])
    have B_Y:
        "pp_t_eqv Prop w (B \<acute> ?q) (Y \<acute> ?q)"
      by (rule pp_t_app_respects[
        OF BY q q pp_t_eqv_reflexive[OF q]])
    have AB_outputs:
        "pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)"
      using pp_t_app_closed[OF domain[OF A] q]
        pp_t_app_closed[OF X q]
        pp_t_app_closed[OF Y q]
        pp_t_app_closed[OF domain[OF B] q]
        A_X agreement B_Y
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    have AB: "A = B"
      by (rule separated[OF A B AB_outputs])
    have XB:
        "pp_t_eqv pp_t_constants_unary_type w X B"
      by (rule pp_t_eqv_symmetric[
        OF domain[OF A] X AX, unfolded AB])
    show "pp_t_eqv pp_t_constants_unary_type w X Y"
      using pp_t_eqv_transitive[
        OF X domain[OF B] Y XB BY] .
  qed
  show ?thesis using q q_value predicate by blast
qed

corollary pp_t_finite_equivariant_stock_has_fun_prime_witness:
  fixes V :: "ZF set"
    and U :: "bool list \<Rightarrow> ZF \<Rightarrow> bool"
  assumes finite: "finite V"
    and domain:
      "\<And>A. A \<in> V
        \<Longrightarrow> Elem A
          (pp_t_domain pp_t_constants_unary_type)"
    and equivariant:
      "\<And>A. A \<in> V
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of A)"
    and represented:
      "\<And>w X.
        Elem X (pp_t_domain pp_t_constants_unary_type)
        \<Longrightarrow>
        (U w X
          \<longleftrightarrow>
          (\<exists>A \<in> V.
            pp_t_eqv pp_t_constants_unary_type w A X))"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_fun_prime_predicate U w q"
  using pp_t_finite_equivariant_stock_has_fun_prime_witness_with_value[
    OF finite domain equivariant represented, of w True]
  by blast

definition pp_t_T6_iterated_representatives_equivariant ::
    "nat \<Rightarrow> bool"
where
  "pp_t_T6_iterated_representatives_equivariant n
    \<longleftrightarrow>
    (\<forall>A \<in> pp_t_T6_iterated_representatives n.
      pp_b_equivariant (pp_b_operator_of A))"

lemma pp_t_T6_iterated_representatives_equivariant_zero:
  "pp_t_T6_iterated_representatives_equivariant 0"
  unfolding
    pp_t_T6_iterated_representatives_equivariant_def
  using pp_t_T6_ten_representatives_equivariant
  unfolding pp_t_T6_ten_representatives_equivariant_def
  by simp

theorem pp_t_T6_finite_stage_fun_prime_witness_with_value:
  assumes
    "pp_t_T6_iterated_representatives_equivariant n"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds q w = b
    \<and> pp_t_fun_prime_predicate
      (pp_t_T6_iterated_unary_pure n) w q"
proof (rule
    pp_t_finite_equivariant_stock_has_fun_prime_witness_with_value[
    OF pp_t_T6_iterated_representatives_finite])
  show "\<And>A.
      A \<in> pp_t_T6_iterated_representatives n
      \<Longrightarrow>
      Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain)
  show "\<And>A.
      A \<in> pp_t_T6_iterated_representatives n
      \<Longrightarrow> pp_b_equivariant (pp_b_operator_of A)"
    using assms
    unfolding
      pp_t_T6_iterated_representatives_equivariant_def
    by blast
  show "\<And>v X.
      Elem X (pp_t_domain pp_t_constants_unary_type)
      \<Longrightarrow>
      (pp_t_T6_iterated_unary_pure n v X
        \<longleftrightarrow>
        (\<exists>A \<in> pp_t_T6_iterated_representatives n.
          pp_t_eqv pp_t_constants_unary_type v A X))"
    by (rule pp_t_T6_iterated_unary_pure_iff_represented)
qed

corollary pp_t_T6_finite_stage_fun_prime_witness:
  assumes
    "pp_t_T6_iterated_representatives_equivariant n"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_fun_prime_predicate
      (pp_t_T6_iterated_unary_pure n) w q"
  using pp_t_T6_finite_stage_fun_prime_witness_with_value[
    OF assms, of w True]
  by blast

corollary pp_t_T6_stage_zero_fun_prime_witness:
  "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_fun_prime_predicate
      (pp_t_T6_iterated_unary_pure 0) w q"
  by (rule pp_t_T6_finite_stage_fun_prime_witness[
    OF pp_t_T6_iterated_representatives_equivariant_zero])

theorem pp_t_T6_equivariance_successor_iff_new_diagonal:
  "pp_t_T6_iterated_representatives_equivariant (Suc n)
    \<longleftrightarrow>
    pp_t_T6_iterated_representatives_equivariant n
      \<and> pp_b_equivariant
        (pp_b_operator_of (pp_t_T6_iterated_diagonal n))"
  unfolding
    pp_t_T6_iterated_representatives_equivariant_def
    pp_t_T6_iterated_representatives.simps
  by auto

lemma pp_t_T6_iterated_representative_cone_related:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
    and A:
      "A \<in> pp_t_T6_iterated_representatives n"
  shows "pp_t_cone_rel pp_t_constants_unary_type s A A"
proof (rule pp_t_unary_operator_equivariant_implies_cone_related)
  show "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  show "pp_b_equivariant (pp_b_operator_of A)"
    using stage A
    unfolding
      pp_t_T6_iterated_representatives_equivariant_def
    by blast
qed

lemma pp_t_T6_iterated_unary_pure_cone_iff:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows "pp_t_T6_iterated_unary_pure n (s @ u) X
    \<longleftrightarrow>
    pp_t_T6_iterated_unary_pure n u Y"
  unfolding pp_t_T6_iterated_unary_pure_iff_represented[OF X]
    pp_t_T6_iterated_unary_pure_iff_represented[OF Y]
proof
  assume left:
      "\<exists>A \<in> pp_t_T6_iterated_representatives n.
        pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
  then obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  have AY:
      "pp_t_eqv pp_t_constants_unary_type u A Y"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF A_domain A_domain X Y
        pp_t_T6_iterated_representative_cone_related[
          OF stage A] XY,
      of u]
      AX by blast
  show "\<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_eqv pp_t_constants_unary_type u A Y"
    using A AY by blast
next
  assume right:
      "\<exists>A \<in> pp_t_T6_iterated_representatives n.
        pp_t_eqv pp_t_constants_unary_type u A Y"
  then obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and AY:
      "pp_t_eqv pp_t_constants_unary_type u A Y"
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  have AX:
      "pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF A_domain A_domain X Y
        pp_t_T6_iterated_representative_cone_related[
          OF stage A] XY,
      of u]
      AY by blast
  show "\<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    using A AX by blast
qed

lemma pp_t_T6_iterated_classifier_pointwise_cone:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows
    "pp_t_holds (pp_t_T6_iterated_classifier n \<acute> X)
        (s @ u)
      \<longleftrightarrow>
     pp_t_holds (pp_t_T6_iterated_classifier n \<acute> Y) u"
proof -
  have left:
      "pp_t_holds (pp_t_T6_iterated_classifier n \<acute> X)
          (s @ u)
        \<longleftrightarrow>
       pp_t_T6_iterated_unary_pure n (s @ u) X"
    unfolding pp_t_T6_iterated_classifier_def
    by (rule pp_t_classifier_holds[OF X])
  have right:
      "pp_t_holds (pp_t_T6_iterated_classifier n \<acute> Y) u
        \<longleftrightarrow>
       pp_t_T6_iterated_unary_pure n u Y"
    unfolding pp_t_T6_iterated_classifier_def
    by (rule pp_t_classifier_holds[OF Y])
  show ?thesis
    using left right
      pp_t_T6_iterated_unary_pure_cone_iff[
        OF stage X Y XY, of u]
    by blast
qed

lemma pp_t_T6_iterated_classifier_outputs_cone:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows "pp_t_cone_rel Prop s
    (pp_t_T6_iterated_classifier n \<acute> X)
    (pp_t_T6_iterated_classifier n \<acute> Y)"
  unfolding pp_t_cone_rel.simps(2)
  using pp_t_T6_iterated_classifier_pointwise_cone[
    OF stage X Y XY]
  by blast

lemma pp_t_T6_iterated_classifier_cone_related:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
  shows "pp_t_cone_rel pp_t_constants_classifier_type s
    (pp_t_T6_iterated_classifier n)
    (pp_t_T6_iterated_classifier n)"
  apply (subst pp_t_cone_rel.simps(3))
  using pp_t_T6_iterated_classifier_outputs_cone[OF stage]
  by blast

lemma pp_t_T6_iterated_diagonal_cone_related:
  assumes stage:
      "pp_t_T6_iterated_representatives_equivariant n"
  shows "pp_t_cone_rel pp_t_constants_unary_type s
    (pp_t_T6_iterated_diagonal n)
    (pp_t_T6_iterated_diagonal n)"
proof -
  have builder:
      "pp_t_cone_rel pp_t_T6_builder_type s
        pp_t_T6_purity_builder_den
        pp_t_T6_purity_builder_den"
    by (rule pp_t_T6_purity_builder_den_cone_related)
  have classifier:
      "pp_t_cone_rel pp_t_constants_classifier_type s
        (pp_t_T6_iterated_classifier n)
        (pp_t_T6_iterated_classifier n)"
    by (rule pp_t_T6_iterated_classifier_cone_related[OF stage])
  have classifier_domain:
      "Elem (pp_t_T6_iterated_classifier n)
        (pp_t_domain pp_t_constants_classifier_type)"
    by (rule pp_t_T6_iterated_classifier_in_domain)
  have applied:
      "pp_t_cone_rel pp_t_constants_unary_type s
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_T6_iterated_classifier n)
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_T6_iterated_classifier n)"
    using builder classifier_domain classifier_domain classifier
    by simp
  show ?thesis
    using applied
    unfolding pp_t_T6_iterated_diagonal_def .
qed

theorem pp_t_T6_iterated_diagonal_equivariant:
  assumes
    "pp_t_T6_iterated_representatives_equivariant n"
  shows "pp_b_equivariant
    (pp_b_operator_of (pp_t_T6_iterated_diagonal n))"
  by (rule pp_t_cone_rel_operator_implies_equivariant)
    (rule pp_t_T6_iterated_diagonal_cone_related[OF assms])

theorem pp_t_T6_every_finite_stage_equivariant:
  "pp_t_T6_iterated_representatives_equivariant n"
proof (induction n)
  case 0
  show ?case
    by (rule
      pp_t_T6_iterated_representatives_equivariant_zero)
next
  case (Suc n)
  show ?case
    unfolding
      pp_t_T6_equivariance_successor_iff_new_diagonal
    using Suc.IH
      pp_t_T6_iterated_diagonal_equivariant[OF Suc.IH]
    by blast
qed

corollary pp_t_T6_every_finite_stage_has_fun_prime_witness:
  "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_fun_prime_predicate
      (pp_t_T6_iterated_unary_pure n) w q"
  by (rule pp_t_T6_finite_stage_fun_prime_witness[
    OF pp_t_T6_every_finite_stage_equivariant])

theorem pp_t_T6_stage_stable_iff_global_collision:
  "pp_t_T6_stage_stable n
    \<longleftrightarrow>
    (\<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_T6_iterated_diagonal n = A)"
proof
  assume stable: "pp_t_T6_stage_stable n"
  then obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and root:
      "pp_t_eqv pp_t_constants_unary_type []
        A (pp_t_T6_iterated_diagonal n)"
    unfolding pp_t_T6_stage_stable_iff_represented
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  have equality:
      "A = pp_t_T6_iterated_diagonal n"
    using pp_t_root_eqv_iff_eq[
      OF A_domain pp_t_T6_iterated_diagonal_in_domain]
      root by blast
  show "\<exists>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_T6_iterated_diagonal n = A"
    using A equality by blast
next
  assume collision:
      "\<exists>A \<in> pp_t_T6_iterated_representatives n.
        pp_t_T6_iterated_diagonal n = A"
  then obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and equality: "pp_t_T6_iterated_diagonal n = A"
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  have represented:
      "\<forall>w. \<exists>A \<in> pp_t_T6_iterated_representatives n.
        pp_t_eqv pp_t_constants_unary_type w A
          (pp_t_T6_iterated_diagonal n)"
  proof
    fix w
    have reflexive:
        "pp_t_eqv pp_t_constants_unary_type w A A"
      by (rule pp_t_eqv_reflexive[OF A_domain])
    show "\<exists>A \<in> pp_t_T6_iterated_representatives n.
        pp_t_eqv pp_t_constants_unary_type w A
          (pp_t_T6_iterated_diagonal n)"
      using A equality reflexive by blast
  qed
  show "pp_t_T6_stage_stable n"
    using represented
    unfolding pp_t_T6_stage_stable_iff_represented .
qed

corollary pp_t_T6_stage_unstable_iff_no_global_collision:
  "\<not> pp_t_T6_stage_stable n
    \<longleftrightarrow>
    (\<forall>A \<in> pp_t_T6_iterated_representatives n.
      pp_t_T6_iterated_diagonal n \<noteq> A)"
  unfolding pp_t_T6_stage_stable_iff_global_collision
  by blast

lemma pp_t_T6_iterated_diagonal_neq_if_preserves_settled:
  assumes output_value:
      "pp_t_holds (A \<acute> (pp_zf_truth b)) w = b"
  shows "pp_t_T6_iterated_diagonal n \<noteq> A"
proof
  assume equality: "pp_t_T6_iterated_diagonal n = A"
  have settled:
      "pp_t_eqv Prop w
        (pp_zf_truth b) (pp_zf_truth b)"
    by (rule pp_t_eqv_reflexive[OF pp_t_truth_in_domain])
  have diagonal:
      "pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> (pp_zf_truth b)) w
        = (\<not> b)"
    by (rule pp_t_T6_iterated_diagonal_on_settled[
      OF pp_t_truth_in_domain settled
        pp_t_T6_every_finite_stage_has_fun_prime_witness])
  show False
    using diagonal output_value equality
    by (cases b) simp_all
qed

corollary pp_t_T6_iterated_diagonal_not_identity:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_identity_operator"
proof (rule pp_t_T6_iterated_diagonal_neq_if_preserves_settled[
    where b=False and w="[]"])
  have application:
      "pp_t_identity_operator \<acute> (pp_zf_truth False)
        = pp_zf_truth False"
    unfolding pp_t_identity_operator_def
    by (rule Lambda_app[OF pp_t_truth_in_domain])
  show "pp_t_holds
      (pp_t_identity_operator \<acute> (pp_zf_truth False)) [] =
      False"
    unfolding application
    by simp
qed

corollary pp_t_T6_iterated_diagonal_not_constant:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_constant_operator b"
  by (rule pp_t_T6_iterated_diagonal_neq_if_preserves_settled[
      where b=b and w="[]"])
    (rule pp_t_constant_operator_holds[
      OF pp_t_truth_in_domain])

corollary pp_t_T6_iterated_diagonal_not_necessity:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_necessity_operator"
proof (rule pp_t_T6_iterated_diagonal_neq_if_preserves_settled[
    where b=False and w="[]"])
  show "pp_t_holds
      (pp_t_necessity_operator \<acute> (pp_zf_truth False)) [] =
      False"
    unfolding pp_t_necessity_operator_holds[
      OF pp_t_truth_in_domain]
    by simp
qed

corollary pp_t_T6_iterated_diagonal_not_possibility:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_possibility_operator"
proof (rule pp_t_T6_iterated_diagonal_neq_if_preserves_settled[
    where b=True and w="[]"])
  show "pp_t_holds
      (pp_t_possibility_operator \<acute> (pp_zf_truth True)) [] =
      True"
    unfolding pp_t_possibility_operator_holds[
      OF pp_t_truth_in_domain]
    by auto
qed

corollary pp_t_T6_iterated_diagonal_not_quantified_fun_prime:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_quantified_fun_prime_operator"
proof (rule pp_t_T6_iterated_diagonal_neq_if_preserves_settled[
    where b=False and w="[]"])
  have settled:
      "pp_t_eqv Prop []
        (pp_zf_truth False) (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF pp_t_truth_in_domain])
  show "pp_t_holds
      (pp_t_quantified_fun_prime_operator
        \<acute> (pp_zf_truth False)) [] =
      False"
    using pp_t_quantified_fun_prime_false_on_settled[
      OF pp_t_truth_in_domain settled]
    by simp
qed

lemma pp_t_T6_iterated_diagonal_false_on_negated_true_witness:
  assumes q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
    and q_true: "pp_t_holds q w"
  shows "\<not> pp_t_holds
    (pp_t_T6_iterated_diagonal n
      \<acute> (pp_t_negation_operator \<acute> q)) w"
proof
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have pure_negation:
      "pp_t_T6_iterated_unary_pure n w
        pp_t_negation_operator"
  proof -
    have member:
        "pp_t_negation_operator
          \<in> pp_t_T6_iterated_representatives n"
      by (induction n)
        (simp_all add: pp_t_T6_ten_representatives_def)
    show ?thesis
      unfolding pp_t_T6_iterated_unary_pure_iff_represented[
        OF pp_t_negation_operator_in_domain]
      using member pp_t_eqv_reflexive[
        OF pp_t_negation_operator_in_domain, of w]
      by blast
  qed
  have representation:
      "pp_t_eqv Prop w ?p
        (pp_t_negation_operator \<acute> q)"
    by (rule pp_t_eqv_reflexive[OF p])
  assume Dp:
      "pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> ?p) w"
  have not_double_negation:
      "\<not> pp_t_holds
        (pp_t_negation_operator \<acute> ?p) w"
    using pp_t_T6_iterated_diagonal_holds[OF p, of n w]
      Dp pp_t_negation_operator_in_domain q
      pure_negation Jq representation
    by blast
  have double_negation:
      "pp_t_holds
        (pp_t_negation_operator \<acute> ?p) w"
    using pp_t_negation_operator_holds[OF p, of w]
      pp_t_negation_operator_holds[OF q, of w]
      q_true
    by simp
  show False using not_double_negation double_negation by blast
qed

corollary pp_t_T6_iterated_diagonal_not_negation:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_negation_operator"
proof
  assume equality:
      "pp_t_T6_iterated_diagonal n =
        pp_t_negation_operator"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and q_true: "pp_t_holds q []"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) [] q"
    using pp_t_T6_finite_stage_fun_prime_witness_with_value[
      OF pp_t_T6_every_finite_stage_equivariant,
      of "[]" True]
    by blast
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have not_Dp:
      "\<not> pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> ?p) []"
    by (rule
      pp_t_T6_iterated_diagonal_false_on_negated_true_witness[
        OF q Jq q_true])
  have negation_p:
      "pp_t_holds (pp_t_negation_operator \<acute> ?p) []"
    using pp_t_negation_operator_holds[OF p, of "[]"]
      pp_t_negation_operator_holds[OF q, of "[]"]
      q_true
    by simp
  show False using not_Dp negation_p equality by simp
qed

corollary pp_t_T6_iterated_diagonal_not_possible_falsity:
  "pp_t_T6_iterated_diagonal n \<noteq>
    pp_t_possible_falsity_operator"
proof
  assume equality:
      "pp_t_T6_iterated_diagonal n =
        pp_t_possible_falsity_operator"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and q_true: "pp_t_holds q []"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) [] q"
    using pp_t_T6_finite_stage_fun_prime_witness_with_value[
      OF pp_t_T6_every_finite_stage_equivariant,
      of "[]" True]
    by blast
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have not_p: "\<not> pp_t_holds ?p []"
    using pp_t_negation_operator_holds[OF q, of "[]"]
      q_true by simp
  have not_settled_true:
      "\<not> pp_t_eqv Prop [] ?p (pp_zf_truth True)"
  proof
    assume settled:
        "pp_t_eqv Prop [] ?p (pp_zf_truth True)"
    have "pp_t_holds ?p []"
      using pp_t_prop_eqv_at[OF settled, of "[]"] by simp
    then show False using not_p by blast
  qed
  have possible_falsity_p:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) []"
    using pp_t_possible_falsity_operator_holds[OF p, of "[]"]
      not_settled_true by blast
  have not_Dp:
      "\<not> pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> ?p) []"
    by (rule
      pp_t_T6_iterated_diagonal_false_on_negated_true_witness[
        OF q Jq q_true])
  show False using possible_falsity_p not_Dp equality by simp
qed

lemma pp_t_T6_iterated_representatives_iff:
  "A \<in> pp_t_T6_iterated_representatives n
    \<longleftrightarrow>
    A \<in> pp_t_T6_ten_representatives
      \<or> (\<exists>k < n. A = pp_t_T6_iterated_diagonal k)"
proof (induction n arbitrary: A)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding pp_t_T6_iterated_representatives.simps
      insert_iff Suc.IH
    by (auto simp: less_Suc_eq)
qed

theorem pp_t_T6_finite_stage_collision_candidates:
  assumes stable: "pp_t_T6_stage_stable n"
  shows
    "pp_t_T6_iterated_diagonal n =
        pp_t_necessary_falsity_operator
    \<or> pp_t_T6_iterated_diagonal n =
        pp_t_fun_prime_T6_operator
    \<or> (\<exists>k < n.
        pp_t_T6_iterated_diagonal n =
          pp_t_T6_iterated_diagonal k)"
proof -
  obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and collision:
      "pp_t_T6_iterated_diagonal n = A"
    using stable
    unfolding pp_t_T6_stage_stable_iff_global_collision
    by blast
  have source:
      "A \<in> pp_t_T6_ten_representatives
        \<or> (\<exists>k < n.
          A = pp_t_T6_iterated_diagonal k)"
    using A
    unfolding pp_t_T6_iterated_representatives_iff .
  show ?thesis
    using source collision
      pp_t_T6_iterated_diagonal_not_identity[of n]
      pp_t_T6_iterated_diagonal_not_constant[
        of n True]
      pp_t_T6_iterated_diagonal_not_constant[
        of n False]
      pp_t_T6_iterated_diagonal_not_necessity[of n]
      pp_t_T6_iterated_diagonal_not_possibility[of n]
      pp_t_T6_iterated_diagonal_not_quantified_fun_prime[
        of n]
      pp_t_T6_iterated_diagonal_not_negation[of n]
      pp_t_T6_iterated_diagonal_not_possible_falsity[of n]
    unfolding pp_t_T6_ten_representatives_def
    by blast
qed

lemma pp_t_T6_global_collision_forces_square_failure:
  assumes A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and collision:
      "pp_t_T6_iterated_diagonal n = A"
    and q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q"
  shows "\<not> pp_t_holds (A \<acute> (A \<acute> q)) w"
proof
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_iterated_representative_in_domain[OF A])
  let ?p = "A \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF A_domain q])
  have pure_A:
      "pp_t_T6_iterated_unary_pure n w A"
    unfolding pp_t_T6_iterated_unary_pure_iff_represented[
      OF A_domain]
    using A pp_t_eqv_reflexive[OF A_domain, of w]
    by blast
  have representation:
      "pp_t_eqv Prop w ?p (A \<acute> q)"
    by (rule pp_t_eqv_reflexive[OF p])
  assume square: "pp_t_holds (A \<acute> ?p) w"
  have Dp:
      "pp_t_holds
        (pp_t_T6_iterated_diagonal n \<acute> ?p) w"
    using collision square by simp
  have not_square: "\<not> pp_t_holds (A \<acute> ?p) w"
    using pp_t_T6_iterated_diagonal_holds[OF p, of n w]
      Dp A_domain q pure_A Jq representation
    by blast
  show False using square not_square by blast
qed

theorem pp_t_T6_finite_stage_stability_forces_square_failure:
  assumes stable: "pp_t_T6_stage_stable n"
  shows "\<exists>A \<in> pp_t_T6_iterated_representatives n.
    pp_t_T6_iterated_diagonal n = A
    \<and>
    (\<forall>w q.
      Elem q (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_fun_prime_predicate
        (pp_t_T6_iterated_unary_pure n) w q
      \<longrightarrow>
      \<not> pp_t_holds (A \<acute> (A \<acute> q)) w)"
proof -
  obtain A where A:
      "A \<in> pp_t_T6_iterated_representatives n"
    and collision:
      "pp_t_T6_iterated_diagonal n = A"
    using stable
    unfolding pp_t_T6_stage_stable_iff_global_collision
    by blast
  have square:
      "\<forall>w q.
        Elem q (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_fun_prime_predicate
          (pp_t_T6_iterated_unary_pure n) w q
        \<longrightarrow>
        \<not> pp_t_holds (A \<acute> (A \<acute> q)) w"
    using pp_t_T6_global_collision_forces_square_failure[
      OF A collision]
    by blast
  show ?thesis using A collision square by blast
qed

lemma pp_t_necessary_falsity_square_iff_dense:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_necessary_falsity_operator
        \<acute> (pp_t_necessary_falsity_operator \<acute> q)) w
    \<longleftrightarrow>
    (\<forall>u. prefix w u
      \<longrightarrow> (\<exists>v. prefix u v \<and> pp_t_holds q v))"
proof -
  have Nq:
      "Elem (pp_t_necessary_falsity_operator \<acute> q)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_necessary_falsity_operator_in_domain q])
  show ?thesis
    unfolding pp_t_necessary_falsity_operator_holds[OF Nq]
      pp_t_necessary_falsity_operator_holds[OF q]
      pp_t_eqv.simps
    by auto
qed

subsection \<open>Why equivariance alone does not eliminate necessary falsity\<close>

definition pp_b_dense :: "pp_b_prop \<Rightarrow> bool" where
  "pp_b_dense P \<longleftrightarrow>
    (\<forall>w. \<exists>v. prefix w v \<and> v \<in> P)"

definition pp_b_empty_operator :: pp_b_operator where
  "pp_b_empty_operator P = {}"

definition pp_b_nondensity_operator :: pp_b_operator where
  "pp_b_nondensity_operator P =
    {w. \<not> pp_b_dense (pp_b_view w P)}"

lemma pp_b_empty_operator_equivariant:
  "pp_b_equivariant pp_b_empty_operator"
  unfolding pp_b_equivariant_def
    pp_b_empty_operator_def pp_b_view_def
  by simp

lemma pp_b_nondensity_operator_equivariant:
  "pp_b_equivariant pp_b_nondensity_operator"
  unfolding pp_b_equivariant_def
proof (intro allI set_eqI)
  fix s P u
  show "u \<in> pp_b_view s (pp_b_nondensity_operator P)
    \<longleftrightarrow>
    u \<in> pp_b_nondensity_operator (pp_b_view s P)"
    unfolding pp_b_nondensity_operator_def
      pp_b_view_def pp_b_dense_def
    by (auto simp: prefix_def append_assoc)
qed

lemma pp_b_empty_and_nondensity_distinct:
  "pp_b_empty_operator \<noteq> pp_b_nondensity_operator"
proof
  assume equality:
      "pp_b_empty_operator = pp_b_nondensity_operator"
  have root:
      "[] \<in> pp_b_nondensity_operator {}"
    unfolding pp_b_nondensity_operator_def
      pp_b_dense_def pp_b_view_def
    by simp
  have applications:
      "pp_b_empty_operator {} =
        pp_b_nondensity_operator {}"
    using equality by simp
  show False
    using root applications
    unfolding pp_b_empty_operator_def
    by simp
qed

lemma pp_b_dense_views_dense:
  assumes dense: "pp_b_dense P"
  shows "pp_b_dense (pp_b_view w P)"
  unfolding pp_b_dense_def
proof
  fix u
  obtain x where future: "prefix (w @ u) x"
    and x: "x \<in> P"
    using dense
    unfolding pp_b_dense_def
    by blast
  obtain t where xt0: "x = (w @ u) @ t"
    using future
    unfolding prefix_def by blast
  have xt: "x = w @ (u @ t)"
    using xt0 by (simp add: append_assoc)
  let ?v = "u @ t"
  have "prefix u ?v"
    unfolding prefix_def by blast
  moreover have "?v \<in> pp_b_view w P"
    using x xt
    unfolding pp_b_view_def
    by simp
  ultimately show "\<exists>v.
      prefix u v \<and> v \<in> pp_b_view w P"
    by blast
qed

theorem pp_b_equivariance_does_not_guarantee_dense_separation:
  "pp_b_equivariant pp_b_empty_operator
    \<and> pp_b_equivariant pp_b_nondensity_operator
    \<and> pp_b_empty_operator \<noteq> pp_b_nondensity_operator
    \<and> (\<forall>P. pp_b_dense P
      \<longrightarrow>
      pp_b_empty_operator P =
        pp_b_nondensity_operator P)"
proof (intro conjI allI impI)
  show "pp_b_equivariant pp_b_empty_operator"
    by (rule pp_b_empty_operator_equivariant)
  show "pp_b_equivariant pp_b_nondensity_operator"
    by (rule pp_b_nondensity_operator_equivariant)
  show "pp_b_empty_operator \<noteq> pp_b_nondensity_operator"
    by (rule pp_b_empty_and_nondensity_distinct)
  fix P
  assume dense: "pp_b_dense P"
  have no_gaps:
      "pp_b_nondensity_operator P = {}"
    unfolding pp_b_nondensity_operator_def
    using pp_b_dense_views_dense[OF dense]
    by blast
  show "pp_b_empty_operator P =
      pp_b_nondensity_operator P"
    unfolding pp_b_empty_operator_def no_gaps ..
qed

text \<open>
  Thus the previously isolated equation is exactly the stage-zero stopping
  test, not a model-independent contradiction.  If it fails, the next
  finite stock has eleven representatives and the precise new question is
  whether the builder value at its rebuilt classifier is represented there.
  Every finite stage remains cone-natural and has both true and false
  fun-prime witnesses.  Stabilization is equivalent to a global collision.
  After the uniform collision eliminations above, the only possible
  collisions are with necessary falsity, the old T6 operator, or an earlier
  generated diagonal.  Any such collision forces the square of that
  candidate to fail on every fun-prime witness for the stage.

  For necessary falsity, a positive square is exactly the density condition
  on the witness.  The final theorem shows why the generic separator
  argument cannot simply be strengthened by equivariance: distinct
  equivariant operators may agree on every dense proposition.  Continuing
  this SCC branch therefore requires a new invariant specific to the
  generated T6 operators, strong enough to give dense separation (and the
  analogous square-positive separation for earlier diagonals).  Without
  such an invariant, the finite iteration has reached the same absorption
  obstruction as the direct model construction.
\<close>

end
