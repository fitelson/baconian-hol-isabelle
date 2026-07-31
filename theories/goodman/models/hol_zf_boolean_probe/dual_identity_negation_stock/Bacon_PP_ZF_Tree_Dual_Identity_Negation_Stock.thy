theory Bacon_PP_ZF_Tree_Dual_Identity_Negation_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Recurrent_Generic_Seed.Bacon_PP_ZF_Tree_Dual_Recurrent_Generic_Seed
begin

section \<open>The dual modal-boundary base stock\<close>

definition pp_t_dual_modal_boundary_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_dual_modal_boundary_stock w X
    \<longleftrightarrow>
    pp_t_probe_modal_boolean_stock w X
    \<or>
    pp_t_moving_boundary_singleton_stock
      pp_t_probe_modal_boolean_dual_recurrent_seed_at w X"

lemma pp_t_dual_modal_boundary_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_dual_modal_boundary_stock"
  using pp_t_probe_modal_boolean_stock_admissible
    pp_t_moving_boundary_singleton_stock_admissible[
      where R=pp_t_probe_modal_boolean_dual_recurrent_seed_at]
  unfolding pp_t_predicate_admissible_def
    pp_t_dual_modal_boundary_stock_def
  by blast

lemma pp_t_dual_modal_boundary_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_modal_boundary_stock w X"
  shows "pp_t_dual_modal_boundary_stock w
    (pp_t_pointwise_complement X)"
proof -
  have modal:
      "pp_t_probe_modal_boolean_stock w X
        \<Longrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_pointwise_complement X)"
    unfolding pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF X])
  have boundary:
      "pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_dual_recurrent_seed_at w X
        \<Longrightarrow>
       pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_dual_recurrent_seed_at w
          (pp_t_pointwise_complement X)"
    by (rule
      pp_t_moving_boundary_singleton_stock_negation_closed[OF X])
  show ?thesis
    using stock modal boundary
    unfolding pp_t_dual_modal_boundary_stock_def
    by blast
qed

theorem pp_t_dual_modal_boundary_stock_recombines:
  "pp_t_unary_recombines_at
    pp_t_dual_modal_boundary_stock
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  have modal:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_recombines)
  have boundary:
      "pp_t_unary_recombines_at
        (pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_dual_recurrent_seed_at)
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
    by (rule pp_t_moving_boundary_singleton_stock_recombines)
      (rule
        pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  show ?thesis
    using modal boundary
    unfolding pp_t_unary_recombines_at_def
      pp_t_dual_modal_boundary_stock_def
    by blast
qed

section \<open>The complete identity-negation enlargement\<close>

abbreviation pp_t_dual_identity_section :: ZF
where
  "pp_t_dual_identity_section \<equiv>
    pp_t_dual_recurrent_full_section (pp_t_closed_den prop_id)"

abbreviation pp_t_dual_negation_section :: ZF
where
  "pp_t_dual_negation_section \<equiv>
    pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_negation_operator)"

abbreviation pp_t_dual_complemented_identity_section :: ZF
where
  "pp_t_dual_complemented_identity_section \<equiv>
    pp_t_pointwise_complement pp_t_dual_identity_section"

abbreviation pp_t_dual_complemented_negation_section :: ZF
where
  "pp_t_dual_complemented_negation_section \<equiv>
    pp_t_pointwise_complement pp_t_dual_negation_section"

definition pp_t_dual_identity_negation_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_dual_identity_negation_stock w X
    \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_one_context_unary_type)
    \<and>
    (pp_t_dual_modal_boundary_stock w X
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w X
       pp_t_dual_identity_section
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w X
       pp_t_dual_complemented_identity_section
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w X
       pp_t_dual_negation_section
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w X
       pp_t_dual_complemented_negation_section)"

lemma pp_t_dual_identity_section_in_domain:
  "Elem pp_t_dual_identity_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_dual_recurrent_full_section_in_domain)
    (rule pp_t_closed_den_in_domain, rule typed_prop_id)

lemma pp_t_dual_negation_section_in_domain:
  "Elem pp_t_dual_negation_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_dual_recurrent_full_section_in_domain)
    (rule pp_t_closed_den_in_domain, rule pp_t_closed_negation_typed)

lemma pp_t_dual_complemented_identity_section_in_domain:
  "Elem pp_t_dual_complemented_identity_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_pointwise_complement_in_domain)
    (rule pp_t_dual_identity_section_in_domain)

lemma pp_t_dual_complemented_negation_section_in_domain:
  "Elem pp_t_dual_complemented_negation_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_pointwise_complement_in_domain)
    (rule pp_t_dual_negation_section_in_domain)

lemma pp_t_reverse_eqv_class_predicate_admissible:
  assumes z: "Elem z (pp_t_domain \<sigma>)"
  shows "pp_t_predicate_admissible \<sigma>
    (\<lambda>w X. pp_t_eqv \<sigma> w X z)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain \<sigma>)"
    and Y: "Elem Y (pp_t_domain \<sigma>)"
    and XY: "pp_t_eqv \<sigma> w X Y"
    and wv: "prefix w v"
  have XY_v: "pp_t_eqv \<sigma> v X Y"
    by (rule pp_t_eqv_persistent[OF XY wv])
  have YX_v: "pp_t_eqv \<sigma> v Y X"
    by (rule pp_t_eqv_symmetric[OF X Y XY_v])
  show "pp_t_eqv \<sigma> v X z = pp_t_eqv \<sigma> v Y z"
  proof
    assume Xz: "pp_t_eqv \<sigma> v X z"
    show "pp_t_eqv \<sigma> v Y z"
      by (rule pp_t_eqv_transitive[OF Y X z YX_v Xz])
  next
    assume Yz: "pp_t_eqv \<sigma> v Y z"
    show "pp_t_eqv \<sigma> v X z"
      by (rule pp_t_eqv_transitive[OF X Y z XY_v Yz])
  qed
qed

lemma pp_t_dual_identity_negation_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_dual_identity_negation_stock"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have base:
      "pp_t_dual_modal_boundary_stock v X
        \<longleftrightarrow>
       pp_t_dual_modal_boundary_stock v Y"
    using pp_t_dual_modal_boundary_stock_admissible
      X Y XY wv
    unfolding pp_t_predicate_admissible_def
    by blast
  have class_eq:
      "\<And>P.
        Elem P (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        (pp_t_eqv pp_t_one_context_unary_type v X P
          \<longleftrightarrow>
         pp_t_eqv pp_t_one_context_unary_type v Y P)"
  proof -
    fix P
    assume P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
    have admissible:
        "pp_t_predicate_admissible pp_t_one_context_unary_type
          (\<lambda>w X. pp_t_eqv pp_t_one_context_unary_type w X P)"
      by (rule pp_t_reverse_eqv_class_predicate_admissible[OF P])
    show "pp_t_eqv pp_t_one_context_unary_type v X P
        \<longleftrightarrow>
      pp_t_eqv pp_t_one_context_unary_type v Y P"
      using admissible X Y XY wv
      unfolding pp_t_predicate_admissible_def
      by blast
  qed
  show "pp_t_dual_identity_negation_stock v X
      \<longleftrightarrow>
    pp_t_dual_identity_negation_stock v Y"
    unfolding pp_t_dual_identity_negation_stock_def
    using X Y base
      class_eq[OF pp_t_dual_identity_section_in_domain]
      class_eq[OF pp_t_dual_complemented_identity_section_in_domain]
      class_eq[OF pp_t_dual_negation_section_in_domain]
      class_eq[OF pp_t_dual_complemented_negation_section_in_domain]
    by blast
qed

lemma pp_t_dual_identity_negation_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_identity_negation_stock w X"
  shows "pp_t_dual_identity_negation_stock w
    (pp_t_pointwise_complement X)"
proof -
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  have base:
      "pp_t_dual_modal_boundary_stock w X
        \<Longrightarrow>
       pp_t_dual_identity_negation_stock w
        (pp_t_pointwise_complement X)"
    unfolding pp_t_dual_identity_negation_stock_def
    using NX pp_t_dual_modal_boundary_stock_negation_closed[OF X]
    by blast
  have complement_class:
      "\<And>P.
        Elem P (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w X P
        \<Longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement P)"
    by (rule pp_t_pointwise_complement_respects_equivalence[OF X])
  have involution_class:
      "\<And>P.
        Elem P (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          X (pp_t_pointwise_complement P)
        \<Longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X) P"
  proof -
    fix P
    assume P: "Elem P (pp_t_domain pp_t_one_context_unary_type)"
      and XP:
        "pp_t_eqv pp_t_one_context_unary_type w
          X (pp_t_pointwise_complement P)"
    have NP:
        "Elem (pp_t_pointwise_complement P)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF P])
    have complements:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement
            (pp_t_pointwise_complement P))"
      by (rule pp_t_pointwise_complement_respects_equivalence[
        OF X NP XP])
    have involution:
        "pp_t_pointwise_complement
            (pp_t_pointwise_complement P) = P"
      by (rule pp_t_pointwise_complement_involution[OF P])
    show "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_pointwise_complement X) P"
      using complements
      unfolding involution .
  qed
  from stock have cases:
      "pp_t_dual_modal_boundary_stock w X
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
        pp_t_dual_identity_section
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
        pp_t_dual_complemented_identity_section
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
        pp_t_dual_negation_section
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w X
        pp_t_dual_complemented_negation_section"
    unfolding pp_t_dual_identity_negation_stock_def
    by blast
  from cases show ?thesis
  proof
    assume base_X: "pp_t_dual_modal_boundary_stock w X"
    show ?thesis by (rule base[OF base_X])
  next
    assume generated:
        "pp_t_eqv pp_t_one_context_unary_type w X
            pp_t_dual_identity_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
            pp_t_dual_complemented_identity_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
            pp_t_dual_negation_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
            pp_t_dual_complemented_negation_section"
    from generated show ?thesis
    proof
      assume XI:
          "pp_t_eqv pp_t_one_context_unary_type w X
            pp_t_dual_identity_section"
      have result:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_pointwise_complement X)
            pp_t_dual_complemented_identity_section"
        by (rule complement_class[
          OF pp_t_dual_identity_section_in_domain XI])
      show ?thesis
        unfolding pp_t_dual_identity_negation_stock_def
        using NX result by blast
    next
      assume remaining:
          "pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_complemented_identity_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_negation_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_complemented_negation_section"
      from remaining show ?thesis
      proof
        assume XNI:
            "pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_complemented_identity_section"
        have result:
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_pointwise_complement X)
              pp_t_dual_identity_section"
          by (rule involution_class[
            OF pp_t_dual_identity_section_in_domain XNI])
        show ?thesis
          unfolding pp_t_dual_identity_negation_stock_def
          using NX result by blast
      next
        assume negation_remaining:
            "pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_negation_section
            \<or>
             pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_complemented_negation_section"
        from negation_remaining show ?thesis
        proof
          assume XN:
              "pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_negation_section"
          have result:
              "pp_t_eqv pp_t_one_context_unary_type w
                (pp_t_pointwise_complement X)
                pp_t_dual_complemented_negation_section"
            by (rule complement_class[
              OF pp_t_dual_negation_section_in_domain XN])
          show ?thesis
            unfolding pp_t_dual_identity_negation_stock_def
            using NX result by blast
        next
          assume XNN:
              "pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_complemented_negation_section"
          have result:
              "pp_t_eqv pp_t_one_context_unary_type w
                (pp_t_pointwise_complement X)
                pp_t_dual_negation_section"
            by (rule involution_class[
              OF pp_t_dual_negation_section_in_domain XNN])
          show ?thesis
            unfolding pp_t_dual_identity_negation_stock_def
            using NX result by blast
        qed
      qed
    qed
  qed
qed

theorem pp_t_dual_identity_negation_stock_recombines:
  "pp_t_unary_recombines_at
    pp_t_dual_identity_negation_stock
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_dual_identity_negation_stock w X"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds
          (X \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) v"
    and q: "Elem q (pp_t_domain Prop)"
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have safe:
      "pp_t_recombination_safe_unary_operator X ?r w"
  proof -
    from stock have cases:
        "pp_t_dual_modal_boundary_stock w X
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
          pp_t_dual_identity_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
          pp_t_dual_complemented_identity_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
          pp_t_dual_negation_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w X
          pp_t_dual_complemented_negation_section"
      unfolding pp_t_dual_identity_negation_stock_def by blast
    from cases show ?thesis
    proof
      assume base: "pp_t_dual_modal_boundary_stock w X"
      show ?thesis
        using pp_t_dual_modal_boundary_stock_recombines
          X base
        unfolding pp_t_unary_recombines_at_def
          pp_t_recombination_safe_unary_operator_def
        by blast
    next
      assume generated:
          "pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_identity_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_complemented_identity_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_negation_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_complemented_negation_section"
      from generated show ?thesis
      proof
        assume XI:
            "pp_t_eqv pp_t_one_context_unary_type w X
              pp_t_dual_identity_section"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X pp_t_dual_identity_section_in_domain XI r
              pp_t_dual_recurrent_identity_section_safe])
      next
        assume remaining:
            "pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_complemented_identity_section
            \<or>
             pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_negation_section
            \<or>
             pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_complemented_negation_section"
        from remaining show ?thesis
        proof
          assume XNI:
              "pp_t_eqv pp_t_one_context_unary_type w X
                pp_t_dual_complemented_identity_section"
          show ?thesis
            by (rule pp_t_equivalent_recombination_safe_operator[
              OF X pp_t_dual_complemented_identity_section_in_domain
                XNI r
                pp_t_dual_recurrent_complemented_identity_section_safe])
        next
          assume negation_remaining:
              "pp_t_eqv pp_t_one_context_unary_type w X
                  pp_t_dual_negation_section
              \<or>
               pp_t_eqv pp_t_one_context_unary_type w X
                  pp_t_dual_complemented_negation_section"
          from negation_remaining show ?thesis
          proof
            assume XN:
                "pp_t_eqv pp_t_one_context_unary_type w X
                  pp_t_dual_negation_section"
            show ?thesis
              by (rule pp_t_equivalent_recombination_safe_operator[
                OF X pp_t_dual_negation_section_in_domain XN r
                  pp_t_dual_recurrent_negation_section_safe])
          next
            assume XNN:
                "pp_t_eqv pp_t_one_context_unary_type w X
                  pp_t_dual_complemented_negation_section"
            show ?thesis
              by (rule pp_t_equivalent_recombination_safe_operator[
                OF X pp_t_dual_complemented_negation_section_in_domain
                  XNN r
                  pp_t_dual_recurrent_complemented_negation_section_safe])
          qed
        qed
      qed
    qed
  qed
  have universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w"
    using safe necessary
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
  show "pp_t_holds (X \<acute> q) w"
    using universal q by blast
qed

end
