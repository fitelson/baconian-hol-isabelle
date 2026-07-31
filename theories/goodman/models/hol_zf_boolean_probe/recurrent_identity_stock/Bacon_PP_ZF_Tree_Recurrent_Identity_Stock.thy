theory Bacon_PP_ZF_Tree_Recurrent_Identity_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Antipatching.Bacon_PP_ZF_Tree_Recurrent_Probe_Antipatching
begin

section \<open>Adjoining the full identity classifier section\<close>

abbreviation pp_t_recurrent_full_identity_section :: ZF
where
  "pp_t_recurrent_full_identity_section \<equiv>
    pp_t_recurrent_probe_operator_probe \<acute> pp_t_closed_den prop_id"

abbreviation pp_t_recurrent_complemented_full_identity_section :: ZF
where
  "pp_t_recurrent_complemented_full_identity_section \<equiv>
    pp_t_pointwise_complement pp_t_recurrent_full_identity_section"

definition pp_t_recurrent_identity_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_recurrent_identity_stock w X
    \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_one_context_unary_type)
    \<and>
    (pp_t_recurrent_probe_stock w X
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w
        X pp_t_recurrent_full_identity_section
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w
        X pp_t_recurrent_complemented_full_identity_section)"

lemma pp_t_recurrent_full_identity_section_in_domain:
  "Elem pp_t_recurrent_full_identity_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_app_closed[
    OF pp_t_recurrent_probe_operator_probe_in_domain
      pp_t_closed_den_in_domain[OF typed_prop_id]])

lemma pp_t_recurrent_complemented_full_identity_section_in_domain:
  "Elem pp_t_recurrent_complemented_full_identity_section
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_pointwise_complement_in_domain)
    (rule pp_t_recurrent_full_identity_section_in_domain)

lemma pp_t_recurrent_identity_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_recurrent_identity_stock"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have XY_v: "pp_t_eqv pp_t_one_context_unary_type v X Y"
    by (rule pp_t_eqv_persistent[OF XY wv])
  have YX_v: "pp_t_eqv pp_t_one_context_unary_type v Y X"
    by (rule pp_t_eqv_symmetric[OF X Y XY_v])
  have base:
      "pp_t_recurrent_probe_stock v X
        \<longleftrightarrow>
       pp_t_recurrent_probe_stock v Y"
    using pp_t_recurrent_probe_stock_admissible
      X Y XY wv
    unfolding pp_t_predicate_admissible_def
    by blast
  have positive:
      "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_full_identity_section
        \<longleftrightarrow>
       pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_full_identity_section"
  proof
    assume XP:
        "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_full_identity_section"
    show "pp_t_eqv pp_t_one_context_unary_type v
        Y pp_t_recurrent_full_identity_section"
      by (rule pp_t_eqv_transitive[
        OF Y X pp_t_recurrent_full_identity_section_in_domain
          YX_v XP])
  next
    assume YP:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_full_identity_section"
    show "pp_t_eqv pp_t_one_context_unary_type v
        X pp_t_recurrent_full_identity_section"
      by (rule pp_t_eqv_transitive[
        OF X Y pp_t_recurrent_full_identity_section_in_domain
          XY_v YP])
  qed
  have negative:
      "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_complemented_full_identity_section
        \<longleftrightarrow>
       pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_complemented_full_identity_section"
  proof
    assume XN:
        "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_complemented_full_identity_section"
    show "pp_t_eqv pp_t_one_context_unary_type v
        Y pp_t_recurrent_complemented_full_identity_section"
      by (rule pp_t_eqv_transitive[
        OF Y X pp_t_recurrent_complemented_full_identity_section_in_domain
          YX_v XN])
  next
    assume YN:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_complemented_full_identity_section"
    show "pp_t_eqv pp_t_one_context_unary_type v
        X pp_t_recurrent_complemented_full_identity_section"
      by (rule pp_t_eqv_transitive[
        OF X Y pp_t_recurrent_complemented_full_identity_section_in_domain
          XY_v YN])
  qed
  show "pp_t_recurrent_identity_stock v X
      \<longleftrightarrow> pp_t_recurrent_identity_stock v Y"
    unfolding pp_t_recurrent_identity_stock_def
    using X Y base positive negative by blast
qed

lemma pp_t_recurrent_identity_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_recurrent_identity_stock w X"
  shows "pp_t_recurrent_identity_stock w
    (pp_t_pointwise_complement X)"
proof -
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  have base:
      "pp_t_recurrent_probe_stock w X
        \<Longrightarrow>
       pp_t_recurrent_identity_stock w
        (pp_t_pointwise_complement X)"
    unfolding pp_t_recurrent_identity_stock_def
    using NX pp_t_recurrent_probe_stock_negation_closed[OF X]
    by blast
  have from_positive:
      "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_full_identity_section
        \<Longrightarrow>
       pp_t_recurrent_identity_stock w
        (pp_t_pointwise_complement X)"
  proof -
    assume XP:
        "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_full_identity_section"
    have complements:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          pp_t_recurrent_complemented_full_identity_section"
      by (rule pp_t_pointwise_complement_respects_equivalence[
        OF X pp_t_recurrent_full_identity_section_in_domain XP])
    show ?thesis
      unfolding pp_t_recurrent_identity_stock_def
      using NX complements by blast
  qed
  have from_negative:
      "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_full_identity_section
        \<Longrightarrow>
       pp_t_recurrent_identity_stock w
        (pp_t_pointwise_complement X)"
  proof -
    assume XN:
        "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_full_identity_section"
    have complements:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement
            pp_t_recurrent_complemented_full_identity_section)"
      by (rule pp_t_pointwise_complement_respects_equivalence[
        OF X pp_t_recurrent_complemented_full_identity_section_in_domain
          XN])
    have involution:
        "pp_t_pointwise_complement
            pp_t_recurrent_complemented_full_identity_section
          =
         pp_t_recurrent_full_identity_section"
      by (rule pp_t_pointwise_complement_involution[
        OF pp_t_recurrent_full_identity_section_in_domain])
    have returned:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          pp_t_recurrent_full_identity_section"
      using complements
      unfolding involution .
    show ?thesis
      unfolding pp_t_recurrent_identity_stock_def
      using NX returned by blast
  qed
  show ?thesis
    using stock base from_positive from_negative
    unfolding pp_t_recurrent_identity_stock_def
    by blast
qed

theorem pp_t_recurrent_identity_stock_recombines:
  "pp_t_unary_recombines_at
    pp_t_recurrent_identity_stock
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_recurrent_identity_stock w X"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds
          (X \<acute> pp_t_probe_modal_boolean_recurrent_seed_at w) v"
    and q: "Elem q (pp_t_domain Prop)"
  let ?r = "pp_t_probe_modal_boolean_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_recurrent_seed_at_in_domain)
  have safe:
      "pp_t_recombination_safe_unary_operator X ?r w"
  proof -
    from stock have cases:
        "pp_t_recurrent_probe_stock w X
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_full_identity_section
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_full_identity_section"
      unfolding pp_t_recurrent_identity_stock_def by blast
    from cases show ?thesis
    proof
      assume base: "pp_t_recurrent_probe_stock w X"
      have recombines:
          "pp_t_unary_recombines_at
            pp_t_recurrent_probe_stock ?r w"
        by (rule pp_t_recurrent_probe_stock_recombines)
      show ?thesis
        using recombines X base
        unfolding pp_t_unary_recombines_at_def
          pp_t_recombination_safe_unary_operator_def
        by blast
    next
      assume generated:
          "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_full_identity_section
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_complemented_full_identity_section"
      from generated show ?thesis
      proof
        assume XP:
            "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_full_identity_section"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X pp_t_recurrent_full_identity_section_in_domain
              XP r
              pp_t_recurrent_full_identity_section_recombination_safe])
      next
        assume XN:
            "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_complemented_full_identity_section"
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X pp_t_recurrent_complemented_full_identity_section_in_domain
              XN r
              pp_t_recurrent_complemented_full_identity_section_recombination_safe])
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
