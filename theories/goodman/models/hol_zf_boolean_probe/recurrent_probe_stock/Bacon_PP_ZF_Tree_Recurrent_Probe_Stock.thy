theory Bacon_PP_ZF_Tree_Recurrent_Probe_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Generic_Seed.Bacon_PP_ZF_Tree_Recurrent_Generic_Seed
begin

section \<open>The recurrent modal-boundary stock\<close>

definition pp_t_recurrent_modal_boundary_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_recurrent_modal_boundary_stock w X
    \<longleftrightarrow>
    pp_t_probe_modal_boolean_stock w X
    \<or>
    pp_t_moving_boundary_singleton_stock
      pp_t_probe_modal_boolean_recurrent_seed_at w X"

lemma pp_t_recurrent_modal_boundary_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_recurrent_modal_boundary_stock"
proof -
  have modal:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        pp_t_probe_modal_boolean_stock"
    by (rule pp_t_probe_modal_boolean_stock_admissible)
  have boundary:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_recurrent_seed_at)"
    by (rule pp_t_moving_boundary_singleton_stock_admissible)
  show ?thesis
    using modal boundary
    unfolding pp_t_predicate_admissible_def
      pp_t_recurrent_modal_boundary_stock_def
    by blast
qed

lemma pp_t_recurrent_modal_boundary_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_recurrent_modal_boundary_stock w X"
  shows "pp_t_recurrent_modal_boundary_stock w
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
          pp_t_probe_modal_boolean_recurrent_seed_at w X
        \<Longrightarrow>
       pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_recurrent_seed_at w
          (pp_t_pointwise_complement X)"
    by (rule
      pp_t_moving_boundary_singleton_stock_negation_closed[OF X])
  show ?thesis
    using stock modal boundary
    unfolding pp_t_recurrent_modal_boundary_stock_def
    by blast
qed

theorem pp_t_recurrent_modal_boundary_stock_recombines:
  "pp_t_unary_recombines_at
    pp_t_recurrent_modal_boundary_stock
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
proof -
  have modal:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock
        (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
    by (rule pp_t_probe_modal_boolean_recurrent_seed_recombines)
  have boundary:
      "pp_t_unary_recombines_at
        (pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_recurrent_seed_at)
        (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
    by (rule pp_t_moving_boundary_singleton_stock_recombines)
      (rule pp_t_probe_modal_boolean_recurrent_seed_at_in_domain)
  show ?thesis
    using modal boundary
    unfolding pp_t_unary_recombines_at_def
      pp_t_recurrent_modal_boundary_stock_def
    by blast
qed

section \<open>Adjoining the first generated boundary probe\<close>

abbreviation pp_t_recurrent_boundary_probe :: ZF
where
  "pp_t_recurrent_boundary_probe \<equiv>
    pp_t_moving_boundary_identity_probe
      pp_t_probe_modal_boolean_recurrent_seed_at"

abbreviation pp_t_recurrent_complemented_boundary_probe :: ZF
where
  "pp_t_recurrent_complemented_boundary_probe \<equiv>
    pp_t_pointwise_complement pp_t_recurrent_boundary_probe"

definition pp_t_recurrent_probe_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_recurrent_probe_stock w X
    \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_one_context_unary_type)
    \<and>
    (pp_t_recurrent_modal_boundary_stock w X
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w
        X pp_t_recurrent_boundary_probe
      \<or>
     pp_t_eqv pp_t_one_context_unary_type w
        X pp_t_recurrent_complemented_boundary_probe)"

lemma pp_t_recurrent_boundary_probe_in_domain:
  "Elem pp_t_recurrent_boundary_probe
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_moving_boundary_identity_probe_in_domain)

lemma pp_t_recurrent_complemented_boundary_probe_in_domain:
  "Elem pp_t_recurrent_complemented_boundary_probe
    (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_pointwise_complement_in_domain)
    (rule pp_t_recurrent_boundary_probe_in_domain)

lemma pp_t_recurrent_probe_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_recurrent_probe_stock"
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
      "pp_t_recurrent_modal_boundary_stock v X
        \<longleftrightarrow>
       pp_t_recurrent_modal_boundary_stock v Y"
    using pp_t_recurrent_modal_boundary_stock_admissible
      X Y XY wv
    unfolding pp_t_predicate_admissible_def
    by blast
  have P:
      "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_boundary_probe
        \<longleftrightarrow>
       pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_boundary_probe"
  proof
    assume XP:
        "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_boundary_probe"
    show "pp_t_eqv pp_t_one_context_unary_type v
        Y pp_t_recurrent_boundary_probe"
      by (rule pp_t_eqv_transitive[
        OF Y X pp_t_recurrent_boundary_probe_in_domain YX_v XP])
  next
    assume YP:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_boundary_probe"
    show "pp_t_eqv pp_t_one_context_unary_type v
        X pp_t_recurrent_boundary_probe"
      by (rule pp_t_eqv_transitive[
        OF X Y pp_t_recurrent_boundary_probe_in_domain XY_v YP])
  qed
  have N:
      "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_complemented_boundary_probe
        \<longleftrightarrow>
       pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_complemented_boundary_probe"
  proof
    assume XN:
        "pp_t_eqv pp_t_one_context_unary_type v
          X pp_t_recurrent_complemented_boundary_probe"
    show "pp_t_eqv pp_t_one_context_unary_type v
        Y pp_t_recurrent_complemented_boundary_probe"
      by (rule pp_t_eqv_transitive[
        OF Y X pp_t_recurrent_complemented_boundary_probe_in_domain
          YX_v XN])
  next
    assume YN:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y pp_t_recurrent_complemented_boundary_probe"
    show "pp_t_eqv pp_t_one_context_unary_type v
        X pp_t_recurrent_complemented_boundary_probe"
      by (rule pp_t_eqv_transitive[
        OF X Y pp_t_recurrent_complemented_boundary_probe_in_domain
          XY_v YN])
  qed
  show "pp_t_recurrent_probe_stock v X
      \<longleftrightarrow> pp_t_recurrent_probe_stock v Y"
    unfolding pp_t_recurrent_probe_stock_def
    using X Y base P N by blast
qed

lemma pp_t_recurrent_probe_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_recurrent_probe_stock w X"
  shows "pp_t_recurrent_probe_stock w
    (pp_t_pointwise_complement X)"
proof -
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  have base:
      "pp_t_recurrent_modal_boundary_stock w X
        \<Longrightarrow>
       pp_t_recurrent_probe_stock w
        (pp_t_pointwise_complement X)"
    unfolding pp_t_recurrent_probe_stock_def
    using NX pp_t_recurrent_modal_boundary_stock_negation_closed[
      OF X]
    by blast
  have from_P:
      "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_boundary_probe
        \<Longrightarrow>
       pp_t_recurrent_probe_stock w
        (pp_t_pointwise_complement X)"
  proof -
    assume XP:
        "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_boundary_probe"
    have complements:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          pp_t_recurrent_complemented_boundary_probe"
      by (rule pp_t_pointwise_complement_respects_equivalence[
        OF X pp_t_recurrent_boundary_probe_in_domain XP])
    show ?thesis
      unfolding pp_t_recurrent_probe_stock_def
      using NX complements by blast
  qed
  have from_N:
      "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_boundary_probe
        \<Longrightarrow>
       pp_t_recurrent_probe_stock w
        (pp_t_pointwise_complement X)"
  proof -
    assume XN:
        "pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_boundary_probe"
    have complements:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement
            pp_t_recurrent_complemented_boundary_probe)"
      by (rule pp_t_pointwise_complement_respects_equivalence[
        OF X pp_t_recurrent_complemented_boundary_probe_in_domain XN])
    have involution:
        "pp_t_pointwise_complement
            pp_t_recurrent_complemented_boundary_probe
          =
         pp_t_recurrent_boundary_probe"
      by (rule pp_t_pointwise_complement_involution[
        OF pp_t_recurrent_boundary_probe_in_domain])
    show ?thesis
      unfolding pp_t_recurrent_probe_stock_def
    proof (intro conjI)
      show "Elem (pp_t_pointwise_complement X)
          (pp_t_domain pp_t_one_context_unary_type)"
        by (rule NX)
      show "pp_t_recurrent_modal_boundary_stock w
            (pp_t_pointwise_complement X)
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_pointwise_complement X)
            pp_t_recurrent_boundary_probe
          \<or>
          pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_pointwise_complement X)
            pp_t_recurrent_complemented_boundary_probe"
      proof (rule disjI2, rule disjI1)
        from complements show
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_pointwise_complement X)
            pp_t_recurrent_boundary_probe"
          by (simp only: involution)
      qed
    qed
  qed
  show ?thesis
    using stock base from_P from_N
    unfolding pp_t_recurrent_probe_stock_def
    by blast
qed

lemma pp_t_equivalent_recombination_safe_operator:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and r: "Elem r (pp_t_domain Prop)"
    and safe: "pp_t_recombination_safe_unary_operator Y r w"
  shows "pp_t_recombination_safe_unary_operator X r w"
proof (unfold pp_t_recombination_safe_unary_operator_def,
    intro impI)
  assume X_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> r) v"
  have Y_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (Y \<acute> r) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have XY_v: "pp_t_eqv pp_t_one_context_unary_type v X Y"
      by (rule pp_t_eqv_persistent[OF XY wv])
    have rr: "pp_t_eqv Prop v r r"
      by (rule pp_t_eqv_reflexive[OF r])
    have applications: "pp_t_eqv Prop v (X \<acute> r) (Y \<acute> r)"
      by (rule pp_t_app_respects[OF XY_v r r rr])
    show "pp_t_holds (Y \<acute> r) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        X_necessary[rule_format, OF wv]
      by simp
  qed
  have Y_universal:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (Y \<acute> q) w"
    using safe Y_necessary
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
  show "\<forall>q. Elem q (pp_t_domain Prop)
      \<longrightarrow> pp_t_holds (X \<acute> q) w"
  proof (intro allI impI)
    fix q
    assume q: "Elem q (pp_t_domain Prop)"
    have qq: "pp_t_eqv Prop w q q"
      by (rule pp_t_eqv_reflexive[OF q])
    have applications: "pp_t_eqv Prop w (X \<acute> q) (Y \<acute> q)"
      by (rule pp_t_app_respects[OF XY q q qq])
    show "pp_t_holds (X \<acute> q) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        Y_universal[rule_format, OF q]
      by simp
  qed
qed

theorem pp_t_recurrent_probe_stock_recombines:
  "pp_t_unary_recombines_at
    pp_t_recurrent_probe_stock
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
proof (unfold pp_t_unary_recombines_at_def,
    intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_recurrent_probe_stock w X"
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
        "pp_t_recurrent_modal_boundary_stock w X
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_boundary_probe
        \<or>
         pp_t_eqv pp_t_one_context_unary_type w
          X pp_t_recurrent_complemented_boundary_probe"
      unfolding pp_t_recurrent_probe_stock_def by blast
    from cases show ?thesis
    proof
      assume base: "pp_t_recurrent_modal_boundary_stock w X"
      have recombines:
          "pp_t_unary_recombines_at
            pp_t_recurrent_modal_boundary_stock ?r w"
        by (rule pp_t_recurrent_modal_boundary_stock_recombines)
      show ?thesis
        using recombines X base
        unfolding pp_t_unary_recombines_at_def
          pp_t_recombination_safe_unary_operator_def
        by blast
    next
      assume generated:
          "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_boundary_probe
          \<or>
           pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_complemented_boundary_probe"
      from generated show ?thesis
      proof
        assume XP:
            "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_boundary_probe"
        have P_safe:
            "pp_t_recombination_safe_unary_operator
              pp_t_recurrent_boundary_probe ?r w"
          by (rule
            pp_t_moving_boundary_identity_probe_recombination_safe)
            (rule
              pp_t_probe_modal_boolean_recurrent_seed_at_in_domain)
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X pp_t_recurrent_boundary_probe_in_domain XP r P_safe])
      next
        assume XN:
            "pp_t_eqv pp_t_one_context_unary_type w
              X pp_t_recurrent_complemented_boundary_probe"
        have N_safe:
            "pp_t_recombination_safe_unary_operator
              pp_t_recurrent_complemented_boundary_probe ?r w"
          by (rule
            pp_t_recurrent_seed_complemented_boundary_probe_recombination_safe)
        show ?thesis
          by (rule pp_t_equivalent_recombination_safe_operator[
            OF X pp_t_recurrent_complemented_boundary_probe_in_domain
              XN r N_safe])
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
