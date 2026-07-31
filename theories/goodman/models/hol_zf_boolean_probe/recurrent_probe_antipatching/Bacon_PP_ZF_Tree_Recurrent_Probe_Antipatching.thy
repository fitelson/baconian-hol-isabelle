theory Bacon_PP_ZF_Tree_Recurrent_Probe_Antipatching
  imports
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stabilization.Bacon_PP_ZF_Tree_Recurrent_Probe_Stabilization
begin

section \<open>The two remaining seed obligations for a generated section\<close>

definition pp_t_operator_boundary_recurrence ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_operator_boundary_recurrence R F w
    \<longleftrightarrow>
    (\<exists>v. prefix w v
      \<and> pp_t_fundamental_boundary (R v) v (F \<acute> R w))"

definition pp_t_operator_boundary_antipatching ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF
      \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_operator_boundary_antipatching R F X w
    \<longleftrightarrow>
    ((\<not> (\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w))
      \<longrightarrow>
     (\<exists>v. prefix w v
        \<and> \<not> pp_t_holds (X \<acute> R w) v
        \<and> \<not> pp_t_fundamental_boundary
          (R v) v (F \<acute> R w)))"

lemma pp_t_generated_boundary_disjunction_recombination_safe:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and antipatching:
      "pp_t_operator_boundary_antipatching R F X w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction X
        (pp_t_moving_boundary_operator_probe R \<acute> F))
      (R w) w"
proof (unfold pp_t_recombination_safe_unary_operator_def,
    intro impI)
  let ?B = "pp_t_moving_boundary_operator_probe R \<acute> F"
  let ?C = "pp_t_unary_output_disjunction X ?B"
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (?C \<acute> R w) v"
  show "\<forall>q. Elem q (pp_t_domain Prop)
      \<longrightarrow> pp_t_holds (?C \<acute> q) w"
  proof (cases
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w")
    case True
    show ?thesis
    proof (intro allI impI)
      fix q
      assume q: "Elem q (pp_t_domain Prop)"
      have Xq: "pp_t_holds (X \<acute> q) w"
        using True q by blast
      show "pp_t_holds (?C \<acute> q) w"
        using pp_t_unary_output_disjunction_apply_holds[
          OF X B q, of w]
          Xq by blast
    qed
  next
    case False
    obtain v where wv: "prefix w v"
      and not_X: "\<not> pp_t_holds (X \<acute> R w) v"
      and not_boundary:
        "\<not> pp_t_fundamental_boundary
          (R v) v (F \<acute> R w)"
      using antipatching False
      unfolding pp_t_operator_boundary_antipatching_def
      by blast
    have r: "Elem (R w) (pp_t_domain Prop)"
      by (rule R)
    have not_B: "\<not> pp_t_holds (?B \<acute> R w) v"
      using pp_t_moving_boundary_operator_probe_apply_holds[
        where R=R and w=v and p="R w",
        OF R[of v] F r]
        not_boundary by blast
    have C:
        "pp_t_holds (?C \<acute> R w) v"
      using necessary wv by blast
    have "pp_t_holds (X \<acute> R w) v
        \<or> pp_t_holds (?B \<acute> R w) v"
      using pp_t_unary_output_disjunction_apply_holds[
        OF X B r, of v]
        C by blast
    then show ?thesis
      using not_X not_B by blast
  qed
qed

lemma pp_t_complemented_generated_boundary_disjunction_recombination_safe:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and recurrence: "pp_t_operator_boundary_recurrence R F w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_unary_output_disjunction X
          (pp_t_moving_boundary_operator_probe R \<acute> F)))
      (R w) w"
proof (unfold pp_t_recombination_safe_unary_operator_def,
    intro impI)
  let ?B = "pp_t_moving_boundary_operator_probe R \<acute> F"
  let ?C = "pp_t_unary_output_disjunction X ?B"
  let ?N = "pp_t_pointwise_complement ?C"
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  have C:
      "Elem ?C (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_unary_output_disjunction_in_domain[OF X B])
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (?N \<acute> R w) v"
  obtain v where wv: "prefix w v"
    and boundary:
      "pp_t_fundamental_boundary (R v) v (F \<acute> R w)"
    using recurrence
    unfolding pp_t_operator_boundary_recurrence_def by blast
  have r: "Elem (R w) (pp_t_domain Prop)"
    by (rule R)
  have B_true: "pp_t_holds (?B \<acute> R w) v"
    using pp_t_moving_boundary_operator_probe_apply_holds[
      where R=R and w=v and p="R w",
      OF R[of v] F r]
      boundary by blast
  have C_true: "pp_t_holds (?C \<acute> R w) v"
    using pp_t_unary_output_disjunction_apply_holds[
      OF X B r, of v]
      B_true by blast
  have N_true: "pp_t_holds (?N \<acute> R w) v"
    using necessary wv by blast
  show "\<forall>q. Elem q (pp_t_domain Prop)
      \<longrightarrow> pp_t_holds (?N \<acute> q) w"
    using pp_t_pointwise_complement_holds[
      OF r, of ?C v]
      C_true N_true by simp
qed

section \<open>Instantiation to the stabilized classifier range\<close>

abbreviation pp_t_recurrent_modal_component :: "ZF \<Rightarrow> ZF"
where
  "pp_t_recurrent_modal_component F \<equiv>
    pp_t_modal_singleton_operator_probe \<acute> F"

lemma pp_t_recurrent_modal_component_in_domain:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "Elem (pp_t_recurrent_modal_component F)
      (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_app_closed[
    OF pp_t_modal_singleton_operator_probe_in_domain F])

theorem pp_t_recurrent_full_section_recombination_safe:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and antipatching:
      "pp_t_operator_boundary_antipatching
        pp_t_probe_modal_boolean_recurrent_seed_at F
        (pp_t_recurrent_modal_component F) w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_recurrent_probe_operator_probe \<acute> F)
      (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
proof -
  have decomposed:
      "pp_t_recurrent_probe_operator_probe \<acute> F
        =
       pp_t_unary_output_disjunction
         (pp_t_recurrent_modal_component F)
         (pp_t_moving_boundary_operator_probe
            pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)"
    by (rule
      pp_t_recurrent_probe_full_classifier_decomposition[OF F])
  show ?thesis
    unfolding decomposed
    by (rule pp_t_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain F
        pp_t_recurrent_modal_component_in_domain[OF F]
        antipatching])
qed

theorem pp_t_recurrent_complemented_full_section_recombination_safe:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and recurrence:
      "pp_t_operator_boundary_recurrence
        pp_t_probe_modal_boolean_recurrent_seed_at F w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_pointwise_complement
        (pp_t_recurrent_probe_operator_probe \<acute> F))
      (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
proof -
  have decomposed:
      "pp_t_recurrent_probe_operator_probe \<acute> F
        =
       pp_t_unary_output_disjunction
         (pp_t_recurrent_modal_component F)
         (pp_t_moving_boundary_operator_probe
            pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)"
    by (rule
      pp_t_recurrent_probe_full_classifier_decomposition[OF F])
  show ?thesis
    unfolding decomposed
    by (rule
      pp_t_complemented_generated_boundary_disjunction_recombination_safe[
        OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain F
          pp_t_recurrent_modal_component_in_domain[OF F]
          recurrence])
qed

section \<open>The identity section\<close>

lemma pp_t_identity_boundary_recurrence_iff_seed_recurrence:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
  shows
    "pp_t_operator_boundary_recurrence
        R (pp_t_closed_den prop_id) w
      \<longleftrightarrow>
     pp_t_seed_boundary_recurrence R w"
  unfolding pp_t_operator_boundary_recurrence_def
    pp_t_seed_boundary_recurrence_def
    pp_t_closed_identity_apply[OF R[of w]]
  by simp

lemma pp_t_recurrent_identity_boundary_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_recurrent_seed_at
    (pp_t_closed_den prop_id) w"
  using pp_t_probe_modal_boolean_recurrent_seed_recurrence[of w]
  unfolding pp_t_identity_boundary_recurrence_iff_seed_recurrence[
    OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain] .

lemma pp_t_recurrent_modal_identity_component_false_on_seed:
  "\<not> pp_t_holds
    (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
      \<acute> pp_t_probe_modal_boolean_recurrent_seed_at w) w"
proof -
  let ?r = "pp_t_probe_modal_boolean_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_recurrent_seed_at_in_domain)
  have not_singleton:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?r)"
  proof
    assume singleton:
        "pp_t_probe_modal_boolean_stock w
          (pp_t_singleton_family_at ?r)"
    have not_reflexive: "\<not> pp_t_eqv Prop w ?r ?r"
      by (rule
        pp_t_pure_singleton_parameter_not_currently_fundamental[
          where Pure=pp_t_probe_modal_boolean_stock,
          OF r r singleton
            pp_t_probe_modal_boolean_recurrent_seed_recombines])
    show False
      using not_reflexive pp_t_eqv_reflexive[OF r, of w]
      by blast
  qed
  have component:
      "pp_t_holds
          (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
            \<acute> ?r) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at
          (pp_t_closed_den prop_id \<acute> ?r))"
    by (rule pp_t_modal_singleton_operator_probe_apply_holds[
      OF pp_t_closed_den_in_domain[OF typed_prop_id] r])
  show ?thesis
    using component not_singleton
    unfolding pp_t_closed_identity_apply[OF r]
    by blast
qed

lemma pp_t_recurrent_identity_boundary_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_recurrent_seed_at
    (pp_t_closed_den prop_id)
    (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)) w"
proof (unfold pp_t_operator_boundary_antipatching_def,
    intro impI)
  let ?r = "pp_t_probe_modal_boolean_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_recurrent_seed_at_in_domain)
  have not_component:
      "\<not> pp_t_holds
        (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
          \<acute> ?r) w"
    by (rule pp_t_recurrent_modal_identity_component_false_on_seed)
  have not_boundary:
      "\<not> pp_t_fundamental_boundary ?r w
        (pp_t_closed_den prop_id \<acute> ?r)"
    unfolding pp_t_closed_identity_apply[OF r]
      pp_t_fundamental_boundary_def
    using pp_t_eqv_reflexive[OF r, of w]
    by blast
  show "\<exists>v. prefix w v
      \<and> \<not> pp_t_holds
        (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
          \<acute> ?r) v
      \<and> \<not> pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_recurrent_seed_at v) v
        (pp_t_closed_den prop_id \<acute> ?r)"
    using not_component not_boundary
    by (intro exI[of _ w]) simp
qed

theorem
  pp_t_recurrent_complemented_full_identity_section_recombination_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_recurrent_probe_operator_probe
        \<acute> pp_t_closed_den prop_id))
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  by (rule
    pp_t_recurrent_complemented_full_section_recombination_safe[
      OF pp_t_closed_den_in_domain[OF typed_prop_id]
        pp_t_recurrent_identity_boundary_recurrence])

theorem pp_t_recurrent_full_identity_section_recombination_safe_if:
  assumes antipatching:
      "pp_t_operator_boundary_antipatching
        pp_t_probe_modal_boolean_recurrent_seed_at
        (pp_t_closed_den prop_id)
        (pp_t_recurrent_modal_component
          (pp_t_closed_den prop_id)) w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_recurrent_probe_operator_probe
        \<acute> pp_t_closed_den prop_id)
      (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  by (rule pp_t_recurrent_full_section_recombination_safe[
    OF pp_t_closed_den_in_domain[OF typed_prop_id] antipatching])

corollary pp_t_recurrent_full_identity_section_recombination_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_recurrent_probe_operator_probe
      \<acute> pp_t_closed_den prop_id)
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  by (rule
    pp_t_recurrent_full_identity_section_recombination_safe_if[
      OF pp_t_recurrent_identity_boundary_antipatching])

end
