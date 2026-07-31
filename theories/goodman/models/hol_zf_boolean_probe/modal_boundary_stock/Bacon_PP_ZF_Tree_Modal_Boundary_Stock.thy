theory Bacon_PP_ZF_Tree_Modal_Boundary_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Boundary_Singleton_Stock.Bacon_PP_ZF_Tree_Boundary_Singleton_Stock
    Higher_Order_Metaphysics_PP_ZF_Modal_Boolean_Probe.Bacon_PP_ZF_Tree_Modal_Boolean_Probe
begin

section \<open>The modal-Boolean stock with its moving boundary\<close>

definition pp_t_modal_boundary_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_modal_boundary_stock w X
    \<longleftrightarrow>
    pp_t_probe_modal_boolean_stock w X
    \<or>
    pp_t_moving_boundary_singleton_stock
      pp_t_probe_modal_boolean_stock_seed_at w X"

lemma pp_t_pointwise_complement_eq_unary_complement:
  "pp_t_pointwise_complement X = pp_t_unary_complement X"
  unfolding pp_t_pointwise_complement_def
    pp_t_unary_complement_def
  by simp

lemma pp_t_modal_boundary_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    pp_t_modal_boundary_stock"
proof -
  have modal:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        pp_t_probe_modal_boolean_stock"
    by (rule pp_t_probe_modal_boolean_stock_admissible)
  have boundary:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_stock_seed_at)"
    by (rule pp_t_moving_boundary_singleton_stock_admissible)
  show ?thesis
    using modal boundary
    unfolding pp_t_predicate_admissible_def
      pp_t_modal_boundary_stock_def
    by blast
qed

lemma pp_t_modal_boundary_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_modal_boundary_stock w X"
  shows "pp_t_modal_boundary_stock w
    (pp_t_pointwise_complement X)"
proof -
  have modal:
      "pp_t_probe_modal_boolean_stock w X \<Longrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_pointwise_complement X)"
  proof -
    assume modal_X: "pp_t_probe_modal_boolean_stock w X"
    show ?thesis
      unfolding pp_t_pointwise_complement_eq_unary_complement
      by (rule
        pp_t_probe_modal_boolean_stock_unary_complement_closed[
          OF X modal_X])
  qed
  have boundary:
      "pp_t_moving_boundary_singleton_stock
        pp_t_probe_modal_boolean_stock_seed_at w X \<Longrightarrow>
       pp_t_moving_boundary_singleton_stock
        pp_t_probe_modal_boolean_stock_seed_at w
        (pp_t_pointwise_complement X)"
    by (rule
      pp_t_moving_boundary_singleton_stock_negation_closed[OF X])
  show ?thesis
    using stock modal boundary
    unfolding pp_t_modal_boundary_stock_def
    by blast
qed

theorem pp_t_modal_boundary_stock_recombines_at_every_world:
  "pp_t_unary_recombines_at
    pp_t_modal_boundary_stock
    (pp_t_probe_modal_boolean_stock_seed_at w) w"
proof -
  have modal:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock
        (pp_t_probe_modal_boolean_stock_seed_at w) w"
    by (rule
      pp_t_probe_modal_boolean_stock_seed_recombines_at_every_world)
  have boundary:
      "pp_t_unary_recombines_at
        (pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_stock_seed_at)
        (pp_t_probe_modal_boolean_stock_seed_at w) w"
    by (rule pp_t_moving_boundary_singleton_stock_recombines)
      (rule pp_t_probe_modal_boolean_stock_seed_at_in_domain)
  show ?thesis
    using modal boundary
    unfolding pp_t_unary_recombines_at_def
      pp_t_modal_boundary_stock_def
    by blast
qed

end
