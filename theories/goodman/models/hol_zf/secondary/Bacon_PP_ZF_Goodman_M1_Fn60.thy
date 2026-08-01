theory Bacon_PP_ZF_Goodman_M1_Fn60
  imports Bacon_PP_ZF_Tree_Generic_Seed
begin

section \<open>Goodman M1 in the secondary Boolean-tree model\<close>

text \<open>
  This theory is retained as a comparison calculation.  The exact-carrier
  classifier and PP equivalence are proved in \<open>Bacon_PP_ZF_Exact_M1\<close>.
\<close>

abbreviation pp_t_M1_unary_type :: otype where
  "pp_t_M1_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_M1_fn60_classifier :: ZF where
  "pp_t_M1_fn60_classifier \<equiv>
    pp_t_classifier pp_t_M1_unary_type
      (pp_t_closed_logical_stock pp_t_M1_unary_type)"

theorem pp_t_M1_fn60_classifier_in_full_domain:
  "Elem pp_t_M1_fn60_classifier
    (pp_t_domain (pp_t_M1_unary_type \<rightarrow>\<^sub>o Prop))"
  by (rule pp_t_classifier_in_domain[
      OF pp_t_closed_logical_stock_admissible])

theorem pp_t_M1_fn60_classifier_exact_extension:
  assumes X: "Elem X (pp_t_domain pp_t_M1_unary_type)"
  shows "pp_t_holds (pp_t_M1_fn60_classifier \<acute> X) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_M1_unary_type w X"
  by (rule pp_t_classifier_holds[OF X])

text \<open>
  The interpretation of \<open>Pure\<close> at the unary-operator type is exactly
  this classifier.  PP at that type therefore holds precisely when the
  classifier is itself in the next pure stock.  Thus completeness of the
  function domain supplies the infinitary join, but not its purity.
\<close>

theorem pp_t_M1_fn60_is_Pure_interpretation:
  "pp_t_eval pp_t_generic_internal_constants \<rho>
      (pp_Pure pp_t_M1_unary_type)
    = pp_t_M1_fn60_classifier"
  by simp

theorem pp_t_M1_fn60_PP_iff_classifier_pure_at_world:
  "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        pp_target_PP) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      (pp_t_M1_unary_type \<rightarrow>\<^sub>o Prop) w
      pp_t_M1_fn60_classifier"
  by (rule pp_t_generic_target_PP_holds_iff)

corollary pp_t_M1_fn60_global_PP_iff_classifier_pure_at_root:
  "GenericTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      (pp_t_M1_unary_type \<rightarrow>\<^sub>o Prop) []
      pp_t_M1_fn60_classifier"
  by (rule pp_t_generic_recombination_PP_gvalid_iff_root)

end
