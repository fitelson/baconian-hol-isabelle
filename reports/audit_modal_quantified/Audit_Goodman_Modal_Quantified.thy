theory Audit_Goodman_Modal_Quantified
  imports
    Goodman_Modal_Quantified_ZF_Bridge.Bacon_PP_Fresh_ZF_Modal_Quantified_Bridge
begin

section \<open>Kernel theorem-object audit\<close>

ML \<open>
fun require_clean (name, thm) =
  let
    val oracles = Thm_Deps.all_oracles [thm]
    val hyps = Thm.hyps_of thm
    val tpairs = Thm.tpairs_of thm
    val clean = null oracles andalso null hyps andalso null tpairs
    val line = name
      ^ ": oracles=" ^ string_of_int (length oracles)
      ^ " hyps=" ^ string_of_int (length hyps)
      ^ " tpairs=" ^ string_of_int (length tpairs)
  in
    if clean then (true, line ^ " [CLEAN]")
    else (false, line ^ " [PROBLEM]")
  end

val targets = [
  ("necessity global validity",
    @{thm pp_t_necessity_fragment_PP_gvalid}),
  ("necessity consistency",
    @{thm pp_necessity_fragment_PP_axioms_consistent}),
  ("possibility global validity",
    @{thm pp_t_possibility_fragment_PP_gvalid}),
  ("possibility consistency",
    @{thm pp_possibility_fragment_PP_axioms_consistent}),
  ("Leibniz truth is necessity",
    @{thm pp_t_HO_leibniz_truth_eqv_necessity}),
  ("Leibniz falsity is necessary falsity",
    @{thm pp_t_HO_leibniz_false_eqv_necessary_falsity}),
  ("negated Leibniz truth is possible falsity",
    @{thm pp_t_HO_not_leibniz_truth_eqv_possible_falsity}),
  ("negated Leibniz falsity is possibility",
    @{thm pp_t_HO_not_leibniz_false_eqv_possibility}),
  ("universal application is constant falsity",
    @{thm pp_t_HO_forall_application_eqv_constant_falsity}),
  ("existential application is constant truth",
    @{thm pp_t_HO_exists_application_eqv_constant_truth}),
  ("Leibniz truth is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(1)}),
  ("Leibniz falsity is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(2)}),
  ("negated Leibniz truth is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(3)}),
  ("negated Leibniz falsity is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(4)}),
  ("universal application is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(5)}),
  ("existential application is pure",
    @{thm pp_t_HO_quantified_terms_are_pure(6)}),
  ("necessary-falsity Recombination",
    @{thm pp_t_necessary_falsity_class_QLN(1)}),
  ("necessary-falsity Exhaustion",
    @{thm pp_t_necessary_falsity_class_QLN(2)}),
  ("possible-falsity Recombination",
    @{thm pp_t_possible_falsity_class_QLN(1)}),
  ("possible-falsity Exhaustion",
    @{thm pp_t_possible_falsity_class_QLN(2)}),
  ("quantified-stock unary Recombination",
    @{thm pp_t_quantified_pure_unary_QLN(1)}),
  ("quantified-stock unary Exhaustion",
    @{thm pp_t_quantified_pure_unary_QLN(2)}),
  ("quantified-stock application closure",
    @{thm pp_t_quantified_fragment_application}),
  ("quantified-stock PP",
    @{thm pp_t_quantified_target_PP_gvalid}),
  ("quantified-stock Modalized Functionality",
    @{thm pp_t_quantified_modalized_functionality_gvalid}),
  ("quantified-stock global validity",
    @{thm pp_t_quantified_fragment_PP_gvalid}),
  ("quantified-stock consistency",
    @{thm pp_quantified_fragment_PP_axioms_consistent}),
  ("quantified stock is within Goodman's principles",
    @{thm pp_quantified_fragment_PP_axioms_subset_fresh_goodman}),
  ("Goodman restricted-stock consistency",
    @{thm fresh_goodman_modal_quantified_only_consistent}),
  ("exact Goodman restricted-stock consistency",
    @{thm pp_quantified_fragment_is_goodman_consistent})
]

val results = map require_clean targets
val report = cat_lines (map #2 results)
val _ =
  if forall #1 results
  then writeln
    ("GOODMAN-MODAL-QUANTIFIED-AUDIT-KERNEL-CLEAN\n" ^ report)
  else error
    ("GOODMAN-MODAL-QUANTIFIED-AUDIT-PROBLEM\n" ^ report)
\<close>

end
