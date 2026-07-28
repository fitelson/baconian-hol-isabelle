theory Bacon_PP_Fresh_ZF_Modal_Quantified_Bridge
  imports
    "Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified.Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model"
    "Goodman_Fresh_ZF_Bridge.Bacon_PP_Fresh_ZF_Fragment_Bridge"
begin

section \<open>Necessity, possibility, and the six quantified operators\<close>

lemma pp_possibility_fragment_PP_axioms_subset_fresh_goodman:
  "pp_possibility_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
proof
  fix A
  assume A: "A \<in> pp_possibility_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_binary_truth_fragment_PP_axioms"
    | (necessity) "A = pp_necessity_purity_axiom"
    | (possibility) "A = pp_possibility_purity_axiom"
    unfolding pp_possibility_fragment_PP_axioms_def
      pp_necessity_fragment_PP_axioms_def
    by blast
  then show "A \<in> fresh_goodman_axioms"
  proof cases
    case old
    then show ?thesis
      using pp_binary_truth_fragment_PP_axioms_subset_fresh_goodman
      by blast
  next
    case necessity
    have "A \<in> pp_purity_schema"
      unfolding necessity
      by (rule pp_necessity_purity_axiom_in_schema)
    then show ?thesis
      unfolding fresh_goodman_axioms_def
        fresh_goodman_background_axioms_def
        pp_full_QLN_background_axioms_def
        pp_recombination_background_axioms_def
        pp_background_axioms_def
      by blast
  next
    case possibility
    have "A \<in> pp_purity_schema"
      unfolding possibility
      by (rule pp_possibility_purity_axiom_in_schema)
    then show ?thesis
      unfolding fresh_goodman_axioms_def
        fresh_goodman_background_axioms_def
        pp_full_QLN_background_axioms_def
        pp_recombination_background_axioms_def
        pp_background_axioms_def
      by blast
  qed
qed

lemma pp_quantified_fragment_PP_axioms_subset_fresh_goodman:
  "pp_quantified_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
proof
  fix A
  assume A: "A \<in> pp_quantified_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_possibility_fragment_PP_axioms"
    | (quantified) "A \<in> pp_HO_quantified_purity_axioms"
    unfolding pp_quantified_fragment_PP_axioms_def by blast
  then show "A \<in> fresh_goodman_axioms"
  proof cases
    case old
    then show ?thesis
      using pp_possibility_fragment_PP_axioms_subset_fresh_goodman
      by blast
  next
    case quantified
    then have "A \<in> pp_purity_schema"
      using pp_HO_quantified_purity_axioms_in_schema by blast
    then show ?thesis
      unfolding fresh_goodman_axioms_def
        fresh_goodman_background_axioms_def
        pp_full_QLN_background_axioms_def
        pp_recombination_background_axioms_def
        pp_background_axioms_def
      by blast
  qed
qed

definition pp_modal_quantified_allowed_purity :: "oterm set" where
  "pp_modal_quantified_allowed_purity =
    pp_binary_truth_allowed_purity
      \<union> {pp_necessity_purity_axiom,
        pp_possibility_purity_axiom}
      \<union> pp_HO_quantified_purity_axioms"

theorem fresh_goodman_modal_quantified_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> pp_modal_quantified_allowed_purity"
  shows "U \<subseteq> pp_quantified_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_quantified_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    have allowed: "A \<in> pp_modal_quantified_allowed_purity"
      using A True purity by blast
    show ?thesis
      using allowed
      unfolding pp_modal_quantified_allowed_purity_def
        pp_quantified_fragment_PP_axioms_def
        pp_possibility_fragment_PP_axioms_def
        pp_necessity_fragment_PP_axioms_def
        pp_binary_truth_allowed_purity_def
        pp_binary_truth_fragment_PP_axioms_def
        pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have background:
        "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have sparse: "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    show ?thesis
      using sparse
      unfolding pp_quantified_fragment_PP_axioms_def
        pp_possibility_fragment_PP_axioms_def
        pp_necessity_fragment_PP_axioms_def
        pp_binary_truth_fragment_PP_axioms_def
        pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_modal_quantified_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> pp_modal_quantified_allowed_purity"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_modal_quantified_only_subset[
    OF subset purity]
  by (rule pp_quantified_fragment_consistent)

corollary pp_quantified_fragment_is_goodman_consistent:
  "pp_quantified_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_quantified_fragment_PP_axioms"
  using
    pp_quantified_fragment_PP_axioms_subset_fresh_goodman
    pp_quantified_fragment_PP_axioms_consistent
  by blast

end
