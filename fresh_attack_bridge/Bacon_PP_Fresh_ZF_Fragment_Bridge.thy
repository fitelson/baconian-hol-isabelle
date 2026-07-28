theory Bacon_PP_Fresh_ZF_Fragment_Bridge
  imports
    "Higher_Order_Metaphysics_PP_ZF_Truth_Functions.Bacon_PP_ZF_Fresh_Binary_Truth_Functions_Fragment_Model"
    "Goodman_Fresh_Attack.Bacon_PP_Fresh_Finite_Fragment"
begin

section \<open>The sparse model stated in the fresh formulation\<close>

lemma fresh_modalized_functionality_eq:
  "fresh_modalized_functionality \<sigma> \<tau> =
    pp_modalized_functionality \<sigma> \<tau>"
  unfolding fresh_modalized_functionality_def
    pp_modalized_functionality_def
  by simp

lemma fresh_modalized_functionality_schema_eq:
  "fresh_modalized_functionality_schema =
    pp_modalized_functionality_schema"
  unfolding fresh_modalized_functionality_schema_def
    pp_modalized_functionality_schema_def
  by (auto simp: fresh_modalized_functionality_eq)

lemma fresh_goodman_without_logical_purity_subset_sparse:
  "fresh_goodman_axioms - pp_purity_schema
    \<subseteq> pp_fresh_sparse_PP_axioms"
proof
  fix A
  assume A:
      "A \<in> fresh_goodman_axioms - pp_purity_schema"
  then have fresh: "A \<in> fresh_goodman_axioms"
    and not_purity: "A \<notin> pp_purity_schema"
    by auto
  from fresh consider
      (target) "A = pp_target_PP"
    | (purity) "A \<in> pp_purity_schema"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> fresh_modalized_functionality_schema"
    unfolding fresh_goodman_axioms_def
      fresh_goodman_background_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show "A \<in> pp_fresh_sparse_PP_axioms"
  proof cases
    case target
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def by simp
  next
    case purity
    then show ?thesis
      using not_purity by blast
  next
    case application
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  next
    case unique
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  next
    case no_other
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  next
    case zeroary_recombination
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  next
    case unary_recombination
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  next
    case zeroary_exhaustion
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
        pp_exhaustion_axioms_def
      by blast
  next
    case unary_exhaustion
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
        pp_exhaustion_axioms_def
      by blast
  next
    case functionality
    then have "A \<in> pp_modalized_functionality_schema"
      using fresh_modalized_functionality_schema_eq by simp
    then show ?thesis
      unfolding pp_fresh_sparse_PP_axioms_def
        pp_fresh_sparse_background_axioms_def
      by blast
  qed
qed

theorem fresh_goodman_fragment_without_logical_purity_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and no_purity: "U \<inter> pp_purity_schema = {}"
  shows "CEV_axiom_consistent [] U"
proof -
  have "U \<subseteq> fresh_goodman_axioms - pp_purity_schema"
    using subset no_purity by blast
  then have "U \<subseteq> pp_fresh_sparse_PP_axioms"
    using fresh_goodman_without_logical_purity_subset_sparse
    by blast
  then show ?thesis
    by (rule pp_fresh_sparse_fragment_consistent)
qed

corollary fresh_goodman_finite_fragment_without_logical_purity_consistent:
  assumes "finite U"
    and "U \<subseteq> fresh_goodman_axioms"
    and "U \<inter> pp_purity_schema = {}"
  shows "CEV_axiom_consistent [] U"
  using assms(2,3)
  by (rule fresh_goodman_fragment_without_logical_purity_consistent)

section \<open>Adding purity of the proposition identity operator\<close>

lemma fresh_prop_id_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> prop_id : Prop \<rightarrow>\<^sub>o Prop"
    by (rule typed_prop_id)
  show "consts_of prop_id = {}"
    by (simp add: prop_id_def)
  show "pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id =
      pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id"
    by simp
qed

lemma pp_fresh_sparse_PP_axioms_subset_fresh_goodman:
  "pp_fresh_sparse_PP_axioms \<subseteq> fresh_goodman_axioms"
  unfolding pp_fresh_sparse_PP_axioms_def
    pp_fresh_sparse_background_axioms_def
    fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  using fresh_modalized_functionality_schema_eq
  by blast

lemma pp_identity_fragment_PP_axioms_subset_fresh_goodman:
  "pp_identity_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
  unfolding pp_identity_fragment_PP_axioms_def
  using pp_fresh_sparse_PP_axioms_subset_fresh_goodman
    fresh_prop_id_purity_axiom
  unfolding fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

theorem fresh_goodman_identity_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id}"
  shows "U \<subseteq> pp_identity_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_identity_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    then have
        "A = pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id"
      using A purity by blast
    then show ?thesis
      unfolding pp_identity_fragment_PP_axioms_def by simp
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_identity_fragment_PP_axioms_def by simp
  qed
qed

theorem fresh_goodman_identity_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id}"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_identity_only_subset[OF subset purity]
  by (rule pp_identity_fragment_consistent)

corollary pp_identity_fragment_is_goodman_consistent:
  "pp_identity_fragment_PP_axioms \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent [] pp_identity_fragment_PP_axioms"
  using pp_identity_fragment_PP_axioms_subset_fresh_goodman
    pp_identity_fragment_PP_axioms_consistent
  by blast

section \<open>Adding purity of propositional negation\<close>

lemma fresh_negation_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_negation_operator
    \<in> pp_purity_schema"
  using pp_negation_operator_purity_axiom
  unfolding pp_unary_ty_def .

lemma pp_identity_negation_fragment_PP_axioms_subset_fresh_goodman:
  "pp_identity_negation_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
  unfolding pp_identity_negation_fragment_PP_axioms_def
  using pp_fresh_sparse_PP_axioms_subset_fresh_goodman
    fresh_prop_id_purity_axiom
    fresh_negation_purity_axiom
  unfolding fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

theorem fresh_goodman_identity_negation_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator}"
  shows
    "U \<subseteq> pp_identity_negation_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_identity_negation_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    then have
        "A = pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_negation_operator"
      using A purity by blast
    then show ?thesis
      unfolding pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_identity_negation_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator}"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_identity_negation_only_subset[
    OF subset purity]
  by (rule pp_identity_negation_fragment_consistent)

corollary
    pp_identity_negation_fragment_is_goodman_consistent:
  "pp_identity_negation_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_identity_negation_fragment_PP_axioms"
  using
    pp_identity_negation_fragment_PP_axioms_subset_fresh_goodman
    pp_identity_negation_fragment_PP_axioms_consistent
  by blast

section \<open>Adding the constant-truth and constant-falsity operators\<close>

lemma fresh_constant_ObjTrue_purity_axiom:
  "pp_pure pp_unary_ty (pp_constant_operator ObjTrue)
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_constant_operator ObjTrue : pp_unary_ty"
    using typed_ObjTrue by (rule typed_pp_constant_operator)
  show "consts_of (pp_constant_operator ObjTrue) = {}"
    by (simp add: pp_constant_operator_def
      pp_constant_builder_def ObjTrue_def)
  show "pp_pure pp_unary_ty
      (pp_constant_operator ObjTrue) =
      pp_pure pp_unary_ty
      (pp_constant_operator ObjTrue)"
    by simp
qed

lemma fresh_constant_ObjFalse_purity_axiom:
  "pp_pure pp_unary_ty (pp_constant_operator ObjFalse)
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_constant_operator ObjFalse : pp_unary_ty"
    using typed_ObjFalse by (rule typed_pp_constant_operator)
  show "consts_of (pp_constant_operator ObjFalse) = {}"
    by (simp add: pp_constant_operator_def
      pp_constant_builder_def ObjFalse_def ObjTrue_def)
  show "pp_pure pp_unary_ty
      (pp_constant_operator ObjFalse) =
      pp_pure pp_unary_ty
      (pp_constant_operator ObjFalse)"
    by simp
qed

lemma
    pp_logical_constants_fragment_PP_axioms_subset_fresh_goodman:
  "pp_logical_constants_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
  unfolding pp_logical_constants_fragment_PP_axioms_def
  using
    pp_identity_negation_fragment_PP_axioms_subset_fresh_goodman
    fresh_constant_ObjTrue_purity_axiom
    fresh_constant_ObjFalse_purity_axiom
  unfolding fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

theorem fresh_goodman_logical_constants_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse)}"
  shows
    "U \<subseteq> pp_logical_constants_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_logical_constants_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    then have
        "A = pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_negation_operator
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue)
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjFalse)"
      using A purity by blast
    then show ?thesis
      unfolding pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_logical_constants_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse)}"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_logical_constants_only_subset[
    OF subset purity]
  by (rule pp_logical_constants_fragment_consistent)

corollary
    pp_logical_constants_fragment_is_goodman_consistent:
  "pp_logical_constants_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_logical_constants_fragment_PP_axioms"
  using
    pp_logical_constants_fragment_PP_axioms_subset_fresh_goodman
    pp_logical_constants_fragment_PP_axioms_consistent
  by blast

section \<open>Adding the constant-function builder\<close>

lemma
    pp_constant_builder_fragment_PP_axioms_subset_fresh_goodman:
  "pp_constant_builder_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
  unfolding pp_constant_builder_fragment_PP_axioms_def
  using
    pp_logical_constants_fragment_PP_axioms_subset_fresh_goodman
    pp_constant_builder_purity_axiom
  unfolding fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

theorem fresh_goodman_constant_builder_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse),
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_constant_builder}"
  shows
    "U \<subseteq> pp_constant_builder_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_constant_builder_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    then have
        "A = pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_negation_operator
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue)
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjFalse)
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_constant_builder"
      using A purity by blast
    then show ?thesis
      unfolding pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_constant_builder_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse),
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_constant_builder}"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_constant_builder_only_subset[
    OF subset purity]
  by (rule pp_constant_builder_fragment_consistent)

corollary
    pp_constant_builder_fragment_is_goodman_consistent:
  "pp_constant_builder_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_constant_builder_fragment_PP_axioms"
  using
    pp_constant_builder_fragment_PP_axioms_subset_fresh_goodman
    pp_constant_builder_fragment_PP_axioms_consistent
  by blast

section \<open>Adding conjunction\<close>

lemma pp_conjunction_fragment_PP_axioms_subset_fresh_goodman:
  "pp_conjunction_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
  unfolding pp_conjunction_fragment_PP_axioms_def
  using
    pp_constant_builder_fragment_PP_axioms_subset_fresh_goodman
    pp_conjunction_builder_purity_axiom
  unfolding fresh_goodman_axioms_def
    fresh_goodman_background_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def
    pp_background_axioms_def
  by blast

theorem fresh_goodman_conjunction_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse),
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_constant_builder,
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_conjunction_builder}"
  shows "U \<subseteq> pp_conjunction_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_conjunction_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    then have
        "A = pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o Prop)
          pp_negation_operator
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue)
        \<or>
        A = pp_pure pp_unary_ty
          (pp_constant_operator ObjFalse)
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_constant_builder
        \<or>
        A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_conjunction_builder"
      using A purity by blast
    then show ?thesis
      unfolding pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_conjunction_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq>
          {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
           pp_pure (Prop \<rightarrow>\<^sub>o Prop)
             pp_negation_operator,
           pp_pure pp_unary_ty
             (pp_constant_operator ObjTrue),
           pp_pure pp_unary_ty
             (pp_constant_operator ObjFalse),
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_constant_builder,
           pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
             pp_conjunction_builder}"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_conjunction_only_subset[
    OF subset purity]
  by (rule pp_conjunction_fragment_consistent)

corollary pp_conjunction_fragment_is_goodman_consistent:
  "pp_conjunction_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_conjunction_fragment_PP_axioms"
  using
    pp_conjunction_fragment_PP_axioms_subset_fresh_goodman
    pp_conjunction_fragment_PP_axioms_consistent
  by blast

section \<open>Adding every binary truth-function\<close>

lemma pp_binary_truth_fragment_PP_axioms_subset_fresh_goodman:
  "pp_binary_truth_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms"
proof
  fix A
  assume A: "A \<in> pp_binary_truth_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_conjunction_fragment_PP_axioms"
    | (truth_function) F where
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          (pp_truth_function_builder F)"
    unfolding pp_binary_truth_fragment_PP_axioms_def
      pp_truth_function_purity_axioms_def
    by blast
  then show "A \<in> fresh_goodman_axioms"
  proof cases
    case old
    then show ?thesis
      using pp_conjunction_fragment_PP_axioms_subset_fresh_goodman
      by blast
  next
    case truth_function
    have "A \<in> pp_purity_schema"
      unfolding truth_function
      by (rule pp_truth_function_builder_purity_axiom)
    then show ?thesis
      unfolding fresh_goodman_axioms_def
        fresh_goodman_background_axioms_def
        pp_full_QLN_background_axioms_def
        pp_recombination_background_axioms_def
        pp_background_axioms_def
      by blast
  qed
qed

definition pp_binary_truth_allowed_purity :: "oterm set" where
  "pp_binary_truth_allowed_purity =
    {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
     pp_pure (Prop \<rightarrow>\<^sub>o Prop)
       pp_negation_operator,
     pp_pure pp_unary_ty
       (pp_constant_operator ObjTrue),
     pp_pure pp_unary_ty
       (pp_constant_operator ObjFalse),
     pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
       pp_constant_builder,
     pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
       pp_conjunction_builder}
    \<union> pp_truth_function_purity_axioms"

theorem fresh_goodman_binary_truth_only_subset:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> pp_binary_truth_allowed_purity"
  shows "U \<subseteq> pp_binary_truth_fragment_PP_axioms"
proof
  fix A
  assume A: "A \<in> U"
  show "A \<in> pp_binary_truth_fragment_PP_axioms"
  proof (cases "A \<in> pp_purity_schema")
    case True
    have "A \<in> pp_binary_truth_allowed_purity"
      using A True purity by blast
    then show ?thesis
      unfolding pp_binary_truth_allowed_purity_def
        pp_binary_truth_fragment_PP_axioms_def
        pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by blast
  next
    case False
    have "A \<in> fresh_goodman_axioms - pp_purity_schema"
      using A subset False by blast
    then have "A \<in> pp_fresh_sparse_PP_axioms"
      using fresh_goodman_without_logical_purity_subset_sparse
      by blast
    then show ?thesis
      unfolding pp_binary_truth_fragment_PP_axioms_def
        pp_conjunction_fragment_PP_axioms_def
        pp_constant_builder_fragment_PP_axioms_def
        pp_logical_constants_fragment_PP_axioms_def
        pp_identity_negation_fragment_PP_axioms_def
      by simp
  qed
qed

theorem fresh_goodman_binary_truth_only_consistent:
  assumes subset: "U \<subseteq> fresh_goodman_axioms"
    and purity:
      "U \<inter> pp_purity_schema
        \<subseteq> pp_binary_truth_allowed_purity"
  shows "CEV_axiom_consistent [] U"
  using fresh_goodman_binary_truth_only_subset[
    OF subset purity]
  by (rule pp_binary_truth_fragment_consistent)

corollary pp_binary_truth_fragment_is_goodman_consistent:
  "pp_binary_truth_fragment_PP_axioms
      \<subseteq> fresh_goodman_axioms
    \<and>
    CEV_axiom_consistent []
      pp_binary_truth_fragment_PP_axioms"
  using
    pp_binary_truth_fragment_PP_axioms_subset_fresh_goodman
    pp_binary_truth_fragment_PP_axioms_consistent
  by blast

end
