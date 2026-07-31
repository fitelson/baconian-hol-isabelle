theory Bacon_PP_Finite_Fragment_Model_Program
  imports
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Axiom_Soundness"
    "Goodman_CEVplus_Canonical.Bacon_PP_Finite_Application_Graph"
begin

section \<open>Countable self-classifying models for finite fragments\<close>

subsection \<open>The finite data carried by a fragment\<close>

definition pp_recombination_fixed_axioms :: "oterm set" where
  "pp_recombination_fixed_axioms =
    {pp_target_PP, pp_unique_fundamental Prop,
      pp_zeroary_recombination, pp_unary_recombination}"

definition pp_purity_generator_of :: "oterm \<Rightarrow> otype \<times> oterm" where
  "pp_purity_generator_of A =
    (SOME p.
      [] \<turnstile> snd p : fst p
      \<and> pp_logical_vocabulary (snd p)
      \<and> A = pp_pure (fst p) (snd p))"

definition pp_application_pair_of :: "oterm \<Rightarrow> otype \<times> otype" where
  "pp_application_pair_of A =
    (SOME p. A = pp_application_closure (fst p) (snd p))"

definition pp_nonfundamental_type_of :: "oterm \<Rightarrow> otype" where
  "pp_nonfundamental_type_of A =
    (SOME \<sigma>. \<sigma> \<noteq> Prop \<and> A = pp_no_fundamentals \<sigma>)"

definition pp_fragment_logical_generators ::
    "oterm set \<Rightarrow> (otype \<times> oterm) set" where
  "pp_fragment_logical_generators U =
    pp_purity_generator_of ` (U \<inter> pp_purity_schema)"

definition pp_fragment_application_pairs ::
    "oterm set \<Rightarrow> (otype \<times> otype) set" where
  "pp_fragment_application_pairs U =
    pp_application_pair_of ` (U \<inter> pp_application_closure_schema)"

definition pp_fragment_nonfundamental_types ::
    "oterm set \<Rightarrow> otype set" where
  "pp_fragment_nonfundamental_types U =
    pp_nonfundamental_type_of `
      (U \<inter> pp_no_other_fundamentals_schema)"

lemma pp_purity_generator_of_correct:
  assumes "A \<in> pp_purity_schema"
  shows "[] \<turnstile> snd (pp_purity_generator_of A) :
      fst (pp_purity_generator_of A)"
    and "pp_logical_vocabulary (snd (pp_purity_generator_of A))"
    and "A = pp_pure
      (fst (pp_purity_generator_of A))
      (snd (pp_purity_generator_of A))"
proof -
  have "\<exists>p.
      [] \<turnstile> snd p : fst p
      \<and> pp_logical_vocabulary (snd p)
      \<and> A = pp_pure (fst p) (snd p)"
    using assms unfolding pp_purity_schema_def by force
  then show
      "[] \<turnstile> snd (pp_purity_generator_of A) :
        fst (pp_purity_generator_of A)"
      "pp_logical_vocabulary (snd (pp_purity_generator_of A))"
      "A = pp_pure
        (fst (pp_purity_generator_of A))
        (snd (pp_purity_generator_of A))"
    unfolding pp_purity_generator_of_def
    by (metis (mono_tags, lifting) someI_ex)+
qed

lemma pp_application_pair_of_correct:
  assumes "A \<in> pp_application_closure_schema"
  shows "A = pp_application_closure
    (fst (pp_application_pair_of A))
    (snd (pp_application_pair_of A))"
proof -
  have "\<exists>p.
      A = pp_application_closure (fst p) (snd p)"
    using assms unfolding pp_application_closure_schema_def by force
  then show ?thesis
    unfolding pp_application_pair_of_def
    by (metis (mono_tags, lifting) someI_ex)
qed

lemma pp_nonfundamental_type_of_correct:
  assumes "A \<in> pp_no_other_fundamentals_schema"
  shows "pp_nonfundamental_type_of A \<noteq> Prop"
    and "A = pp_no_fundamentals (pp_nonfundamental_type_of A)"
proof -
  have "\<exists>\<sigma>.
      \<sigma> \<noteq> Prop \<and> A = pp_no_fundamentals \<sigma>"
    using assms unfolding pp_no_other_fundamentals_schema_def by blast
  then show
      "pp_nonfundamental_type_of A \<noteq> Prop"
      "A = pp_no_fundamentals (pp_nonfundamental_type_of A)"
    unfolding pp_nonfundamental_type_of_def
    by (metis (mono_tags, lifting) someI_ex)+
qed

lemma pp_fragment_logical_generators_finite:
  assumes "finite U"
  shows "finite (pp_fragment_logical_generators U)"
  using assms
  unfolding pp_fragment_logical_generators_def by simp

lemma pp_fragment_application_pairs_finite:
  assumes "finite U"
  shows "finite (pp_fragment_application_pairs U)"
  using assms
  unfolding pp_fragment_application_pairs_def by simp

lemma pp_fragment_nonfundamental_types_finite:
  assumes "finite U"
  shows "finite (pp_fragment_nonfundamental_types U)"
  using assms
  unfolding pp_fragment_nonfundamental_types_def by simp

lemma pp_fragment_purity_part:
  "{pp_pure (fst p) (snd p) |p.
      p \<in> pp_fragment_logical_generators U}
    = U \<inter> pp_purity_schema"
proof
  show "{pp_pure (fst p) (snd p) |p.
      p \<in> pp_fragment_logical_generators U}
      \<subseteq> U \<inter> pp_purity_schema"
  proof
    fix A
    assume "A \<in> {pp_pure (fst p) (snd p) |p.
        p \<in> pp_fragment_logical_generators U}"
    then obtain p B where
        p: "p = pp_purity_generator_of B"
      and B: "B \<in> U \<inter> pp_purity_schema"
      and A: "A = pp_pure (fst p) (snd p)"
      unfolding pp_fragment_logical_generators_def by blast
    have "B = pp_pure (fst p) (snd p)"
      using pp_purity_generator_of_correct(3)[of B] p B by simp
    then show "A \<in> U \<inter> pp_purity_schema"
      using A B by simp
  qed
  show "U \<inter> pp_purity_schema
      \<subseteq> {pp_pure (fst p) (snd p) |p.
        p \<in> pp_fragment_logical_generators U}"
  proof
    fix A
    assume A: "A \<in> U \<inter> pp_purity_schema"
    let ?p = "pp_purity_generator_of A"
    have "?p \<in> pp_fragment_logical_generators U"
      using A unfolding pp_fragment_logical_generators_def by blast
    moreover have "A = pp_pure (fst ?p) (snd ?p)"
      using pp_purity_generator_of_correct(3) A by blast
    ultimately show "A \<in> {pp_pure (fst p) (snd p) |p.
        p \<in> pp_fragment_logical_generators U}"
      by blast
  qed
qed

lemma pp_fragment_application_part:
  "{pp_application_closure (fst p) (snd p) |p.
      p \<in> pp_fragment_application_pairs U}
    = U \<inter> pp_application_closure_schema"
proof
  show "{pp_application_closure (fst p) (snd p) |p.
      p \<in> pp_fragment_application_pairs U}
      \<subseteq> U \<inter> pp_application_closure_schema"
  proof
    fix A
    assume "A \<in> {pp_application_closure (fst p) (snd p) |p.
        p \<in> pp_fragment_application_pairs U}"
    then obtain p B where
        p: "p = pp_application_pair_of B"
      and B: "B \<in> U \<inter> pp_application_closure_schema"
      and A: "A = pp_application_closure (fst p) (snd p)"
      unfolding pp_fragment_application_pairs_def by blast
    have "B = pp_application_closure (fst p) (snd p)"
      using pp_application_pair_of_correct[of B] p B by simp
    then show "A \<in> U \<inter> pp_application_closure_schema"
      using A B by simp
  qed
  show "U \<inter> pp_application_closure_schema
      \<subseteq> {pp_application_closure (fst p) (snd p) |p.
        p \<in> pp_fragment_application_pairs U}"
  proof
    fix A
    assume A: "A \<in> U \<inter> pp_application_closure_schema"
    let ?p = "pp_application_pair_of A"
    have "?p \<in> pp_fragment_application_pairs U"
      using A unfolding pp_fragment_application_pairs_def by blast
    moreover have "A = pp_application_closure (fst ?p) (snd ?p)"
      using pp_application_pair_of_correct A by blast
    ultimately show "A \<in>
        {pp_application_closure (fst p) (snd p) |p.
          p \<in> pp_fragment_application_pairs U}"
      by blast
  qed
qed

lemma pp_fragment_nonfundamental_part:
  "{pp_no_fundamentals \<sigma> |\<sigma>.
      \<sigma> \<in> pp_fragment_nonfundamental_types U}
    = U \<inter> pp_no_other_fundamentals_schema"
proof
  show "{pp_no_fundamentals \<sigma> |\<sigma>.
      \<sigma> \<in> pp_fragment_nonfundamental_types U}
      \<subseteq> U \<inter> pp_no_other_fundamentals_schema"
  proof
    fix A
    assume "A \<in> {pp_no_fundamentals \<sigma> |\<sigma>.
        \<sigma> \<in> pp_fragment_nonfundamental_types U}"
    then obtain \<sigma> B where
        \<sigma>: "\<sigma> = pp_nonfundamental_type_of B"
      and B: "B \<in> U \<inter> pp_no_other_fundamentals_schema"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_fragment_nonfundamental_types_def by blast
    have "B = pp_no_fundamentals \<sigma>"
      using pp_nonfundamental_type_of_correct(2)[of B] \<sigma> B by simp
    then show "A \<in> U \<inter> pp_no_other_fundamentals_schema"
      using A B by simp
  qed
  show "U \<inter> pp_no_other_fundamentals_schema
      \<subseteq> {pp_no_fundamentals \<sigma> |\<sigma>.
        \<sigma> \<in> pp_fragment_nonfundamental_types U}"
  proof
    fix A
    assume A: "A \<in> U \<inter> pp_no_other_fundamentals_schema"
    let ?\<sigma> = "pp_nonfundamental_type_of A"
    have "?\<sigma> \<in> pp_fragment_nonfundamental_types U"
      using A unfolding pp_fragment_nonfundamental_types_def by blast
    moreover have "A = pp_no_fundamentals ?\<sigma>"
      using pp_nonfundamental_type_of_correct(2) A by blast
    ultimately show "A \<in> {pp_no_fundamentals \<sigma> |\<sigma>.
        \<sigma> \<in> pp_fragment_nonfundamental_types U}"
      by blast
  qed
qed

theorem pp_finite_fragment_exact_data:
  assumes U_sub: "U \<subseteq> pp_recombination_PP_axioms"
  shows "U =
    (U \<inter> pp_recombination_fixed_axioms)
    \<union> {pp_pure (fst p) (snd p) |p.
      p \<in> pp_fragment_logical_generators U}
    \<union> {pp_application_closure (fst p) (snd p) |p.
      p \<in> pp_fragment_application_pairs U}
    \<union> {pp_no_fundamentals \<sigma> |\<sigma>.
      \<sigma> \<in> pp_fragment_nonfundamental_types U}"
proof -
  have stock:
      "pp_recombination_PP_axioms =
        pp_recombination_fixed_axioms
        \<union> pp_purity_schema
        \<union> pp_application_closure_schema
        \<union> pp_no_other_fundamentals_schema"
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
      pp_recombination_fixed_axioms_def
    by blast
  have "U =
      (U \<inter> pp_recombination_fixed_axioms)
      \<union> (U \<inter> pp_purity_schema)
      \<union> (U \<inter> pp_application_closure_schema)
      \<union> (U \<inter> pp_no_other_fundamentals_schema)"
    using U_sub stock by blast
  then show ?thesis
    using pp_fragment_purity_part
      pp_fragment_application_part
      pp_fragment_nonfundamental_part
    by simp
qed

corollary pp_finite_fragment_data_are_finite:
  assumes "finite U"
  shows "finite (pp_fragment_logical_generators U)"
    and "finite (pp_fragment_application_pairs U)"
    and "finite (pp_fragment_nonfundamental_types U)"
  using assms
    pp_fragment_logical_generators_finite
    pp_fragment_application_pairs_finite
    pp_fragment_nonfundamental_types_finite
  by blast+

definition pp_fragment_classifier_acyclic :: "oterm set \<Rightarrow> bool" where
  "pp_fragment_classifier_acyclic U \<longleftrightarrow>
    pp_finite_classifier_acyclic
      (pp_fragment_application_pairs U)"

theorem pp_acyclic_finite_fragment_unary_values_stabilize:
  assumes "pp_fragment_classifier_acyclic U"
  shows "pp_finite_generated_unary_values
      logical classifier app
      (pp_fragment_logical_generators U)
      (pp_fragment_application_pairs U)
    =
    pp_finite_classifier_free_unary_values
      logical classifier app
      (pp_fragment_logical_generators U)
      (pp_fragment_application_pairs U)"
  using assms
  unfolding pp_fragment_classifier_acyclic_def
  by (rule pp_finite_acyclic_generated_unary_values_stabilize)

corollary pp_acyclic_finite_fragment_unary_values_independent_of_classifier:
  assumes "pp_fragment_classifier_acyclic U"
  shows "pp_finite_generated_unary_values
      logical classifier\<^sub>1 app
      (pp_fragment_logical_generators U)
      (pp_fragment_application_pairs U)
    =
    pp_finite_generated_unary_values
      logical classifier\<^sub>2 app
      (pp_fragment_logical_generators U)
      (pp_fragment_application_pairs U)"
  using assms
  unfolding pp_fragment_classifier_acyclic_def
  by (rule pp_finite_acyclic_unary_values_independent_of_classifier)

subsection \<open>The first classifier-bearing cyclic package\<close>

definition pp_finite_first_cyclic_package :: "oterm set" where
  "pp_finite_first_cyclic_package =
    pp_recombination_fixed_axioms
    \<union> {
      pp_pure
        (pp_finite_classifier_type
          \<rightarrow>\<^sub>o pp_finite_unary_type)
        pp_finite_singleton_probe_builder,
      pp_application_closure
        pp_finite_classifier_type
        pp_finite_unary_type}"

lemma pp_finite_first_cyclic_package_finite:
  "finite pp_finite_first_cyclic_package"
  unfolding pp_finite_first_cyclic_package_def
    pp_recombination_fixed_axioms_def
  by simp

lemma pp_finite_first_cyclic_package_subset:
  "pp_finite_first_cyclic_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have purity:
      "pp_pure
        (pp_finite_classifier_type
          \<rightarrow>\<^sub>o pp_finite_unary_type)
        pp_finite_singleton_probe_builder
      \<in> pp_purity_schema"
    using pp_finite_singleton_probe_builder_typed
      pp_finite_singleton_probe_builder_logical
    unfolding pp_purity_schema_def by blast
  have application:
      "pp_application_closure
        pp_finite_classifier_type
        pp_finite_unary_type
      \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  show ?thesis
    using purity application
    unfolding pp_finite_first_cyclic_package_def
      pp_recombination_fixed_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

lemma pp_application_closure_pair_injective:
  assumes "pp_application_closure \<sigma> \<tau> =
    pp_application_closure \<sigma>' \<tau>'"
  shows "\<sigma> = \<sigma>' \<and> \<tau> = \<tau>'"
  using assms
  unfolding pp_application_closure_def
    pp_pure_def pp_Pure_def
  by simp

lemma pp_finite_first_cyclic_pair_extracted:
  "(pp_finite_classifier_type, pp_finite_unary_type)
    \<in> pp_fragment_application_pairs
      pp_finite_first_cyclic_package"
proof -
  let ?A =
      "pp_application_closure
        pp_finite_classifier_type
        pp_finite_unary_type"
  have A_package: "?A \<in> pp_finite_first_cyclic_package"
    unfolding pp_finite_first_cyclic_package_def by simp
  have A_schema: "?A \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  let ?p = "pp_application_pair_of ?A"
  have p_in:
      "?p \<in> pp_fragment_application_pairs
        pp_finite_first_cyclic_package"
    using A_package A_schema
    unfolding pp_fragment_application_pairs_def by blast
  have equation:
      "?A = pp_application_closure (fst ?p) (snd ?p)"
    using pp_application_pair_of_correct[OF A_schema] .
  have pair:
      "?p =
        (pp_finite_classifier_type, pp_finite_unary_type)"
    using pp_application_closure_pair_injective[OF equation]
    by (cases ?p) simp
  show ?thesis
    using p_in unfolding pair .
qed

theorem pp_finite_first_package_has_classifier_cycle:
  "\<not> pp_fragment_classifier_acyclic
    pp_finite_first_cyclic_package"
proof -
  have pair:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> pp_fragment_application_pairs
          pp_finite_first_cyclic_package"
    by (rule pp_finite_first_cyclic_pair_extracted)
  have edge:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> pp_finite_application_dependency
          (pp_fragment_application_pairs
            pp_finite_first_cyclic_package)"
    using pair by (rule pp_finite_application_dependency_argument)
  have path:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> (pp_finite_application_dependency
          (pp_fragment_application_pairs
            pp_finite_first_cyclic_package))\<^sup>*"
    using edge by (rule r_into_rtrancl)
  show ?thesis
    using path
    unfolding pp_fragment_classifier_acyclic_def
      pp_finite_classifier_acyclic_def
    by blast
qed

text \<open>
  This package is finite and belongs to the exact Recombination-only stock.
  PP supplies a pure classifier; the displayed logical builder is pure; and
  application closure at the pair
  \<open>(pp_finite_classifier_type, pp_finite_unary_type)\<close> therefore forces
  the singleton-family classifier test into the unary pure stock.  The
  application pair is the subset-minimal type-level classifier cycle proved
  above.  Its semantic value is the next construction target.
\<close>

subsection \<open>The semantic model interface\<close>

text \<open>
  This locale states the exact semantic obligation in the finite-fragment
  program.  The model may depend on the finite fragment \<open>U\<close>, but all models
  use common carrier and world types.  That is no loss for the intended
  HOL-ZF construction, whose universal carrier and tree of worlds are fixed.

  We require the model assigned to \<open>U\<close> to validate
  \<open>insert pp_target_PP U\<close>, rather than merely \<open>U\<close>.  Thus every tailored
  model is self-classifying even when the particular fragment supplied by
  compactness omits PP.  Since PP is itself a member of Goodman's full stock,
  adjoining it preserves finiteness and remains within that stock.

  Countability is recorded explicitly.  It is a construction constraint, not
  an assumption used by the soundness or compactness arguments.
\<close>

locale pp_recombination_finite_fragment_models =
  fixes dom ::
      "oterm set \<Rightarrow> otype \<Rightarrow> 'u \<Rightarrow> bool"
    and holds ::
      "oterm set \<Rightarrow> 'u \<Rightarrow> 'w \<Rightarrow> bool"
    and den ::
      "oterm set \<Rightarrow> oterm \<Rightarrow> 'u list \<Rightarrow> 'u"
  assumes action_model:
      "\<lbrakk>finite U; U \<subseteq> pp_recombination_PP_axioms\<rbrakk>
        \<Longrightarrow> henkin_action_model (dom U) (holds U) (den U)"
    and base_sound:
      "\<lbrakk>finite U; U \<subseteq> pp_recombination_PP_axioms;
        \<Gamma> \<turnstile>\<^sub>CEV A\<rbrakk>
        \<Longrightarrow>
          henkin_action_model.gvalid
            (dom U) (holds U) (den U) \<Gamma> A"
    and zeta_sound:
      "\<lbrakk>finite U; U \<subseteq> pp_recombination_PP_axioms;
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop;
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop;
        henkin_action_model.gvalid
          (dom U) (holds U) (den U)
          (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G)\<rbrakk>
        \<Longrightarrow>
          henkin_action_model.gvalid
            (dom U) (holds U) (den U) \<Gamma>
            (Eq (arrow_type \<sigma>s Prop) F G)"
    and self_classifying_fragment_valid:
      "\<lbrakk>finite U; U \<subseteq> pp_recombination_PP_axioms\<rbrakk>
        \<Longrightarrow>
          henkin_action_model.gvalid_set
            (dom U) (holds U) (den U)
            (insert pp_target_PP U)"
    and countable_domains:
      "\<lbrakk>finite U; U \<subseteq> pp_recombination_PP_axioms\<rbrakk>
        \<Longrightarrow> countable {x. dom U \<sigma> x}"
    and countable_worlds: "countable (UNIV :: 'w set)"
begin

theorem self_classifying_finite_fragment_consistent:
  assumes finite_U: "finite U"
    and U_sub: "U \<subseteq> pp_recombination_PP_axioms"
  shows "CEV_axiom_consistent [] (insert pp_target_PP U)"
proof -
  interpret Model: henkin_action_model
      "dom U" "holds U" "den U"
    using action_model[OF finite_U U_sub] .
  have base:
      "\<And>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>CEV A
        \<Longrightarrow> Model.gvalid \<Gamma> A"
    using base_sound[OF finite_U U_sub] .
  have zeta:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop
        \<Longrightarrow> \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop
        \<Longrightarrow>
          Model.gvalid (\<sigma>s @ \<Gamma>)
            (zeta_body \<sigma>s F G)
        \<Longrightarrow>
          Model.gvalid \<Gamma>
            (Eq (arrow_type \<sigma>s Prop) F G)"
    using zeta_sound[OF finite_U U_sub] .
  have valid:
      "Model.gvalid_set (insert pp_target_PP U)"
    using self_classifying_fragment_valid[OF finite_U U_sub] .
  show ?thesis
    using base zeta valid
    by (rule Model.CEV_axiom_consistent_of_gvalid)
qed

corollary finite_fragment_consistent:
  assumes finite_U: "finite U"
    and U_sub: "U \<subseteq> pp_recombination_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  interpret Model: henkin_action_model
      "dom U" "holds U" "den U"
    using action_model[OF finite_U U_sub] .
  have base:
      "\<And>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>CEV A
        \<Longrightarrow> Model.gvalid \<Gamma> A"
    using base_sound[OF finite_U U_sub] .
  have zeta:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop
        \<Longrightarrow> \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop
        \<Longrightarrow>
          Model.gvalid (\<sigma>s @ \<Gamma>)
            (zeta_body \<sigma>s F G)
        \<Longrightarrow>
          Model.gvalid \<Gamma>
            (Eq (arrow_type \<sigma>s Prop) F G)"
    using zeta_sound[OF finite_U U_sub] .
  have valid_enlarged:
      "Model.gvalid_set (insert pp_target_PP U)"
    using self_classifying_fragment_valid[OF finite_U U_sub] .
  have valid_U: "Model.gvalid_set U"
    using valid_enlarged
    unfolding Model.gvalid_set_def by blast
  show ?thesis
    using base zeta valid_U
    by (rule Model.CEV_axiom_consistent_of_gvalid)
qed

theorem finite_fragment_models_answer_Goodman:
  "pp_recombination_axiom_consistency_question"
  by (rule pp_recombination_all_finite_fragments_answer_affirmatively)
    (rule finite_fragment_consistent)

end

text \<open>
  The preceding theorem completes the proof-theoretic and semantic reduction.
  It does not assert that the locale has been instantiated.  The remaining
  mathematical task is constructive: for each finite fragment, define its
  countable domains, worlds, denotation function, and interpretations of
  \<open>Pure\<close> and \<open>Fun\<close>, and then discharge the locale assumptions.  A failure
  of one proposed interpretation is not an inconsistent core; only an
  axiom-extension derivation of \<open>ObjFalse\<close> has that force.
\<close>

end
