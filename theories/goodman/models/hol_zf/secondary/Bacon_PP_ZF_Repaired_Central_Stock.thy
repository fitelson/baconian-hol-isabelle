theory Bacon_PP_ZF_Repaired_Central_Stock
  imports Bacon_PP_ZF_Tree_Range_Term_Basis
begin

section \<open>The repaired central stock in the tree basis model\<close>

text \<open>
  The Recombination stock used in the repaired QSS bridge adds zeroary
  Exhaustion.  For a cone-natural basis this addition costs nothing:
  every pure proposition is locally equivalent to a basis proposition,
  and every cone-natural basis proposition is globally constant.
\<close>

definition pp_t_self_applicative_pure ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_t_self_applicative_pure Pure \<longleftrightarrow>
    Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (Pure (Prop \<rightarrow>\<^sub>o Prop)))"

context pp_t_stock_basis
begin

interpretation RepairedBasisConstants:
  pp_t_constants
    "pp_t_seeded_internal_constants
      (pp_t_basis_stock D) pp_t_basis_seed_at"
  by standard
    (rule BasisSeeded.pp_t_seeded_internal_constants_typed)

lemma pp_t_basis_pure_prop_truth_implies_necessary:
  assumes pure: "pp_t_basis_stock D Prop w P"
    and true_now: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  obtain d where P: "Elem P (pp_t_domain Prop)"
    and d: "d \<in> D Prop"
    and Pd: "pp_t_eqv Prop w P d"
    using pure unfolding pp_t_basis_stock_def by blast
  have d_typed: "Elem d (pp_t_domain Prop)"
    using basis_typed[OF d] .
  have d_invariant: "\<And>s. pp_t_cone_rel Prop s d d"
    using basis_cone_natural[OF d] .
  have d_collapse:
      "d = pp_zf_truth (pp_t_holds d [])"
    using pp_t_cone_invariant_prop_collapse[
      OF d_typed d_invariant] .
  have transfer:
      "pp_t_holds P w \<longleftrightarrow> pp_t_holds d w"
    using pp_t_prop_eqv_at[OF Pd, of w] by simp
  have d_true_now: "pp_t_holds d w"
    using true_now transfer by blast
  have d_world_iff_root:
      "pp_t_holds d w \<longleftrightarrow> pp_t_holds d []"
    using d_collapse by (cases "pp_t_holds d []") simp_all
  have d_true_root: "pp_t_holds d []"
    using d_true_now d_world_iff_root by blast
  have d_truth: "d = pp_zf_truth True"
    using d_collapse d_true_root by simp
  show ?thesis
    using Pd d_truth by simp
qed

lemma pp_t_basis_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval
      (pp_t_seeded_internal_constants
        (pp_t_basis_stock D) pp_t_basis_seed_at)
      \<rho> pp_zeroary_exhaustion) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_exhaustion_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_t_domain Prop)"
    have extended:
        "pp_t_env_typed [Prop] (extend_env P \<rho>)"
      using pp_t_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_t_holds
          (pp_t_eval
            (pp_t_seeded_internal_constants
              (pp_t_basis_stock D) pp_t_basis_seed_at)
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_basis_stock D Prop w P"
      using BasisSeeded.pp_t_seeded_eval_pure_holds[
        OF var_type extended, of w] by simp
    have exhaustion:
        "pp_t_basis_stock D Prop w P \<Longrightarrow>
          pp_t_holds P w \<Longrightarrow>
          pp_t_eqv Prop w P (pp_zf_truth True)"
      by (rule pp_t_basis_pure_prop_truth_implies_necessary)
    show "pp_t_holds
        (pp_t_eval
          (pp_t_seeded_internal_constants
            (pp_t_basis_stock D) pp_t_basis_seed_at)
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff exhaustion
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_basis_zeroary_exhaustion_gvalid:
  "RepairedBasisConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    RepairedBasisConstants.TreeHenkin.gvalid_def
    RepairedBasisConstants.pp_t_den_def
  using pp_t_basis_zeroary_exhaustion_holds by blast

theorem pp_t_basis_repaired_central_gvalid_iff:
  "RepairedBasisConstants.TreeHenkin.gvalid_set
      pp_recombination_zeroary_exhaustion_axioms
    \<longleftrightarrow>
    pp_t_self_applicative_pure (pp_t_basis_stock D)"
proof
  assume repaired:
      "RepairedBasisConstants.TreeHenkin.gvalid_set
        pp_recombination_zeroary_exhaustion_axioms"
  have original:
      "RepairedBasisConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
    using repaired
    unfolding
      RepairedBasisConstants.TreeHenkin.gvalid_set_def
      pp_recombination_zeroary_exhaustion_axioms_def
    by blast
  show "pp_t_self_applicative_pure (pp_t_basis_stock D)"
    using original
      pp_t_basis_recombination_PP_gvalid_iff_root
    unfolding pp_t_self_applicative_pure_def by blast
next
  assume self:
      "pp_t_self_applicative_pure (pp_t_basis_stock D)"
  have original:
      "RepairedBasisConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
    using self
      pp_t_basis_recombination_PP_gvalid_iff_root
    unfolding pp_t_self_applicative_pure_def by blast
  show "RepairedBasisConstants.TreeHenkin.gvalid_set
      pp_recombination_zeroary_exhaustion_axioms"
    unfolding
      RepairedBasisConstants.TreeHenkin.gvalid_set_def
      pp_recombination_zeroary_exhaustion_axioms_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume A:
        "A \<in> insert pp_zeroary_exhaustion
          pp_recombination_PP_axioms"
    then consider
      (exhaustion) "A = pp_zeroary_exhaustion"
    | (original) "A \<in> pp_recombination_PP_axioms"
      by blast
    then show
        "RepairedBasisConstants.TreeHenkin.gvalid \<Gamma> A"
    proof cases
      case exhaustion
      show ?thesis
        unfolding exhaustion
        by (rule pp_t_basis_zeroary_exhaustion_gvalid)
    next
      case original_case: original
      show ?thesis
        using original original_case
        unfolding
          RepairedBasisConstants.TreeHenkin.gvalid_set_def
        by blast
    qed
  qed
qed

end

section \<open>The absorption fixed point now discharges the repaired stock\<close>

context pp_t_cone_natural_enumerator
begin

interpretation RepairedTermConstants:
  pp_t_constants
    "pp_t_seeded_internal_constants
      (pp_t_basis_stock (pp_t_enumerator_basis E))
      TermBasis.pp_t_basis_seed_at"
  by standard
    (rule TermBasis.BasisSeeded.pp_t_seeded_internal_constants_typed)

theorem pp_t_term_basis_repaired_central_gvalid_from_fixed_point:
  assumes fixed_point:
      "pp_t_enumerator_basis E pp_t_unary_type =
        (\<lambda>n. E \<acute> n) `
          {n. Elem n (pp_t_domain Ind)}"
  shows "RepairedTermConstants.TreeHenkin.gvalid_set
    pp_recombination_zeroary_exhaustion_axioms"
proof -
  have self:
      "pp_t_self_applicative_pure
        (pp_t_basis_stock (pp_t_enumerator_basis E))"
    unfolding pp_t_self_applicative_pure_def
      pp_unary_ty_def
    using pp_t_term_basis_self_classifies_from_fixed_point[
      OF fixed_point] .
  show ?thesis
    using
      TermBasis.pp_t_basis_repaired_central_gvalid_iff
      self by blast
qed

end

section \<open>The exact T6 escape forced by a completed repaired model\<close>

theorem (in henkin_action_model)
  repaired_central_stock_answers_Goodman:
  assumes base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma> B"
    and zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
    and repaired:
      "gvalid_set pp_recombination_zeroary_exhaustion_axioms"
  shows "pp_recombination_axiom_consistency_question"
proof -
  have original: "gvalid_set pp_recombination_PP_axioms"
    using repaired
    unfolding gvalid_set_def
      pp_recombination_zeroary_exhaustion_axioms_def
    by blast
  show ?thesis
    using base_sound zeta_sound original
    by (rule pp_recombination_question_of_gvalid)
qed

theorem (in henkin_action_model)
  repaired_central_stock_forces_L2_or_TU_failure:
  assumes base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma> B"
    and zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
    and repaired:
      "gvalid_set pp_recombination_zeroary_exhaustion_axioms"
  shows "\<not> gvalid_set {pp_L2, pp_TU}"
proof
  assume pair: "gvalid_set {pp_L2, pp_TU}"
  have full: "gvalid_set pp_repaired_T6_TU_axioms"
    unfolding gvalid_set_def pp_repaired_T6_TU_axioms_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume
        "A \<in> insert pp_TU
          (insert pp_L2
            pp_recombination_zeroary_exhaustion_axioms)"
    then show "gvalid \<Gamma> A"
      using repaired pair
      unfolding gvalid_set_def by blast
  qed
  have not_full: "\<not> gvalid_set pp_repaired_T6_TU_axioms"
    using base_sound zeta_sound
      CEV_Goodman_T6_TU_repaired_central_stock
    by (rule derivable_false_excludes_gvalid_set)
  show False
    using full not_full by blast
qed

corollary (in henkin_action_model)
  repaired_central_stock_has_explicit_L2_or_TU_failure:
  assumes base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma> B"
    and zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
    and repaired:
      "gvalid_set pp_recombination_zeroary_exhaustion_axioms"
  shows "\<exists>\<Gamma>. \<not> gvalid \<Gamma> pp_L2 \<or> \<not> gvalid \<Gamma> pp_TU"
proof -
  have "\<not> gvalid_set {pp_L2, pp_TU}"
    using base_sound zeta_sound repaired
    by (rule repaired_central_stock_forces_L2_or_TU_failure)
  then show ?thesis
    unfolding gvalid_set_def by blast
qed

context pp_t_cone_natural_enumerator
begin

interpretation RepairedTermConstants:
  pp_t_constants
    "pp_t_seeded_internal_constants
      (pp_t_basis_stock (pp_t_enumerator_basis E))
      TermBasis.pp_t_basis_seed_at"
  by standard
    (rule TermBasis.BasisSeeded.pp_t_seeded_internal_constants_typed)

theorem pp_t_term_basis_fixed_point_forces_L2_or_TU_failure:
  assumes fixed_point:
      "pp_t_enumerator_basis E pp_t_unary_type =
        (\<lambda>n. E \<acute> n) `
          {n. Elem n (pp_t_domain Ind)}"
    and base_sound:
      "\<And>\<Gamma> B. \<Gamma> \<turnstile>\<^sub>CEV B \<Longrightarrow>
        RepairedTermConstants.TreeHenkin.gvalid \<Gamma> B"
    and zeta_sound:
      "\<And>\<Gamma> \<sigma>s F G.
        \<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        RepairedTermConstants.TreeHenkin.gvalid
          (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G) \<Longrightarrow>
        RepairedTermConstants.TreeHenkin.gvalid \<Gamma>
          (Eq (arrow_type \<sigma>s Prop) F G)"
  shows "\<exists>\<Gamma>.
    \<not> RepairedTermConstants.TreeHenkin.gvalid \<Gamma> pp_L2
    \<or>
    \<not> RepairedTermConstants.TreeHenkin.gvalid \<Gamma> pp_TU"
proof -
  have repaired:
      "RepairedTermConstants.TreeHenkin.gvalid_set
        pp_recombination_zeroary_exhaustion_axioms"
    using fixed_point
    by (rule
      pp_t_term_basis_repaired_central_gvalid_from_fixed_point)
  show ?thesis
    using base_sound zeta_sound repaired
    by (rule RepairedTermConstants.TreeHenkin.repaired_central_stock_has_explicit_L2_or_TU_failure)
qed

end

end
