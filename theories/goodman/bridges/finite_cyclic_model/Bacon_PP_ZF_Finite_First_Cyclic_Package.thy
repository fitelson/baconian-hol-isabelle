theory Bacon_PP_ZF_Finite_First_Cyclic_Package
  imports
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Singleton_Family_Elimination"
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Symmetrized_Singleton"
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Complemented_Symmetrized_Singleton"
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Family_Probe_Absorption"
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers"
    "Goodman_CEVplus_Finite_Fragment_Model_Program.Bacon_PP_Finite_Fragment_Model_Program"
begin

section \<open>A model for the first classifier-bearing cyclic package\<close>

text \<open>
  The acyclic theorem stops precisely when an application pair can carry a
  value depending on the classifier of the unary pure stock back into that
  stock.  The first such package contains one closed logical builder of type
  \<open>((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
    \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)\<close>
  and application closure at the corresponding pair.

  We interpret the unary pure stock as Bacon's exact closed logical stock.
  At the classifier type we take the equivalence class of its classifier; at
  the builder type we take the equivalence class of the displayed builder.
  The only cyclic application then denotes the singleton-family test.  The
  previously verified elimination theorem identifies that test with the
  closed logical settled-now operator, closing the cycle in one step.
\<close>

abbreviation pp_t_first_cyclic_unary_type :: otype where
  "pp_t_first_cyclic_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_first_cyclic_classifier_type :: otype where
  "pp_t_first_cyclic_classifier_type \<equiv>
    pp_t_first_cyclic_unary_type \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_first_cyclic_builder_type :: otype where
  "pp_t_first_cyclic_builder_type \<equiv>
    pp_t_first_cyclic_classifier_type
      \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type"

definition pp_t_first_cyclic_builder_den :: ZF where
  "pp_t_first_cyclic_builder_den =
    pp_t_closed_den pp_finite_singleton_probe_builder"

lemma pp_finite_singleton_probe_builder_eq_one_step:
  "pp_finite_singleton_probe_builder =
    pp_t_one_step_singleton_test_builder"
  unfolding pp_finite_singleton_probe_builder_def
    pp_t_one_step_singleton_test_builder_def
  by simp

lemma pp_t_first_cyclic_builder_den_in_domain:
  "Elem pp_t_first_cyclic_builder_den
    (pp_t_domain pp_t_first_cyclic_builder_type)"
  unfolding pp_t_first_cyclic_builder_den_def
  using pp_t_closed_den_in_domain[
    OF pp_finite_singleton_probe_builder_typed] .

definition pp_t_first_cyclic_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_first_cyclic_pure \<sigma> w x \<longleftrightarrow>
    (\<sigma> = pp_t_first_cyclic_unary_type
      \<and> pp_t_closed_logical_stock
        pp_t_first_cyclic_unary_type w x)
    \<or>
    (\<sigma> = pp_t_first_cyclic_classifier_type
      \<and> pp_t_eqv pp_t_first_cyclic_classifier_type w
        pp_t_old_unary_stock_classifier x)
    \<or>
    (\<sigma> = pp_t_first_cyclic_builder_type
      \<and> pp_t_eqv pp_t_first_cyclic_builder_type w
        pp_t_first_cyclic_builder_den x)"

lemma pp_t_first_cyclic_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_first_cyclic_pure \<sigma>)"
proof -
  have unary:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_unary_type
        (pp_t_closed_logical_stock pp_t_first_cyclic_unary_type)"
    by (rule pp_t_closed_logical_stock_admissible)
  have classifier:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_first_cyclic_classifier_type w
          pp_t_old_unary_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_old_unary_stock_classifier_in_domain] .
  have builder:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_builder_type
        (\<lambda>w x. pp_t_eqv pp_t_first_cyclic_builder_type w
          pp_t_first_cyclic_builder_den x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_first_cyclic_builder_den_in_domain] .
  show ?thesis
    using unary classifier builder
    unfolding pp_t_predicate_admissible_def
      pp_t_first_cyclic_pure_def
    by blast
qed

lemma pp_t_first_cyclic_pure_unary:
  "pp_t_first_cyclic_pure pp_t_first_cyclic_unary_type w x
    \<longleftrightarrow>
    pp_t_closed_logical_stock
      pp_t_first_cyclic_unary_type w x"
  by (simp add: pp_t_first_cyclic_pure_def)

lemma pp_t_first_cyclic_pure_classifier:
  "pp_t_first_cyclic_pure pp_t_first_cyclic_classifier_type w x
    \<longleftrightarrow>
    pp_t_eqv pp_t_first_cyclic_classifier_type w
      pp_t_old_unary_stock_classifier x"
  by (simp add: pp_t_first_cyclic_pure_def)

lemma pp_t_first_cyclic_pure_builder:
  "pp_t_first_cyclic_pure pp_t_first_cyclic_builder_type w x
    \<longleftrightarrow>
    pp_t_eqv pp_t_first_cyclic_builder_type w
      pp_t_first_cyclic_builder_den x"
  by (simp add: pp_t_first_cyclic_pure_def)

definition pp_t_first_cyclic_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_first_cyclic_constants =
    pp_t_seeded_internal_constants
      pp_t_first_cyclic_pure pp_t_generic_seed_at"

lemma pp_t_first_cyclic_seeded_fundamental[simp]:
  "pp_t_seeded_fundamental_at pp_t_generic_seed_at \<sigma> w x =
    pp_t_generic_fundamental_at \<sigma> w x"
  by (cases \<sigma>) simp_all

interpretation FirstCyclicConstants:
  pp_t_constants pp_t_first_cyclic_constants
proof
  fix c \<sigma>
  show "Elem (pp_t_first_cyclic_constants c \<sigma>)
      (pp_t_domain \<sigma>)"
  proof (cases \<sigma>)
    case Ind
    then show ?thesis
      unfolding pp_t_first_cyclic_constants_def
      using pp_t_default_in_domain[of Ind] by simp
  next
    case Prop
    then show ?thesis
      unfolding pp_t_first_cyclic_constants_def
      using pp_t_default_in_domain[of Prop] by simp
  next
    case (Arr \<sigma> \<tau>)
    have pure_classifier:
        "Elem (pp_t_classifier \<sigma> (pp_t_first_cyclic_pure \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF pp_t_first_cyclic_pure_admissible] .
    have fundamental_admissible:
        "pp_t_predicate_admissible \<sigma>
          (pp_t_seeded_fundamental_at
            pp_t_generic_seed_at \<sigma>)"
      using pp_t_generic_fundamental_admissible[
        of \<sigma>]
      unfolding pp_t_predicate_admissible_def
      by simp
    have fun_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_seeded_fundamental_at
              pp_t_generic_seed_at \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF fundamental_admissible] .
    have default:
        "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using pp_t_default_in_domain .
    show ?thesis
      using Arr pure_classifier fun_classifier default
      by (auto simp: pp_t_first_cyclic_constants_def
          pp_t_seeded_fundamental_at.simps)
  qed
qed

lemma pp_t_first_cyclic_eval_Pure[simp]:
  "pp_t_eval pp_t_first_cyclic_constants \<rho> (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma> (pp_t_first_cyclic_pure \<sigma>)"
  by (simp add: pp_t_first_cyclic_constants_def
      pp_Pure_def pp_pure_name_def)

lemma pp_t_first_cyclic_eval_Fun[simp]:
  "pp_t_eval pp_t_first_cyclic_constants \<rho> (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at pp_t_generic_seed_at \<sigma>)"
  by (simp add: pp_t_first_cyclic_constants_def
      pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_first_cyclic_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_first_cyclic_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_first_cyclic_pure \<sigma> w
        (pp_t_eval pp_t_first_cyclic_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_first_cyclic_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using FirstCyclicConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument, of "pp_t_first_cyclic_pure \<sigma>" w]
    by simp
qed

lemma pp_t_first_cyclic_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_first_cyclic_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_generic_fundamental_at \<sigma> w
        (pp_t_eval pp_t_first_cyclic_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_first_cyclic_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using FirstCyclicConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  have classifier:
      "pp_t_holds
        (pp_t_classifier \<sigma>
          (pp_t_seeded_fundamental_at
            pp_t_generic_seed_at \<sigma>)
          \<acute> pp_t_eval pp_t_first_cyclic_constants \<rho> M) w
      \<longleftrightarrow>
      pp_t_seeded_fundamental_at pp_t_generic_seed_at \<sigma> w
        (pp_t_eval pp_t_first_cyclic_constants \<rho> M)"
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at
        pp_t_generic_seed_at \<sigma>" w] .
  show ?thesis
    unfolding pp_fun_def
    using classifier by simp
qed

lemma pp_t_first_cyclic_unary_classifier:
  "pp_t_classifier pp_t_first_cyclic_unary_type
      (pp_t_first_cyclic_pure pp_t_first_cyclic_unary_type)
    = pp_t_old_unary_stock_classifier"
  unfolding pp_t_old_unary_stock_classifier_def
    pp_t_first_cyclic_pure_def
  by simp

lemma pp_t_first_cyclic_classifier_is_pure:
  "pp_t_first_cyclic_pure pp_t_first_cyclic_classifier_type w
    pp_t_old_unary_stock_classifier"
  apply (rule pp_t_first_cyclic_pure_classifier[THEN iffD2])
  using pp_t_eqv_reflexive[
    OF pp_t_old_unary_stock_classifier_in_domain] .

lemma pp_t_first_cyclic_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_first_cyclic_constants \<rho> pp_target_PP) w"
proof -
  have evaluation:
      "pp_t_eval pp_t_first_cyclic_constants \<rho> pp_target_PP =
        pp_t_classifier pp_t_first_cyclic_classifier_type
          (pp_t_first_cyclic_pure
            pp_t_first_cyclic_classifier_type)
        \<acute>
        pp_t_classifier pp_t_first_cyclic_unary_type
          (pp_t_first_cyclic_pure
            pp_t_first_cyclic_unary_type)"
    unfolding pp_target_PP_def pp_purity_of_pure_def pp_pure_def
    by simp
  have at_classifier:
      "pp_t_holds
        (pp_t_classifier pp_t_first_cyclic_classifier_type
          (pp_t_first_cyclic_pure
            pp_t_first_cyclic_classifier_type)
          \<acute> pp_t_old_unary_stock_classifier) w
      \<longleftrightarrow>
      pp_t_first_cyclic_pure
        pp_t_first_cyclic_classifier_type w
        pp_t_old_unary_stock_classifier"
    using pp_t_classifier_holds[
      OF pp_t_old_unary_stock_classifier_in_domain,
      of "pp_t_first_cyclic_pure
        pp_t_first_cyclic_classifier_type" w] .
  show ?thesis
    unfolding evaluation pp_t_first_cyclic_unary_classifier
    using at_classifier pp_t_first_cyclic_classifier_is_pure
    by blast
qed

theorem pp_t_first_cyclic_target_PP_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma> pp_target_PP"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_def
    FirstCyclicConstants.pp_t_den_def
  using pp_t_first_cyclic_target_PP_holds by blast

lemma pp_t_first_cyclic_builder_eval_eqv:
  "pp_t_eqv pp_t_first_cyclic_builder_type w
    pp_t_first_cyclic_builder_den
    (pp_t_eval pp_t_first_cyclic_constants \<rho>
      pp_finite_singleton_probe_builder)"
proof -
  have const_free:
      "consts_of pp_finite_singleton_probe_builder = {}"
    using pp_finite_singleton_probe_builder_logical
    unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval pp_t_first_cyclic_constants \<rho>
          pp_finite_singleton_probe_builder =
        pp_t_eval pp_t_default_constants \<rho>
          pp_finite_singleton_probe_builder"
    using pp_t_eval_const_free[OF const_free] .
  have eval_domain:
      "Elem
        (pp_t_eval pp_t_default_constants \<rho>
          pp_finite_singleton_probe_builder)
        (pp_t_domain pp_t_first_cyclic_builder_type)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF pp_finite_singleton_probe_builder_typed
        pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have closed_domain:
      "Elem
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_finite_singleton_probe_builder)
        (pp_t_domain pp_t_first_cyclic_builder_type)"
    using pp_t_closed_den_in_domain[
      OF pp_finite_singleton_probe_builder_typed]
    unfolding pp_t_closed_den_def .
  have related_forward:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_default_constants \<rho>
          pp_finite_singleton_probe_builder)
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_finite_singleton_probe_builder)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF pp_finite_singleton_probe_builder_typed
        pp_t_empty_env_eqv] .
  have related:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_finite_singleton_probe_builder)
        (pp_t_eval pp_t_default_constants \<rho>
          pp_finite_singleton_probe_builder)"
    using pp_t_eqv_symmetric[
      OF eval_domain closed_domain related_forward] .
  show ?thesis
    unfolding pp_t_first_cyclic_builder_den_def pp_t_closed_den_def
    using related change_constants by simp
qed

lemma pp_t_first_cyclic_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_first_cyclic_constants \<rho>
      (pp_pure pp_t_first_cyclic_builder_type
        pp_finite_singleton_probe_builder)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_first_cyclic_constants \<rho>
          (pp_pure pp_t_first_cyclic_builder_type
            pp_finite_singleton_probe_builder)) w
      \<longleftrightarrow>
      pp_t_first_cyclic_pure pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_first_cyclic_constants \<rho>
          pp_finite_singleton_probe_builder)"
    using pp_t_first_cyclic_eval_pure_holds[
      OF pp_finite_singleton_probe_builder_typed env, of w] .
  have pure:
      "pp_t_first_cyclic_pure pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_first_cyclic_constants \<rho>
          pp_finite_singleton_probe_builder)"
    apply (rule pp_t_first_cyclic_pure_builder[THEN iffD2])
    by (rule pp_t_first_cyclic_builder_eval_eqv)
  show ?thesis
    using evaluation pure by blast
qed

theorem pp_t_first_cyclic_builder_purity_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_first_cyclic_builder_type
      pp_finite_singleton_probe_builder)"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_def
    FirstCyclicConstants.pp_t_den_def
  using pp_t_first_cyclic_builder_purity_holds by blast

lemma pp_t_first_cyclic_application_absorbed:
  assumes f: "Elem f (pp_t_domain pp_t_first_cyclic_builder_type)"
    and x: "Elem x (pp_t_domain pp_t_first_cyclic_classifier_type)"
    and pure_f:
      "pp_t_first_cyclic_pure pp_t_first_cyclic_builder_type w f"
    and pure_x:
      "pp_t_first_cyclic_pure pp_t_first_cyclic_classifier_type w x"
  shows "pp_t_first_cyclic_pure pp_t_first_cyclic_unary_type
    w (f \<acute> x)"
proof -
  have f_eqv:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        pp_t_first_cyclic_builder_den f"
    using pure_f
    by (rule pp_t_first_cyclic_pure_builder[THEN iffD1])
  have x_eqv:
      "pp_t_eqv pp_t_first_cyclic_classifier_type w
        pp_t_old_unary_stock_classifier x"
    using pure_x
    by (rule pp_t_first_cyclic_pure_classifier[THEN iffD1])
  have builder:
      "Elem pp_t_first_cyclic_builder_den
        (pp_t_domain pp_t_first_cyclic_builder_type)"
    by (rule pp_t_first_cyclic_builder_den_in_domain)
  have old:
      "Elem pp_t_old_unary_stock_classifier
        (pp_t_domain pp_t_first_cyclic_classifier_type)"
    by (rule pp_t_old_unary_stock_classifier_in_domain)
  have f_eqv_elim:
      "\<forall>v. prefix w v \<longrightarrow>
        (\<forall>a b.
          Elem a (pp_t_domain pp_t_first_cyclic_classifier_type)
          \<longrightarrow>
          Elem b (pp_t_domain pp_t_first_cyclic_classifier_type)
          \<longrightarrow>
          pp_t_eqv pp_t_first_cyclic_classifier_type v a b
          \<longrightarrow>
          pp_t_eqv pp_t_first_cyclic_unary_type v
            (pp_t_first_cyclic_builder_den \<acute> a)
            (f \<acute> b))"
    using f_eqv
    by (rule pp_t_eqv.simps(3)[THEN iffD1])
  have first:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        (pp_t_first_cyclic_builder_den
          \<acute> pp_t_old_unary_stock_classifier)
        (f \<acute> pp_t_old_unary_stock_classifier)"
    using f_eqv_elim old pp_t_eqv_reflexive[OF old]
    by simp
  have second:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        (f \<acute> pp_t_old_unary_stock_classifier) (f \<acute> x)"
    using pp_t_arrow_member_respects[OF f old x x_eqv] .
  have output_eqv:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        (pp_t_first_cyclic_builder_den
          \<acute> pp_t_old_unary_stock_classifier)
        (f \<acute> x)"
    using pp_t_eqv_transitive[
      OF pp_t_app_closed[OF builder old]
        pp_t_app_closed[OF f old]
        pp_t_app_closed[OF f x] first second] .
  have output_is_test:
      "pp_t_first_cyclic_builder_den
        \<acute> pp_t_old_unary_stock_classifier =
        pp_t_one_step_singleton_test"
    unfolding pp_t_first_cyclic_builder_den_def
      pp_t_one_step_singleton_test_def
      pp_finite_singleton_probe_builder_eq_one_step
    by simp
  have test_stock:
      "pp_t_closed_logical_stock
        pp_t_first_cyclic_unary_type w
        (pp_t_first_cyclic_builder_den
          \<acute> pp_t_old_unary_stock_classifier)"
    unfolding output_is_test
    by (rule pp_t_singleton_test_in_closed_logical_stock)
  have output_stock:
      "pp_t_closed_logical_stock
        pp_t_first_cyclic_unary_type w (f \<acute> x)"
    using pp_t_closed_logical_stock_admissible[
      of pp_t_first_cyclic_unary_type]
      test_stock output_eqv
      pp_t_app_closed[OF builder old]
      pp_t_app_closed[OF f x]
    unfolding pp_t_predicate_admissible_def
    by blast
  show ?thesis
    using output_stock
    by (rule pp_t_first_cyclic_pure_unary[THEN iffD2])
qed

lemma pp_t_first_cyclic_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_first_cyclic_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x.
        Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_first_cyclic_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_first_cyclic_pure \<sigma> w x
        \<longrightarrow>
        pp_t_first_cyclic_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_first_cyclic_application_closure_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_first_cyclic_classifier_type
      pp_t_first_cyclic_unary_type)"
proof (rule FirstCyclicConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FirstCyclicConstants.pp_t_den
        (pp_application_closure
          pp_t_first_cyclic_classifier_type
          pp_t_first_cyclic_unary_type) env) w"
    unfolding FirstCyclicConstants.pp_t_den_def
      pp_t_first_cyclic_application_closure_holds_iff
    using pp_t_first_cyclic_application_absorbed by blast
qed

section \<open>The fixed Recombination principles\<close>

lemma pp_t_first_cyclic_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_first_cyclic_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_t_generic_seed_at w"
  have base: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[
      OF base pp_t_generic_seed_at_in_domain] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval pp_t_first_cyclic_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      using pp_t_eqv_reflexive[
        OF pp_t_generic_seed_at_in_domain] .
    show ?thesis
      using pp_t_first_cyclic_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_first_cyclic_constants
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_t_domain Prop)"
    have yr_env:
        "pp_t_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_t_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_first_cyclic_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_first_cyclic_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval pp_t_first_cyclic_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_first_cyclic_constants
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_t_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_t_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_t_generic_seed_at_in_domain
      r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

theorem pp_t_first_cyclic_unique_fundamental_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_def
    FirstCyclicConstants.pp_t_den_def
  using pp_t_first_cyclic_unique_fundamental_holds by blast

lemma pp_t_first_cyclic_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_first_cyclic_constants \<rho>
      pp_zeroary_recombination) w"
  by (simp add: pp_zeroary_recombination_def pp_pure_def
      pp_t_classifier_holds extend_env.simps
      pp_t_first_cyclic_pure_def)

theorem pp_t_first_cyclic_zeroary_recombination_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_def
    FirstCyclicConstants.pp_t_den_def
  using pp_t_first_cyclic_zeroary_recombination_holds by blast

lemma pp_t_first_cyclic_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_first_cyclic_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_first_cyclic_unary_type)
      \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_first_cyclic_pure
            pp_t_first_cyclic_unary_type w X
          \<and> pp_t_generic_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v)
          \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_first_cyclic_fundamental_recombines:
  assumes X:
      "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
    and X_pure:
      "pp_t_first_cyclic_pure
        pp_t_first_cyclic_unary_type w X"
    and r: "Elem r (pp_t_domain Prop)"
    and r_fundamental:
      "pp_t_generic_fundamental_at Prop w r"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w"
proof -
  have X_stock:
      "pp_t_closed_logical_stock
        pp_t_first_cyclic_unary_type w X"
    using X_pure
    by (rule pp_t_first_cyclic_pure_unary[THEN iffD1])
  show ?thesis
    using pp_t_generic_fundamental_recombines[
      OF X X_stock r r_fundamental necessary] .
qed

lemma pp_t_first_cyclic_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_first_cyclic_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_first_cyclic_unary_recombination_holds_iff
  using pp_t_first_cyclic_fundamental_recombines by blast

theorem pp_t_first_cyclic_unary_recombination_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_def
    FirstCyclicConstants.pp_t_den_def
  using pp_t_first_cyclic_unary_recombination_holds by blast

section \<open>Validity and consistency of the first cyclic package\<close>

theorem pp_t_first_cyclic_package_gvalid:
  "FirstCyclicConstants.TreeHenkin.gvalid_set
    pp_finite_first_cyclic_package"
  unfolding FirstCyclicConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_finite_first_cyclic_package"
  from A consider
      (target) "A = pp_target_PP"
    | (unique) "A = pp_unique_fundamental Prop"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
    | (builder)
        "A = pp_pure pp_t_first_cyclic_builder_type
          pp_finite_singleton_probe_builder"
    | (application)
        "A = pp_application_closure
          pp_t_first_cyclic_classifier_type
          pp_t_first_cyclic_unary_type"
    unfolding pp_finite_first_cyclic_package_def
      pp_recombination_fixed_axioms_def
    by blast
  then show "FirstCyclicConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case target
    then show ?thesis
      using pp_t_first_cyclic_target_PP_gvalid by simp
  next
    case unique
    then show ?thesis
      using pp_t_first_cyclic_unique_fundamental_gvalid by simp
  next
    case zeroary
    then show ?thesis
      using pp_t_first_cyclic_zeroary_recombination_gvalid by simp
  next
    case unary
    then show ?thesis
      using pp_t_first_cyclic_unary_recombination_gvalid by simp
  next
    case builder
    then show ?thesis
      using pp_t_first_cyclic_builder_purity_gvalid by simp
  next
    case application
    then show ?thesis
      using pp_t_first_cyclic_application_closure_gvalid by simp
  qed
qed

theorem pp_finite_first_cyclic_package_consistent:
  "CEV_axiom_consistent [] pp_finite_first_cyclic_package"
  using FirstCyclicConstants.pp_t_base_sound
    FirstCyclicConstants.pp_t_zeta_sound
    pp_t_first_cyclic_package_gvalid
  by (rule
    FirstCyclicConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

section \<open>The next incoming generator\<close>

text \<open>
  The type-level strongly connected component does not change when a
  different pure term of type \<open>C \<rightarrow>\<^sub>o U\<close> is added.  What changes is
  the value injected into the component.  We classify an incoming
  family-probe generator as covered by the present elimination method when
  its underlying family is view-complete and its view condition has one
  closed logical definition.
\<close>

definition pp_t_family_cycle_elimination_covered ::
    "oterm \<Rightarrow> bool" where
  "pp_t_family_cycle_elimination_covered B \<longleftrightarrow>
    pp_t_family_view_complete B
    \<and> pp_t_family_view_condition_definable B"

lemma pp_t_singleton_cycle_elimination_covered:
  "pp_t_family_cycle_elimination_covered
    pp_t_singleton_family_builder"
proof -
  have complete:
      "pp_t_family_view_complete pp_t_singleton_family_builder"
    using pp_t_injective_logical_family_view_complete[
      OF pp_t_singleton_family_builder_typed
        pp_t_singleton_family_builder_logical
        pp_t_singleton_family_is_injective] .
  have definable:
      "pp_t_family_view_condition_definable
        pp_t_singleton_family_builder"
    using pp_t_injective_logical_family_view_condition_definable[
      OF pp_t_singleton_family_builder_typed
        pp_t_singleton_family_builder_logical
        pp_t_singleton_family_is_injective] .
  show ?thesis
    using complete definable
    unfolding pp_t_family_cycle_elimination_covered_def
    by blast
qed

theorem pp_t_symmetrized_singleton_cycle_not_elimination_covered:
  "\<not> pp_t_family_cycle_elimination_covered
    pp_t_symmetrized_singleton_family_builder"
  using pp_t_symmetrized_singleton_not_view_complete
  unfolding pp_t_family_cycle_elimination_covered_def
  by blast

definition pp_t_next_classifier_cycle_builder :: oterm where
  "pp_t_next_classifier_cycle_builder =
    pp_t_family_probe_builder
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_next_classifier_cycle_builder_typed:
  "[] \<turnstile> pp_t_next_classifier_cycle_builder :
    pp_t_first_cyclic_builder_type"
  unfolding pp_t_next_classifier_cycle_builder_def
  using pp_t_family_probe_builder_typed[
    OF pp_t_symmetrized_singleton_family_builder_typed] .

lemma pp_t_next_classifier_cycle_builder_logical:
  "pp_logical_vocabulary pp_t_next_classifier_cycle_builder"
  unfolding pp_t_next_classifier_cycle_builder_def
  using pp_t_family_probe_builder_logical[
    OF pp_t_symmetrized_singleton_family_builder_logical] .

definition pp_t_next_classifier_cycle_forced_value :: ZF where
  "pp_t_next_classifier_cycle_forced_value =
    pp_t_family_probe
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_next_classifier_cycle_forced_value_eq:
  "pp_t_next_classifier_cycle_forced_value =
    pp_t_closed_den pp_t_next_classifier_cycle_builder
      \<acute> pp_t_old_unary_stock_classifier"
  unfolding pp_t_next_classifier_cycle_forced_value_def
    pp_t_next_classifier_cycle_builder_def
    pp_t_family_probe_def
  by simp

lemma pp_t_next_classifier_cycle_forced_value_in_domain:
  "Elem pp_t_next_classifier_cycle_forced_value
    (pp_t_domain pp_t_first_cyclic_unary_type)"
  unfolding pp_t_next_classifier_cycle_forced_value_def
  using pp_t_family_probe_in_domain[
    OF pp_t_symmetrized_singleton_family_builder_typed] .

lemma pp_t_next_classifier_cycle_forced_by_application:
  assumes builder:
      "Pure pp_t_first_cyclic_builder_type w
        (pp_t_closed_den pp_t_next_classifier_cycle_builder)"
    and classifier:
      "Pure pp_t_first_cyclic_classifier_type w
        pp_t_old_unary_stock_classifier"
    and application:
      "\<And>f x.
        Pure pp_t_first_cyclic_builder_type w f
        \<Longrightarrow>
        Pure pp_t_first_cyclic_classifier_type w x
        \<Longrightarrow>
        Pure pp_t_first_cyclic_unary_type w (f \<acute> x)"
  shows "Pure pp_t_first_cyclic_unary_type w
    pp_t_next_classifier_cycle_forced_value"
  unfolding pp_t_next_classifier_cycle_forced_value_eq
  using application[OF builder classifier] .

section \<open>One-step absorption of the symmetrized-singleton probe\<close>

definition pp_t_symmetrized_enlarged_unary_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_symmetrized_enlarged_unary_stock w X \<longleftrightarrow>
    pp_t_closed_logical_stock
      pp_t_first_cyclic_unary_type w X
    \<or>
    pp_t_eqv pp_t_first_cyclic_unary_type w
      pp_t_next_classifier_cycle_forced_value X"

lemma pp_t_symmetrized_enlarged_unary_stock_admissible:
  "pp_t_predicate_admissible pp_t_first_cyclic_unary_type
    pp_t_symmetrized_enlarged_unary_stock"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_first_cyclic_unary_type
        (pp_t_closed_logical_stock
          pp_t_first_cyclic_unary_type)"
    by (rule pp_t_closed_logical_stock_admissible)
  have added:
      "pp_t_predicate_admissible pp_t_first_cyclic_unary_type
        (\<lambda>w X.
          pp_t_eqv pp_t_first_cyclic_unary_type w
            pp_t_next_classifier_cycle_forced_value X)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_next_classifier_cycle_forced_value_in_domain] .
  show ?thesis
    using old added
    unfolding pp_t_predicate_admissible_def
      pp_t_symmetrized_enlarged_unary_stock_def
    by blast
qed

definition pp_t_symmetrized_enlarged_classifier :: ZF where
  "pp_t_symmetrized_enlarged_classifier =
    pp_t_classifier pp_t_first_cyclic_unary_type
      pp_t_symmetrized_enlarged_unary_stock"

lemma pp_t_symmetrized_enlarged_classifier_in_domain:
  "Elem pp_t_symmetrized_enlarged_classifier
    (pp_t_domain pp_t_first_cyclic_classifier_type)"
  unfolding pp_t_symmetrized_enlarged_classifier_def
  using pp_t_classifier_in_domain[
    OF pp_t_symmetrized_enlarged_unary_stock_admissible] .

definition pp_t_symmetrized_reevaluated_probe :: ZF where
  "pp_t_symmetrized_reevaluated_probe =
    pp_t_closed_den pp_t_next_classifier_cycle_builder
      \<acute> pp_t_symmetrized_enlarged_classifier"

lemma pp_t_symmetrized_reevaluated_probe_in_domain:
  "Elem pp_t_symmetrized_reevaluated_probe
    (pp_t_domain pp_t_first_cyclic_unary_type)"
  unfolding pp_t_symmetrized_reevaluated_probe_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_next_classifier_cycle_builder_typed]
      pp_t_symmetrized_enlarged_classifier_in_domain] .

lemma pp_t_symmetrized_reevaluated_probe_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_symmetrized_reevaluated_probe \<acute> p =
    pp_t_symmetrized_enlarged_classifier
      \<acute> (pp_t_symmetrized_singleton_family_at p)"
  unfolding pp_t_symmetrized_reevaluated_probe_def
    pp_t_next_classifier_cycle_builder_def
    pp_t_family_probe_builder_def pp_t_closed_den_def
  using p pp_t_symmetrized_enlarged_classifier_in_domain
    pp_t_closed_den_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed]
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_symmetrized_probe_collision_absorbed:
  assumes p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        pp_t_next_classifier_cycle_forced_value
        (pp_t_symmetrized_singleton_family_at p)"
  shows "pp_t_closed_logical_stock
    pp_t_first_cyclic_unary_type w
    (pp_t_symmetrized_singleton_family_at p)"
proof -
  have family:
      "Elem (pp_t_symmetrized_singleton_family_at p)
        (pp_t_domain pp_t_first_cyclic_unary_type)"
    using pp_t_symmetrized_singleton_family_at_in_domain[OF p] .
  have pp:
      "pp_t_eqv Prop w p p"
    by (rule pp_t_eqv_reflexive[OF p])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_next_classifier_cycle_forced_value \<acute> p)
        (pp_t_symmetrized_singleton_family_at p \<acute> p)"
    using collision p pp by auto
  have family_true:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at p \<acute> p) w"
  proof -
    have semantic:
        "pp_t_holds
          (pp_t_symmetrized_singleton_family_at p \<acute> p) w
        \<longleftrightarrow>
        pp_t_eqv Prop w p p
          \<or> pp_t_eqv Prop w p (pp_t_complement p)"
      using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF p p, of w] .
    show ?thesis
      using semantic pp by blast
  qed
  have probe_true:
      "pp_t_holds
        (pp_t_next_classifier_cycle_forced_value \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      family_true by simp
  have probe_true':
      "pp_t_holds
        (pp_t_family_probe
          pp_t_symmetrized_singleton_family_builder \<acute> p) w"
    using probe_true
    unfolding pp_t_next_classifier_cycle_forced_value_def .
  show ?thesis
    using pp_t_family_probe_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed p,
      of w]
      probe_true' by blast
qed

theorem pp_t_symmetrized_probe_stabilizes_after_one_enlargement:
  "pp_t_symmetrized_reevaluated_probe =
    pp_t_next_classifier_cycle_forced_value"
proof (rule pp_t_unary_function_ext)
  show "Elem pp_t_symmetrized_reevaluated_probe
      (pp_t_domain pp_t_first_cyclic_unary_type)"
    by (rule pp_t_symmetrized_reevaluated_probe_in_domain)
  show "Elem pp_t_next_classifier_cycle_forced_value
      (pp_t_domain pp_t_first_cyclic_unary_type)"
    by (rule pp_t_next_classifier_cycle_forced_value_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_symmetrized_reevaluated_probe \<acute> p =
      pp_t_next_classifier_cycle_forced_value \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_symmetrized_reevaluated_probe \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_reevaluated_probe_in_domain p] .
    show "Elem (pp_t_next_classifier_cycle_forced_value \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_next_classifier_cycle_forced_value_in_domain p] .
    fix w
    have reevaluated:
        "pp_t_holds
          (pp_t_symmetrized_reevaluated_probe \<acute> p) w
        \<longleftrightarrow>
        pp_t_symmetrized_enlarged_unary_stock w
          (pp_t_symmetrized_singleton_family_at p)"
      unfolding pp_t_symmetrized_reevaluated_probe_apply[OF p]
        pp_t_symmetrized_enlarged_classifier_def
      using pp_t_classifier_holds[
        OF pp_t_symmetrized_singleton_family_at_in_domain[OF p],
        of pp_t_symmetrized_enlarged_unary_stock w] .
    have old:
        "pp_t_holds
          (pp_t_next_classifier_cycle_forced_value \<acute> p) w
        \<longleftrightarrow>
        pp_t_closed_logical_stock
          pp_t_first_cyclic_unary_type w
          (pp_t_symmetrized_singleton_family_at p)"
      using pp_t_family_probe_apply_holds[
        OF pp_t_symmetrized_singleton_family_builder_typed p,
        of w]
      unfolding pp_t_next_classifier_cycle_forced_value_def .
    show "pp_t_holds
          (pp_t_symmetrized_reevaluated_probe \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_next_classifier_cycle_forced_value \<acute> p) w"
      using reevaluated old
        pp_t_symmetrized_probe_collision_absorbed[OF p, of w]
      unfolding pp_t_symmetrized_enlarged_unary_stock_def
      by blast
  qed
qed

lemma pp_t_next_classifier_cycle_forced_value_cone_natural:
  "pp_t_cone_rel pp_t_first_cyclic_unary_type s
    pp_t_next_classifier_cycle_forced_value
    pp_t_next_classifier_cycle_forced_value"
proof -
  have builder:
      "pp_t_cone_rel pp_t_first_cyclic_builder_type s
        (pp_t_closed_den pp_t_next_classifier_cycle_builder)
        (pp_t_closed_den pp_t_next_classifier_cycle_builder)"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF pp_t_next_classifier_cycle_builder_typed
        pp_t_next_classifier_cycle_builder_logical] .
  have classifier:
      "pp_t_cone_rel pp_t_first_cyclic_classifier_type s
        pp_t_old_unary_stock_classifier
        pp_t_old_unary_stock_classifier"
    by (rule pp_t_old_unary_stock_classifier_cone_natural)
  show ?thesis
    unfolding pp_t_next_classifier_cycle_forced_value_eq
    using builder classifier
      pp_t_old_unary_stock_classifier_in_domain by auto
qed

lemma pp_t_symmetrized_enlarged_unary_stock_cone_iff:
  assumes X: "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_first_cyclic_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_first_cyclic_unary_type s X Y"
  shows "pp_t_symmetrized_enlarged_unary_stock (s @ u) X
    \<longleftrightarrow>
    pp_t_symmetrized_enlarged_unary_stock u Y"
proof -
  have old:
      "pp_t_closed_logical_stock
          pp_t_first_cyclic_unary_type (s @ u) X
      \<longleftrightarrow>
      pp_t_closed_logical_stock
          pp_t_first_cyclic_unary_type u Y"
    using pp_t_closed_logical_stock_cone_iff[
      OF X Y XY, of u] .
  have added:
      "pp_t_eqv pp_t_first_cyclic_unary_type (s @ u)
          pp_t_next_classifier_cycle_forced_value X
      \<longleftrightarrow>
      pp_t_eqv pp_t_first_cyclic_unary_type u
          pp_t_next_classifier_cycle_forced_value Y"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF pp_t_next_classifier_cycle_forced_value_in_domain
        pp_t_next_classifier_cycle_forced_value_in_domain
        X Y
        pp_t_next_classifier_cycle_forced_value_cone_natural
        XY,
      of u] .
  show ?thesis
    unfolding pp_t_symmetrized_enlarged_unary_stock_def
    using old added by blast
qed

definition pp_t_symmetrized_unary_representatives :: "ZF set" where
  "pp_t_symmetrized_unary_representatives =
    pp_t_exact_closed_logical_operators
      \<union> {pp_t_next_classifier_cycle_forced_value}"

lemma pp_t_symmetrized_unary_representatives_countable:
  "countable pp_t_symmetrized_unary_representatives"
  unfolding pp_t_symmetrized_unary_representatives_def
  using pp_t_exact_closed_logical_operators_countable
  by simp

lemma pp_t_symmetrized_unary_representative_in_domain:
  assumes "X \<in> pp_t_symmetrized_unary_representatives"
  shows "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
  using assms pp_t_exact_closed_logical_operator_in_domain
    pp_t_next_classifier_cycle_forced_value_in_domain
  unfolding pp_t_symmetrized_unary_representatives_def
  by blast

lemma pp_t_symmetrized_unary_representative_cone_natural:
  assumes X: "X \<in> pp_t_symmetrized_unary_representatives"
  shows "pp_t_cone_rel pp_t_first_cyclic_unary_type s X X"
proof (cases "X = pp_t_next_classifier_cycle_forced_value")
  case True
  then show ?thesis
    using pp_t_next_classifier_cycle_forced_value_cone_natural
    by simp
next
  case False
  then have exact:
      "X \<in> pp_t_exact_closed_logical_operators"
    using X
    unfolding pp_t_symmetrized_unary_representatives_def
    by blast
  then obtain M where typed:
      "[] \<turnstile> M : pp_t_first_cyclic_unary_type"
    and logical: "pp_logical_vocabulary M"
    and X_den: "X = pp_t_closed_den M"
    unfolding pp_t_exact_closed_logical_operators_def
    by blast
  show ?thesis
    unfolding X_den
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
qed

lemma pp_t_symmetrized_unary_representative_equivariant:
  assumes "X \<in> pp_t_symmetrized_unary_representatives"
  shows "pp_b_equivariant (pp_b_operator_of X)"
  using pp_t_cone_rel_operator_implies_equivariant[
    OF pp_t_symmetrized_unary_representative_cone_natural[
      OF assms]] .

lemma pp_t_symmetrized_enlarged_root_represented:
  assumes X: "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
    and stock: "pp_t_symmetrized_enlarged_unary_stock [] X"
  obtains d where
    "d \<in> pp_t_symmetrized_unary_representatives"
    "pp_t_eqv pp_t_first_cyclic_unary_type [] X d"
proof (cases
    "pp_t_closed_logical_stock
      pp_t_first_cyclic_unary_type [] X")
  case True
  then obtain M where typed:
      "[] \<turnstile> M : pp_t_first_cyclic_unary_type"
    and logical: "pp_logical_vocabulary M"
    and XM:
      "pp_t_eqv pp_t_first_cyclic_unary_type []
        X (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have member:
      "pp_t_closed_den M
        \<in> pp_t_symmetrized_unary_representatives"
    unfolding pp_t_symmetrized_unary_representatives_def
      pp_t_exact_closed_logical_operators_def
    using typed logical by blast
  show ?thesis
    using that[OF member XM] .
next
  case False
  have PX:
      "pp_t_eqv pp_t_first_cyclic_unary_type []
        pp_t_next_classifier_cycle_forced_value X"
    using stock False
    unfolding pp_t_symmetrized_enlarged_unary_stock_def
    by blast
  have XP:
      "pp_t_eqv pp_t_first_cyclic_unary_type [] X
        pp_t_next_classifier_cycle_forced_value"
    using pp_t_eqv_symmetric[
      OF pp_t_next_classifier_cycle_forced_value_in_domain X PX] .
  have member:
      "pp_t_next_classifier_cycle_forced_value
        \<in> pp_t_symmetrized_unary_representatives"
    unfolding pp_t_symmetrized_unary_representatives_def
    by simp
  show ?thesis
    using that[OF member XP] .
qed

theorem pp_t_symmetrized_enlarged_root_seed_exists:
  "\<exists>r. Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_symmetrized_enlarged_unary_stock r []"
proof -
  let ?S =
    "pp_b_operator_of `
      pp_t_symmetrized_unary_representatives"
  have countable: "countable ?S"
    using pp_t_symmetrized_unary_representatives_countable
    by (rule countable_image)
  have equivariant:
      "\<And>F. F \<in> ?S \<Longrightarrow> pp_b_equivariant F"
    using pp_t_symmetrized_unary_representative_equivariant
    by blast
  obtain R where generic:
      "\<forall>F \<in> ?S. pp_b_root_unary_recombination F R"
    using pp_b_generic_witness_for_countable_stock[
      OF countable equivariant] by blast
  let ?r = "pp_zf_of_b R"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have pointwise:
      "\<And>X q.
        Elem X (pp_t_domain pp_t_first_cyclic_unary_type)
        \<Longrightarrow>
        pp_t_symmetrized_enlarged_unary_stock [] X
        \<Longrightarrow>
        (\<forall>w. pp_t_holds (X \<acute> ?r) w)
        \<Longrightarrow>
        Elem q (pp_t_domain Prop)
        \<Longrightarrow>
        pp_t_holds (X \<acute> q) []"
  proof -
    fix X q
    assume X: "Elem X
        (pp_t_domain pp_t_first_cyclic_unary_type)"
      and X_stock:
        "pp_t_symmetrized_enlarged_unary_stock [] X"
      and necessary:
        "\<forall>w. pp_t_holds (X \<acute> ?r) w"
      and q: "Elem q (pp_t_domain Prop)"
    obtain d where d:
        "d \<in> pp_t_symmetrized_unary_representatives"
      and Xd:
        "pp_t_eqv pp_t_first_cyclic_unary_type [] X d"
      using pp_t_symmetrized_enlarged_root_represented[
        OF X X_stock] by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_first_cyclic_unary_type)"
      using pp_t_symmetrized_unary_representative_in_domain[OF d] .
    have d_necessary: "\<forall>w. pp_t_holds (d \<acute> ?r) w"
    proof
      fix w
      have Xd_w:
          "pp_t_eqv pp_t_first_cyclic_unary_type w X d"
        using pp_t_eqv_persistent[OF Xd, of w] by simp
      have rr: "pp_t_eqv Prop w ?r ?r"
        using pp_t_eqv_reflexive[OF r] .
      have applications:
          "pp_t_eqv Prop w (X \<acute> ?r) (d \<acute> ?r)"
        using Xd_w r rr by auto
      show "pp_t_holds (d \<acute> ?r) w"
        using pp_t_prop_eqv_at[OF applications, of w]
          necessary[rule_format, of w]
        by simp
    qed
    have d_operator: "pp_b_operator_of d \<in> ?S"
      using d by blast
    have d_universal:
        "\<forall>a. Elem a (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (d \<acute> a) []"
      using pp_b_recombination_transfers_to_zf[
        OF generic[rule_format, OF d_operator] d_necessary] .
    have Xd_q:
        "pp_t_eqv Prop [] (X \<acute> q) (d \<acute> q)"
      using Xd q pp_t_eqv_reflexive[OF q] by auto
    have transfer:
        "pp_t_holds (X \<acute> q) []
          \<longleftrightarrow> pp_t_holds (d \<acute> q) []"
      using pp_t_prop_eqv_at[OF Xd_q, of "[]"] by simp
    have dq: "pp_t_holds (d \<acute> q) []"
      using d_universal q by blast
    show "pp_t_holds (X \<acute> q) []"
      by (metis transfer dq)
  qed
  have recombines:
      "pp_t_unary_recombines_at
        pp_t_symmetrized_enlarged_unary_stock ?r []"
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
  show ?thesis
    using r recombines by blast
qed

theorem pp_t_symmetrized_root_recombination_transports_to_cone:
  assumes r: "Elem r (pp_t_domain Prop)"
    and root:
      "pp_t_unary_recombines_at
        pp_t_symmetrized_enlarged_unary_stock r []"
  shows "pp_t_unary_recombines_at
    pp_t_symmetrized_enlarged_unary_stock
    (pp_t_cone_lift w r) w"
proof -
  have pointwise:
      "\<And>Y q.
        Elem Y (pp_t_domain pp_t_first_cyclic_unary_type)
        \<Longrightarrow>
        pp_t_symmetrized_enlarged_unary_stock w Y
        \<Longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (Y \<acute> pp_t_cone_lift w r) v)
        \<Longrightarrow>
        Elem q (pp_t_domain Prop)
        \<Longrightarrow>
        pp_t_holds (Y \<acute> q) w"
  proof -
    fix Y q
    assume Y:
        "Elem Y (pp_t_domain pp_t_first_cyclic_unary_type)"
      and Y_stock:
        "pp_t_symmetrized_enlarged_unary_stock w Y"
      and necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (Y \<acute> pp_t_cone_lift w r) v"
      and q: "Elem q (pp_t_domain Prop)"
    let ?Z =
      "pp_t_cone_restrict pp_t_first_cyclic_unary_type w Y"
    let ?p = "pp_t_cone_restrict Prop w q"
    have Z:
        "Elem ?Z (pp_t_domain pp_t_first_cyclic_unary_type)"
      using pp_t_cone_restrict_in_domain[OF Y] .
    have p: "Elem ?p (pp_t_domain Prop)"
      using pp_t_cone_restrict_in_domain[OF q] .
    have YZ:
        "pp_t_cone_rel pp_t_first_cyclic_unary_type w Y ?Z"
      using pp_t_cone_restrict_related[OF Y] .
    have lift_r:
        "pp_t_cone_rel Prop w (pp_t_cone_lift w r) r"
      using pp_t_cone_extend_related[OF r, of w] by simp
    have qp: "pp_t_cone_rel Prop w q ?p"
      using pp_t_cone_restrict_related[OF q] .
    have Z_stock:
        "pp_t_symmetrized_enlarged_unary_stock [] ?Z"
      using
        pp_t_symmetrized_enlarged_unary_stock_cone_iff[
          OF Y Z YZ, of "[]"]
        Y_stock by simp
    have Z_necessary: "\<forall>u. pp_t_holds (?Z \<acute> r) u"
    proof
      fix u
      have outputs:
          "pp_t_cone_rel Prop w
            (Y \<acute> pp_t_cone_lift w r) (?Z \<acute> r)"
        using YZ pp_t_cone_lift_in_domain r lift_r by auto
      have left:
          "pp_t_holds
            (Y \<acute> pp_t_cone_lift w r) (w @ u)"
        using necessary by simp
      show "pp_t_holds (?Z \<acute> r) u"
        using outputs left by auto
    qed
    have Z_universal:
        "\<forall>a. Elem a (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (?Z \<acute> a) []"
      using root Z Z_stock Z_necessary
      unfolding pp_t_unary_recombines_at_def by blast
    have Zp: "pp_t_holds (?Z \<acute> ?p) []"
      using Z_universal p by blast
    have outputs:
        "pp_t_cone_rel Prop w (Y \<acute> q) (?Z \<acute> ?p)"
      using YZ q p qp by auto
    have all_outputs:
        "\<forall>u. pp_t_holds (Y \<acute> q) (w @ u)
          \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) u"
      using outputs by simp
    have at_root:
        "pp_t_holds (Y \<acute> q) (w @ [])
          \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) []"
      using all_outputs[rule_format, of "[]"] .
    show "pp_t_holds (Y \<acute> q) w"
      using at_root Zp by simp
  qed
  show ?thesis
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
qed

definition pp_t_symmetrized_root_seed :: ZF where
  "pp_t_symmetrized_root_seed =
    (SOME r. Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_symmetrized_enlarged_unary_stock r [])"

lemma pp_t_symmetrized_root_seed_spec:
  "Elem pp_t_symmetrized_root_seed (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_symmetrized_enlarged_unary_stock
      pp_t_symmetrized_root_seed []"
  unfolding pp_t_symmetrized_root_seed_def
  using someI_ex[OF pp_t_symmetrized_enlarged_root_seed_exists] .

definition pp_t_symmetrized_seed_at :: "bool list \<Rightarrow> ZF" where
  "pp_t_symmetrized_seed_at w =
    pp_t_cone_lift w pp_t_symmetrized_root_seed"

lemma pp_t_symmetrized_seed_at_in_domain:
  "Elem (pp_t_symmetrized_seed_at w) (pp_t_domain Prop)"
  unfolding pp_t_symmetrized_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem pp_t_symmetrized_seed_recombines_at_every_world:
  "pp_t_unary_recombines_at
    pp_t_symmetrized_enlarged_unary_stock
    (pp_t_symmetrized_seed_at w) w"
  unfolding pp_t_symmetrized_seed_at_def
  using pp_t_symmetrized_root_recombination_transports_to_cone[
    OF pp_t_symmetrized_root_seed_spec[THEN conjunct1]
      pp_t_symmetrized_root_seed_spec[THEN conjunct2]] .

section \<open>Recombination after closure under negation\<close>

lemma pp_t_symmetrized_closed_stock_probe_eq_forced_value:
  "pp_t_symmetrized_closed_stock_probe =
    pp_t_next_classifier_cycle_forced_value"
  unfolding pp_t_symmetrized_closed_stock_probe_def
    pp_t_next_classifier_cycle_forced_value_def
    pp_t_family_probe_def
    pp_t_family_probe_for_stock_def
    pp_t_old_unary_stock_classifier_def
  by simp

lemma pp_t_symmetrized_closed_stock_probe_cone_natural:
  "pp_t_cone_rel pp_t_first_cyclic_unary_type s
    pp_t_symmetrized_closed_stock_probe
    pp_t_symmetrized_closed_stock_probe"
  unfolding pp_t_symmetrized_closed_stock_probe_eq_forced_value
  by (rule pp_t_next_classifier_cycle_forced_value_cone_natural)

lemma pp_t_symmetrized_closed_stock_probe_complement_cone_natural:
  "pp_t_cone_rel pp_t_first_cyclic_unary_type s
    (pp_t_unary_complement
      pp_t_symmetrized_closed_stock_probe)
    (pp_t_unary_complement
      pp_t_symmetrized_closed_stock_probe)"
proof -
  let ?N = "pp_t_closed_den pp_t_unary_output_negator"
  have N_domain:
      "Elem ?N
        (pp_t_domain
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_t_unary_output_negator_typed] .
  have N_cone:
      "pp_t_cone_rel
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
        s ?N ?N"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF pp_t_unary_output_negator_typed
        pp_t_unary_output_negator_logical] .
  have P_domain:
      "Elem pp_t_symmetrized_closed_stock_probe
        (pp_t_domain pp_t_first_cyclic_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  have applied:
      "pp_t_cone_rel pp_t_first_cyclic_unary_type s
        (?N \<acute> pp_t_symmetrized_closed_stock_probe)
        (?N \<acute> pp_t_symmetrized_closed_stock_probe)"
    using N_cone P_domain
      pp_t_symmetrized_closed_stock_probe_cone_natural by auto
  show ?thesis
    using applied
    by (simp only:
      pp_t_unary_output_negator_apply[OF P_domain])
qed

lemma pp_t_symmetrized_negation_closed_stock_cone_iff:
  assumes X: "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_first_cyclic_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_first_cyclic_unary_type s X Y"
  shows "pp_t_symmetrized_negation_closed_stock (s @ u) X
    \<longleftrightarrow>
    pp_t_symmetrized_negation_closed_stock u Y"
proof -
  have old:
      "pp_t_closed_logical_stock pp_t_first_cyclic_unary_type
          (s @ u) X
      \<longleftrightarrow>
      pp_t_closed_logical_stock pp_t_first_cyclic_unary_type u Y"
    using pp_t_closed_logical_stock_cone_iff[
      OF X Y XY] .
  have P_domain:
      "Elem pp_t_symmetrized_closed_stock_probe
        (pp_t_domain pp_t_first_cyclic_unary_type)"
    by (rule pp_t_symmetrized_closed_stock_probe_in_domain)
  have probe:
      "pp_t_eqv pp_t_first_cyclic_unary_type (s @ u)
          pp_t_symmetrized_closed_stock_probe X
      \<longleftrightarrow>
      pp_t_eqv pp_t_first_cyclic_unary_type u
          pp_t_symmetrized_closed_stock_probe Y"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF P_domain P_domain X Y
        pp_t_symmetrized_closed_stock_probe_cone_natural XY,
      of u] .
  have cP_domain:
      "Elem
        (pp_t_unary_complement
          pp_t_symmetrized_closed_stock_probe)
        (pp_t_domain pp_t_first_cyclic_unary_type)"
    using pp_t_unary_complement_in_domain[OF P_domain] .
  have complement:
      "pp_t_eqv pp_t_first_cyclic_unary_type (s @ u)
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe) X
      \<longleftrightarrow>
      pp_t_eqv pp_t_first_cyclic_unary_type u
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe) Y"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF cP_domain cP_domain X Y
        pp_t_symmetrized_closed_stock_probe_complement_cone_natural
        XY,
      of u] .
  show ?thesis
    unfolding pp_t_symmetrized_negation_closed_stock_def
    using old probe complement by blast
qed

definition pp_t_symmetrized_negation_closed_representatives ::
    "ZF set"
where
  "pp_t_symmetrized_negation_closed_representatives =
    pp_t_exact_closed_logical_operators
    \<union> {
      pp_t_symmetrized_closed_stock_probe,
      pp_t_unary_complement
        pp_t_symmetrized_closed_stock_probe}"

lemma
  pp_t_symmetrized_negation_closed_representatives_countable:
  "countable pp_t_symmetrized_negation_closed_representatives"
  unfolding
    pp_t_symmetrized_negation_closed_representatives_def
  using pp_t_exact_closed_logical_operators_countable
  by simp

lemma
  pp_t_symmetrized_negation_closed_representative_in_domain:
  assumes
    "X \<in> pp_t_symmetrized_negation_closed_representatives"
  shows "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
  using assms pp_t_exact_closed_logical_operator_in_domain
    pp_t_symmetrized_closed_stock_probe_in_domain
    pp_t_unary_complement_in_domain[
      OF pp_t_symmetrized_closed_stock_probe_in_domain]
  unfolding
    pp_t_symmetrized_negation_closed_representatives_def
  by blast

lemma
  pp_t_symmetrized_negation_closed_representative_cone_natural:
  assumes
    X: "X \<in> pp_t_symmetrized_negation_closed_representatives"
  shows "pp_t_cone_rel pp_t_first_cyclic_unary_type s X X"
proof (cases
    "X = pp_t_symmetrized_closed_stock_probe
      \<or>
     X = pp_t_unary_complement
       pp_t_symmetrized_closed_stock_probe")
  case True
  then show ?thesis
    using pp_t_symmetrized_closed_stock_probe_cone_natural
      pp_t_symmetrized_closed_stock_probe_complement_cone_natural
    by blast
next
  case False
  then have exact:
      "X \<in> pp_t_exact_closed_logical_operators"
    using X
    unfolding
      pp_t_symmetrized_negation_closed_representatives_def
    by blast
  then obtain M where typed:
      "[] \<turnstile> M : pp_t_first_cyclic_unary_type"
    and logical: "pp_logical_vocabulary M"
    and X_den: "X = pp_t_closed_den M"
    unfolding pp_t_exact_closed_logical_operators_def
    by blast
  show ?thesis
    unfolding X_den
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
qed

lemma
  pp_t_symmetrized_negation_closed_representative_equivariant:
  assumes
    "X \<in> pp_t_symmetrized_negation_closed_representatives"
  shows "pp_b_equivariant (pp_b_operator_of X)"
  using pp_t_cone_rel_operator_implies_equivariant[
    OF
      pp_t_symmetrized_negation_closed_representative_cone_natural[
        OF assms]] .

lemma pp_t_symmetrized_negation_closed_root_represented:
  assumes X: "Elem X (pp_t_domain pp_t_first_cyclic_unary_type)"
    and stock: "pp_t_symmetrized_negation_closed_stock [] X"
  obtains d where
    "d \<in> pp_t_symmetrized_negation_closed_representatives"
    "pp_t_eqv pp_t_first_cyclic_unary_type [] X d"
proof (cases
    "pp_t_closed_logical_stock
      pp_t_first_cyclic_unary_type [] X")
  case True
  then obtain M where typed:
      "[] \<turnstile> M : pp_t_first_cyclic_unary_type"
    and logical: "pp_logical_vocabulary M"
    and XM:
      "pp_t_eqv pp_t_first_cyclic_unary_type []
        X (pp_t_closed_den M)"
    unfolding pp_t_closed_logical_stock_def by blast
  have member:
      "pp_t_closed_den M
        \<in> pp_t_symmetrized_negation_closed_representatives"
    unfolding
      pp_t_symmetrized_negation_closed_representatives_def
      pp_t_exact_closed_logical_operators_def
    using typed logical by blast
  show ?thesis
    using that[OF member XM] .
next
  case False
  then have added:
      "pp_t_eqv pp_t_first_cyclic_unary_type []
          pp_t_symmetrized_closed_stock_probe X
      \<or>
      pp_t_eqv pp_t_first_cyclic_unary_type []
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe) X"
    using stock
    unfolding pp_t_symmetrized_negation_closed_stock_def
    by blast
  then show ?thesis
  proof
    assume PX:
        "pp_t_eqv pp_t_first_cyclic_unary_type []
          pp_t_symmetrized_closed_stock_probe X"
    have XP:
        "pp_t_eqv pp_t_first_cyclic_unary_type [] X
          pp_t_symmetrized_closed_stock_probe"
      using pp_t_eqv_symmetric[
        OF pp_t_symmetrized_closed_stock_probe_in_domain X PX] .
    have member:
        "pp_t_symmetrized_closed_stock_probe
          \<in> pp_t_symmetrized_negation_closed_representatives"
      unfolding
        pp_t_symmetrized_negation_closed_representatives_def
      by simp
    show ?thesis
      using that[OF member XP] .
  next
    assume cPX:
        "pp_t_eqv pp_t_first_cyclic_unary_type []
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe) X"
    have cP_domain:
        "Elem
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe)
          (pp_t_domain pp_t_first_cyclic_unary_type)"
      using pp_t_unary_complement_in_domain[
        OF pp_t_symmetrized_closed_stock_probe_in_domain] .
    have XP:
        "pp_t_eqv pp_t_first_cyclic_unary_type [] X
          (pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe)"
      using pp_t_eqv_symmetric[OF cP_domain X cPX] .
    have member:
        "pp_t_unary_complement
            pp_t_symmetrized_closed_stock_probe
          \<in> pp_t_symmetrized_negation_closed_representatives"
      unfolding
        pp_t_symmetrized_negation_closed_representatives_def
      by simp
    show ?thesis
      using that[OF member XP] .
  qed
qed

theorem pp_t_symmetrized_negation_closed_root_seed_exists:
  "\<exists>r. Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_symmetrized_negation_closed_stock r []"
proof (rule pp_t_countably_represented_unary_stock_root_seed_exists[
    where
      D=pp_t_symmetrized_negation_closed_representatives])
  show "countable
      pp_t_symmetrized_negation_closed_representatives"
    by (rule
      pp_t_symmetrized_negation_closed_representatives_countable)
  show "\<And>d.
      d \<in> pp_t_symmetrized_negation_closed_representatives
      \<Longrightarrow>
      Elem d (pp_t_domain pp_t_one_context_unary_type)"
    by (rule
      pp_t_symmetrized_negation_closed_representative_in_domain)
  show "\<And>d.
      d \<in> pp_t_symmetrized_negation_closed_representatives
      \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    by (rule
      pp_t_symmetrized_negation_closed_representative_equivariant)
  show "\<And>X.
      Elem X (pp_t_domain pp_t_one_context_unary_type)
      \<Longrightarrow>
      pp_t_symmetrized_negation_closed_stock [] X
      \<Longrightarrow>
      \<exists>d \<in> pp_t_symmetrized_negation_closed_representatives.
        pp_t_eqv pp_t_one_context_unary_type [] X d"
    using pp_t_symmetrized_negation_closed_root_represented
    by blast
qed

definition pp_t_symmetrized_negation_closed_root_seed :: ZF where
  "pp_t_symmetrized_negation_closed_root_seed =
    (SOME r. Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_symmetrized_negation_closed_stock r [])"

lemma pp_t_symmetrized_negation_closed_root_seed_spec:
  "Elem pp_t_symmetrized_negation_closed_root_seed
      (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_symmetrized_negation_closed_stock
      pp_t_symmetrized_negation_closed_root_seed []"
  unfolding pp_t_symmetrized_negation_closed_root_seed_def
  using someI_ex[
    OF pp_t_symmetrized_negation_closed_root_seed_exists] .

definition pp_t_symmetrized_negation_closed_seed_at ::
    "bool list \<Rightarrow> ZF"
where
  "pp_t_symmetrized_negation_closed_seed_at w =
    pp_t_cone_lift w
      pp_t_symmetrized_negation_closed_root_seed"

lemma pp_t_symmetrized_negation_closed_seed_at_in_domain:
  "Elem (pp_t_symmetrized_negation_closed_seed_at w)
    (pp_t_domain Prop)"
  unfolding pp_t_symmetrized_negation_closed_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem
  pp_t_symmetrized_negation_closed_seed_recombines_at_every_world:
  "pp_t_unary_recombines_at
    pp_t_symmetrized_negation_closed_stock
    (pp_t_symmetrized_negation_closed_seed_at w) w"
  unfolding pp_t_symmetrized_negation_closed_seed_at_def
  by (rule
    pp_t_unary_stock_root_recombination_transports_to_cone[
      OF
        pp_t_symmetrized_negation_closed_root_seed_spec[
          THEN conjunct1]
        pp_t_symmetrized_negation_closed_root_seed_spec[
          THEN conjunct2]
        pp_t_symmetrized_negation_closed_stock_cone_iff])

definition pp_finite_next_cyclic_package :: "oterm set" where
  "pp_finite_next_cyclic_package =
    pp_recombination_fixed_axioms
    \<union> {
      pp_pure pp_t_first_cyclic_builder_type
        pp_t_next_classifier_cycle_builder,
      pp_application_closure
        pp_t_first_cyclic_classifier_type
        pp_t_first_cyclic_unary_type}"

lemma pp_finite_next_cyclic_package_finite:
  "finite pp_finite_next_cyclic_package"
  unfolding pp_finite_next_cyclic_package_def
    pp_recombination_fixed_axioms_def
  by simp

lemma pp_finite_next_cyclic_package_subset:
  "pp_finite_next_cyclic_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have purity:
      "pp_pure pp_t_first_cyclic_builder_type
        pp_t_next_classifier_cycle_builder
      \<in> pp_purity_schema"
    using pp_t_next_classifier_cycle_builder_typed
      pp_t_next_classifier_cycle_builder_logical
    unfolding pp_purity_schema_def by blast
  have application:
      "pp_application_closure
        pp_t_first_cyclic_classifier_type
        pp_t_first_cyclic_unary_type
      \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  show ?thesis
    using purity application
    unfolding pp_finite_next_cyclic_package_def
      pp_recombination_fixed_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

lemma pp_finite_next_cyclic_pair_extracted:
  "(pp_finite_classifier_type, pp_finite_unary_type)
    \<in> pp_fragment_application_pairs
      pp_finite_next_cyclic_package"
proof -
  let ?A =
      "pp_application_closure
        pp_finite_classifier_type
        pp_finite_unary_type"
  have A_package: "?A \<in> pp_finite_next_cyclic_package"
    unfolding pp_finite_next_cyclic_package_def by simp
  have A_schema: "?A \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def by blast
  let ?p = "pp_application_pair_of ?A"
  have p_in:
      "?p \<in> pp_fragment_application_pairs
        pp_finite_next_cyclic_package"
    using A_package A_schema
    unfolding pp_fragment_application_pairs_def by blast
  have equation:
      "?A = pp_application_closure (fst ?p) (snd ?p)"
    using pp_application_pair_of_correct[OF A_schema] .
  have pair:
      "?p = (pp_finite_classifier_type, pp_finite_unary_type)"
    using pp_application_closure_pair_injective[OF equation]
    by (cases ?p) simp
  show ?thesis
    using p_in unfolding pair .
qed

theorem pp_finite_next_package_has_classifier_cycle:
  "\<not> pp_fragment_classifier_acyclic
    pp_finite_next_cyclic_package"
proof -
  have pair:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> pp_fragment_application_pairs
          pp_finite_next_cyclic_package"
    by (rule pp_finite_next_cyclic_pair_extracted)
  have edge:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> pp_finite_application_dependency
          (pp_fragment_application_pairs
            pp_finite_next_cyclic_package)"
    using pair by (rule pp_finite_application_dependency_argument)
  have path:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> (pp_finite_application_dependency
          (pp_fragment_application_pairs
            pp_finite_next_cyclic_package))\<^sup>*"
    using edge by (rule r_into_rtrancl)
  show ?thesis
    using path
    unfolding pp_fragment_classifier_acyclic_def
      pp_finite_classifier_acyclic_def
    by blast
qed

theorem pp_t_next_classifier_cycle_classification:
  "finite pp_finite_next_cyclic_package
    \<and> pp_finite_next_cyclic_package
      \<subseteq> pp_recombination_PP_axioms
    \<and> \<not> pp_fragment_classifier_acyclic
      pp_finite_next_cyclic_package
    \<and> pp_finite_component pp_finite_first_classifier_cycle
        pp_finite_unary_type
      = {pp_finite_unary_type, pp_finite_classifier_type}
    \<and>
      (pp_finite_classifier_type \<rightarrow>\<^sub>o pp_finite_unary_type,
        pp_finite_unary_type)
      \<in> pp_finite_component_precedes
        pp_finite_first_classifier_cycle
    \<and> \<not> pp_t_family_cycle_elimination_covered
      pp_t_symmetrized_singleton_family_builder"
  using pp_finite_next_cyclic_package_finite
    pp_finite_next_cyclic_package_subset
    pp_finite_next_package_has_classifier_cycle
    pp_finite_first_classifier_component
    pp_finite_first_builder_component_precedes
    pp_t_symmetrized_singleton_cycle_not_elimination_covered
  by blast

text \<open>
  This theorem identifies the next explicit cyclic obligation, not an
  inconsistency.  The symmetrized-singleton family is a closed logical
  family, but it is not view-complete.  Hence the singleton-family inverse
  argument and its view-complete generalization do not show that the forced
  value above belongs to the old unary stock.  The next model step is to
  decide that membership by another argument or to enlarge the unary stock
  by this value and test stabilization of the resulting component.
\<close>

section \<open>The stabilized symmetrized-singleton model\<close>

definition pp_t_symmetrized_builder_den :: ZF where
  "pp_t_symmetrized_builder_den =
    pp_t_closed_den pp_t_next_classifier_cycle_builder"

lemma pp_t_symmetrized_builder_den_in_domain:
  "Elem pp_t_symmetrized_builder_den
    (pp_t_domain pp_t_first_cyclic_builder_type)"
  unfolding pp_t_symmetrized_builder_den_def
  using pp_t_closed_den_in_domain[
    OF pp_t_next_classifier_cycle_builder_typed] .

definition pp_t_complemented_symmetrized_builder_den :: ZF where
  "pp_t_complemented_symmetrized_builder_den =
    pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_complemented_symmetrized_singleton_family_builder)"

lemma pp_t_complemented_symmetrized_builder_den_in_domain:
  "Elem pp_t_complemented_symmetrized_builder_den
    (pp_t_domain pp_t_first_cyclic_builder_type)"
  unfolding pp_t_complemented_symmetrized_builder_den_def
  using pp_t_closed_den_in_domain[
    OF pp_t_family_probe_builder_typed[
      OF
      pp_t_complemented_symmetrized_singleton_family_builder_typed]]
    .

definition pp_t_symmetrized_negation_closed_classifier :: ZF where
  "pp_t_symmetrized_negation_closed_classifier =
    pp_t_classifier pp_t_first_cyclic_unary_type
      pp_t_symmetrized_negation_closed_stock"

lemma pp_t_symmetrized_negation_closed_classifier_in_domain:
  "Elem pp_t_symmetrized_negation_closed_classifier
    (pp_t_domain pp_t_first_cyclic_classifier_type)"
  unfolding pp_t_symmetrized_negation_closed_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule
      pp_t_symmetrized_negation_closed_stock_admissible)

definition pp_t_unary_output_negator_den :: ZF where
  "pp_t_unary_output_negator_den =
    pp_t_closed_den pp_t_unary_output_negator"

lemma pp_t_unary_output_negator_den_in_domain:
  "Elem pp_t_unary_output_negator_den
    (pp_t_domain
      (pp_t_first_cyclic_unary_type
        \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type))"
  unfolding pp_t_unary_output_negator_den_def
  by (rule pp_t_closed_den_in_domain)
    (rule pp_t_unary_output_negator_typed)

definition pp_t_symmetrized_model_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_symmetrized_model_pure \<sigma> w x \<longleftrightarrow>
    (\<sigma> = pp_t_first_cyclic_unary_type
      \<and> pp_t_symmetrized_negation_closed_stock w x)
    \<or>
    (\<sigma> = pp_t_first_cyclic_classifier_type
      \<and> pp_t_eqv pp_t_first_cyclic_classifier_type w
        pp_t_symmetrized_negation_closed_classifier x)
    \<or>
    (\<sigma> = pp_t_first_cyclic_builder_type
      \<and>
        (pp_t_eqv pp_t_first_cyclic_builder_type w
          pp_t_symmetrized_builder_den x
        \<or>
        pp_t_eqv pp_t_first_cyclic_builder_type w
          pp_t_complemented_symmetrized_builder_den x))
    \<or>
    (\<sigma> =
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
      \<and> pp_t_eqv
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
        w pp_t_unary_output_negator_den x)"

lemma pp_t_symmetrized_model_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_symmetrized_model_pure \<sigma>)"
proof -
  have unary:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_unary_type
        pp_t_symmetrized_negation_closed_stock"
    by (rule
      pp_t_symmetrized_negation_closed_stock_admissible)
  have classifier:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_first_cyclic_classifier_type w
          pp_t_symmetrized_negation_closed_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_symmetrized_negation_closed_classifier_in_domain] .
  have builder:
      "pp_t_predicate_admissible
        pp_t_first_cyclic_builder_type
        (\<lambda>w x.
          pp_t_eqv pp_t_first_cyclic_builder_type w
            pp_t_symmetrized_builder_den x
          \<or>
          pp_t_eqv pp_t_first_cyclic_builder_type w
            pp_t_complemented_symmetrized_builder_den x)"
  proof -
    have first:
        "pp_t_predicate_admissible
          pp_t_first_cyclic_builder_type
          (\<lambda>w x. pp_t_eqv pp_t_first_cyclic_builder_type w
            pp_t_symmetrized_builder_den x)"
      using pp_t_eqv_classifier_admissible[
        OF pp_t_symmetrized_builder_den_in_domain] .
    have second:
        "pp_t_predicate_admissible
          pp_t_first_cyclic_builder_type
          (\<lambda>w x. pp_t_eqv pp_t_first_cyclic_builder_type w
            pp_t_complemented_symmetrized_builder_den x)"
      using pp_t_eqv_classifier_admissible[
        OF
          pp_t_complemented_symmetrized_builder_den_in_domain] .
    show ?thesis
      using first second
      unfolding pp_t_predicate_admissible_def
      by blast
  qed
  have negator:
      "pp_t_predicate_admissible
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
        (\<lambda>w x. pp_t_eqv
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
          w pp_t_unary_output_negator_den x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_unary_output_negator_den_in_domain] .
  show ?thesis
    using unary classifier builder negator
    unfolding pp_t_predicate_admissible_def
      pp_t_symmetrized_model_pure_def
    by blast
qed

lemma pp_t_symmetrized_model_pure_unary:
  "pp_t_symmetrized_model_pure
      pp_t_first_cyclic_unary_type w x
    \<longleftrightarrow>
    pp_t_symmetrized_negation_closed_stock w x"
  by (simp add: pp_t_symmetrized_model_pure_def)

lemma pp_t_symmetrized_model_pure_classifier:
  "pp_t_symmetrized_model_pure
      pp_t_first_cyclic_classifier_type w x
    \<longleftrightarrow>
    pp_t_eqv pp_t_first_cyclic_classifier_type w
      pp_t_symmetrized_negation_closed_classifier x"
  by (simp add: pp_t_symmetrized_model_pure_def)

lemma pp_t_symmetrized_model_pure_builder:
  "pp_t_symmetrized_model_pure
      pp_t_first_cyclic_builder_type w x
    \<longleftrightarrow>
    (pp_t_eqv pp_t_first_cyclic_builder_type w
      pp_t_symmetrized_builder_den x
    \<or>
    pp_t_eqv pp_t_first_cyclic_builder_type w
      pp_t_complemented_symmetrized_builder_den x)"
  by (simp add: pp_t_symmetrized_model_pure_def)

lemma pp_t_symmetrized_model_pure_output_negator:
  "pp_t_symmetrized_model_pure
      (pp_t_first_cyclic_unary_type
        \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w x
    \<longleftrightarrow>
    pp_t_eqv
      (pp_t_first_cyclic_unary_type
        \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
      w pp_t_unary_output_negator_den x"
  by (simp add: pp_t_symmetrized_model_pure_def)

definition pp_t_symmetrized_model_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_symmetrized_model_constants =
    pp_t_seeded_internal_constants
      pp_t_symmetrized_model_pure
      pp_t_symmetrized_negation_closed_seed_at"

lemma pp_t_symmetrized_seeded_fundamental_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_seeded_fundamental_at
      pp_t_symmetrized_negation_closed_seed_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain Prop)"
      and y: "Elem y (pp_t_domain Prop)"
      and xy: "pp_t_eqv Prop w x y"
      and wv: "prefix w v"
    have xy_v: "pp_t_eqv Prop v x y"
      using pp_t_eqv_persistent[OF xy wv] .
    have seed:
        "Elem (pp_t_symmetrized_negation_closed_seed_at v)
          (pp_t_domain Prop)"
      by (rule
        pp_t_symmetrized_negation_closed_seed_at_in_domain)
    have refl:
        "pp_t_eqv Prop v
          (pp_t_symmetrized_negation_closed_seed_at v)
          (pp_t_symmetrized_negation_closed_seed_at v)"
      using pp_t_eqv_reflexive[OF seed] .
    show "pp_t_seeded_fundamental_at
          pp_t_symmetrized_negation_closed_seed_at Prop v x =
        pp_t_seeded_fundamental_at
          pp_t_symmetrized_negation_closed_seed_at Prop v y"
      using pp_t_eqv_congruence[
        OF x y seed seed xy_v refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
qed

interpretation SymmetrizedModelConstants:
  pp_t_constants pp_t_symmetrized_model_constants
proof
  fix c \<sigma>
  show "Elem (pp_t_symmetrized_model_constants c \<sigma>)
      (pp_t_domain \<sigma>)"
  proof (cases \<sigma>)
    case Ind
    then show ?thesis
      unfolding pp_t_symmetrized_model_constants_def
      using pp_t_default_in_domain[of Ind] by simp
  next
    case Prop
    then show ?thesis
      unfolding pp_t_symmetrized_model_constants_def
      using pp_t_default_in_domain[of Prop] by simp
  next
    case (Arr \<sigma> \<tau>)
    have pure_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_symmetrized_model_pure \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF pp_t_symmetrized_model_pure_admissible] .
    have fun_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_seeded_fundamental_at
              pp_t_symmetrized_negation_closed_seed_at \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF pp_t_symmetrized_seeded_fundamental_admissible] .
    have default:
        "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using pp_t_default_in_domain .
    show ?thesis
      using Arr pure_classifier fun_classifier default
      by (auto simp: pp_t_symmetrized_model_constants_def
          pp_t_seeded_fundamental_at.simps)
  qed
qed

lemma pp_t_symmetrized_model_eval_Pure[simp]:
  "pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma> (pp_t_symmetrized_model_pure \<sigma>)"
  by (simp add: pp_t_symmetrized_model_constants_def
      pp_Pure_def pp_pure_name_def)

lemma pp_t_symmetrized_model_eval_Fun[simp]:
  "pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at
        pp_t_symmetrized_negation_closed_seed_at \<sigma>)"
  by (simp add: pp_t_symmetrized_model_constants_def
      pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_symmetrized_model_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_symmetrized_model_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
    pp_t_symmetrized_model_pure \<sigma> w
      (pp_t_eval pp_t_symmetrized_model_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_symmetrized_model_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using SymmetrizedModelConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument, of "pp_t_symmetrized_model_pure \<sigma>" w]
    by simp
qed

lemma pp_t_symmetrized_model_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_symmetrized_model_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
    pp_t_seeded_fundamental_at
      pp_t_symmetrized_negation_closed_seed_at \<sigma> w
      (pp_t_eval pp_t_symmetrized_model_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_symmetrized_model_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using SymmetrizedModelConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at
        pp_t_symmetrized_negation_closed_seed_at \<sigma>" w]
    by simp
qed

lemma pp_t_symmetrized_model_unary_classifier:
  "pp_t_classifier pp_t_first_cyclic_unary_type
      (pp_t_symmetrized_model_pure
        pp_t_first_cyclic_unary_type)
    = pp_t_symmetrized_negation_closed_classifier"
  unfolding pp_t_symmetrized_negation_closed_classifier_def
    pp_t_symmetrized_model_pure_def
  by simp

lemma pp_t_symmetrized_model_classifier_is_pure:
  "pp_t_symmetrized_model_pure
    pp_t_first_cyclic_classifier_type w
    pp_t_symmetrized_negation_closed_classifier"
  apply (rule pp_t_symmetrized_model_pure_classifier[THEN iffD2])
  using pp_t_eqv_reflexive[
    OF pp_t_symmetrized_negation_closed_classifier_in_domain] .

lemma pp_t_symmetrized_model_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      pp_target_PP) w"
proof -
  have evaluation:
      "pp_t_eval pp_t_symmetrized_model_constants \<rho> pp_target_PP =
        pp_t_classifier pp_t_first_cyclic_classifier_type
          (pp_t_symmetrized_model_pure
            pp_t_first_cyclic_classifier_type)
        \<acute> pp_t_symmetrized_negation_closed_classifier"
    unfolding pp_target_PP_def pp_purity_of_pure_def pp_pure_def
    by (simp add: pp_t_symmetrized_model_unary_classifier)
  have at_classifier:
      "pp_t_holds
        (pp_t_classifier pp_t_first_cyclic_classifier_type
          (pp_t_symmetrized_model_pure
            pp_t_first_cyclic_classifier_type)
          \<acute> pp_t_symmetrized_negation_closed_classifier) w
      \<longleftrightarrow>
      pp_t_symmetrized_model_pure
        pp_t_first_cyclic_classifier_type w
        pp_t_symmetrized_negation_closed_classifier"
    using pp_t_classifier_holds[
      OF pp_t_symmetrized_negation_closed_classifier_in_domain,
      of "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_classifier_type" w] .
  show ?thesis
    unfolding evaluation
    using at_classifier pp_t_symmetrized_model_classifier_is_pure
    by blast
qed

theorem pp_t_symmetrized_model_target_PP_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma> pp_target_PP"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using pp_t_symmetrized_model_target_PP_holds by blast

lemma pp_t_symmetrized_model_builder_eval_eqv:
  "pp_t_eqv pp_t_first_cyclic_builder_type w
    pp_t_symmetrized_builder_den
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      pp_t_next_classifier_cycle_builder)"
proof -
  have const_free:
      "consts_of pp_t_next_classifier_cycle_builder = {}"
    using pp_t_next_classifier_cycle_builder_logical
    unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval pp_t_symmetrized_model_constants \<rho>
          pp_t_next_classifier_cycle_builder =
        pp_t_eval pp_t_default_constants \<rho>
          pp_t_next_classifier_cycle_builder"
    using pp_t_eval_const_free[OF const_free] .
  have eval_domain:
      "Elem
        (pp_t_eval pp_t_default_constants \<rho>
          pp_t_next_classifier_cycle_builder)
        (pp_t_domain pp_t_first_cyclic_builder_type)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF pp_t_next_classifier_cycle_builder_typed
        pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have closed_domain:
      "Elem
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_t_next_classifier_cycle_builder)
        (pp_t_domain pp_t_first_cyclic_builder_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_next_classifier_cycle_builder_typed]
    unfolding pp_t_closed_den_def .
  have forward:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_default_constants \<rho>
          pp_t_next_classifier_cycle_builder)
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_t_next_classifier_cycle_builder)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF pp_t_next_classifier_cycle_builder_typed
        pp_t_empty_env_eqv] .
  have related:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_default_constants pp_t_closed_env
          pp_t_next_classifier_cycle_builder)
        (pp_t_eval pp_t_default_constants \<rho>
          pp_t_next_classifier_cycle_builder)"
    using pp_t_eqv_symmetric[
      OF eval_domain closed_domain forward] .
  show ?thesis
    unfolding pp_t_symmetrized_builder_den_def pp_t_closed_den_def
    using related change_constants by simp
qed

lemma pp_t_symmetrized_model_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_pure pp_t_first_cyclic_builder_type
        pp_t_next_classifier_cycle_builder)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          (pp_pure pp_t_first_cyclic_builder_type
            pp_t_next_classifier_cycle_builder)) w
      \<longleftrightarrow>
      pp_t_symmetrized_model_pure
        pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          pp_t_next_classifier_cycle_builder)"
    using pp_t_symmetrized_model_eval_pure_holds[
      OF pp_t_next_classifier_cycle_builder_typed env, of w] .
  have pure:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          pp_t_next_classifier_cycle_builder)"
    apply (rule pp_t_symmetrized_model_pure_builder[THEN iffD2])
    apply (rule disjI1)
    by (rule pp_t_symmetrized_model_builder_eval_eqv)
  show ?thesis
    using evaluation pure by blast
qed

theorem pp_t_symmetrized_model_builder_purity_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_first_cyclic_builder_type
      pp_t_next_classifier_cycle_builder)"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using pp_t_symmetrized_model_builder_purity_holds by blast

lemma pp_t_symmetrized_model_closed_logical_eval_eqv:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_eqv \<sigma> w
    (pp_t_closed_den M)
    (pp_t_eval pp_t_symmetrized_model_constants \<rho> M)"
proof -
  have const_free: "consts_of M = {}"
    using logical unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval pp_t_symmetrized_model_constants \<rho> M =
        pp_t_eval pp_t_default_constants \<rho> M"
    using pp_t_eval_const_free[OF const_free] .
  have eval_domain:
      "Elem (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using DefaultTreeConstants.pp_t_eval_type[
      OF typed pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have closed_domain:
      "Elem
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)
        (pp_t_domain \<sigma>)"
    using pp_t_closed_den_in_domain[OF typed]
    unfolding pp_t_closed_den_def .
  have forward:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF typed pp_t_empty_env_eqv] .
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)
        (pp_t_eval pp_t_default_constants \<rho> M)"
    using pp_t_eqv_symmetric[
      OF eval_domain closed_domain forward] .
  show ?thesis
    unfolding pp_t_closed_den_def
    using related change_constants by simp
qed

lemma pp_t_symmetrized_model_complemented_builder_eval_eqv:
  "pp_t_eqv pp_t_first_cyclic_builder_type w
    pp_t_complemented_symmetrized_builder_den
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_t_family_probe_builder
        pp_t_complemented_symmetrized_singleton_family_builder))"
  unfolding pp_t_complemented_symmetrized_builder_den_def
  using pp_t_symmetrized_model_closed_logical_eval_eqv[
    OF pp_t_family_probe_builder_typed[
        OF
          pp_t_complemented_symmetrized_singleton_family_builder_typed]
      pp_t_family_probe_builder_logical[
        OF
          pp_t_complemented_symmetrized_singleton_family_builder_logical]]
    .

lemma pp_t_symmetrized_model_complemented_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_pure pp_t_first_cyclic_builder_type
        (pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder))) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have builder_typed:
      "[] \<turnstile>
        pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder :
        pp_t_first_cyclic_builder_type"
    using pp_t_family_probe_builder_typed[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed]
    .
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          (pp_pure pp_t_first_cyclic_builder_type
            (pp_t_family_probe_builder
              pp_t_complemented_symmetrized_singleton_family_builder))) w
      \<longleftrightarrow>
      pp_t_symmetrized_model_pure
        pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder))"
    using pp_t_symmetrized_model_eval_pure_holds[
      OF builder_typed env, of w] .
  have pure:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_builder_type w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          (pp_t_family_probe_builder
            pp_t_complemented_symmetrized_singleton_family_builder))"
    apply (rule pp_t_symmetrized_model_pure_builder[THEN iffD2])
    apply (rule disjI2)
    by (rule
      pp_t_symmetrized_model_complemented_builder_eval_eqv)
  show ?thesis
    using evaluation pure by blast
qed

theorem pp_t_symmetrized_model_complemented_builder_purity_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_first_cyclic_builder_type
      (pp_t_family_probe_builder
        pp_t_complemented_symmetrized_singleton_family_builder))"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using
    pp_t_symmetrized_model_complemented_builder_purity_holds
  by blast

lemma pp_t_symmetrized_model_output_negator_eval_eqv:
  "pp_t_eqv
    (pp_t_first_cyclic_unary_type
      \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w
    pp_t_unary_output_negator_den
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      pp_t_unary_output_negator)"
  unfolding pp_t_unary_output_negator_den_def
  using pp_t_symmetrized_model_closed_logical_eval_eqv[
    OF pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical] .

lemma pp_t_symmetrized_model_output_negator_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_pure
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
        pp_t_unary_output_negator)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have evaluation:
      "pp_t_holds
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          (pp_pure
            (pp_t_first_cyclic_unary_type
              \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
            pp_t_unary_output_negator)) w
      \<longleftrightarrow>
      pp_t_symmetrized_model_pure
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          pp_t_unary_output_negator)"
    using pp_t_symmetrized_model_eval_pure_holds[
      OF pp_t_unary_output_negator_typed env, of w] .
  have pure:
      "pp_t_symmetrized_model_pure
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w
        (pp_t_eval pp_t_symmetrized_model_constants \<rho>
          pp_t_unary_output_negator)"
    apply (rule
      pp_t_symmetrized_model_pure_output_negator[THEN iffD2])
    by (rule pp_t_symmetrized_model_output_negator_eval_eqv)
  show ?thesis
    using evaluation pure by blast
qed

theorem pp_t_symmetrized_model_output_negator_purity_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure
      (pp_t_first_cyclic_unary_type
        \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
      pp_t_unary_output_negator)"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using
    pp_t_symmetrized_model_output_negator_purity_holds
  by blast

lemma pp_t_complemented_symmetrized_probe_eq_forced_value:
  "pp_t_family_probe_for_stock
      (pp_t_closed_logical_stock pp_t_first_cyclic_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_next_classifier_cycle_forced_value"
proof -
  have symmetrized:
      "pp_t_family_probe_for_stock
          (pp_t_closed_logical_stock pp_t_first_cyclic_unary_type)
          pp_t_symmetrized_singleton_family_builder
        =
        pp_t_next_classifier_cycle_forced_value"
    unfolding pp_t_family_probe_for_stock_def
      pp_t_next_classifier_cycle_forced_value_def
      pp_t_family_probe_def
      pp_t_old_unary_stock_classifier_def
    by simp
  show ?thesis
    using
      pp_t_complemented_symmetrized_probe_eq_symmetrized_probe
      symmetrized by simp
qed

lemma
  pp_t_complemented_probe_enlargement_eq_symmetrized_stock:
  "pp_t_family_probe_stock_enlargement
      (pp_t_closed_logical_stock pp_t_first_cyclic_unary_type)
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_symmetrized_enlarged_unary_stock"
  unfolding pp_t_family_probe_stock_enlargement_def
    pp_t_symmetrized_enlarged_unary_stock_def
    pp_t_complemented_symmetrized_probe_eq_forced_value
  by simp

lemma pp_t_complemented_symmetrized_builder_stable:
  "pp_t_complemented_symmetrized_builder_den
      \<acute> pp_t_symmetrized_negation_closed_classifier
    =
    pp_t_next_classifier_cycle_forced_value"
proof -
  have reevaluated:
      "pp_t_complemented_symmetrized_builder_den
          \<acute> pp_t_symmetrized_negation_closed_classifier
        =
        pp_t_family_probe_for_stock
          pp_t_symmetrized_negation_closed_stock
          pp_t_complemented_symmetrized_singleton_family_builder"
    unfolding pp_t_complemented_symmetrized_builder_den_def
      pp_t_symmetrized_negation_closed_classifier_def
      pp_t_family_probe_for_stock_def
    by simp
  have stable:
      "pp_t_family_probe_for_stock
          pp_t_symmetrized_negation_closed_stock
          pp_t_complemented_symmetrized_singleton_family_builder
        =
        pp_t_symmetrized_closed_stock_probe"
    by (rule
      pp_t_complemented_probe_stable_under_negation_closure)
  show ?thesis
    using reevaluated stable
      pp_t_symmetrized_closed_stock_probe_eq_forced_value
    by simp
qed

lemma pp_t_symmetrized_model_application_absorbed:
  assumes f: "Elem f (pp_t_domain pp_t_first_cyclic_builder_type)"
    and x: "Elem x (pp_t_domain pp_t_first_cyclic_classifier_type)"
    and pure_f:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_builder_type w f"
    and pure_x:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_classifier_type w x"
  shows "pp_t_symmetrized_model_pure
    pp_t_first_cyclic_unary_type w (f \<acute> x)"
proof -
  have f_eqv:
      "pp_t_eqv pp_t_first_cyclic_builder_type w
        pp_t_symmetrized_builder_den f
      \<or>
      pp_t_eqv pp_t_first_cyclic_builder_type w
        pp_t_complemented_symmetrized_builder_den f"
    using pure_f
    by (rule pp_t_symmetrized_model_pure_builder[THEN iffD1])
  have x_eqv:
      "pp_t_eqv pp_t_first_cyclic_classifier_type w
        pp_t_symmetrized_negation_closed_classifier x"
    using pure_x
    by (rule pp_t_symmetrized_model_pure_classifier[THEN iffD1])
  have stable:
      "pp_t_symmetrized_builder_den
          \<acute> pp_t_symmetrized_negation_closed_classifier =
        pp_t_next_classifier_cycle_forced_value"
  proof -
    have identity:
        "pp_t_symmetrized_builder_den
            \<acute> pp_t_symmetrized_negation_closed_classifier =
          pp_t_family_probe_for_stock
            pp_t_symmetrized_negation_closed_stock
            pp_t_symmetrized_singleton_family_builder"
      unfolding pp_t_symmetrized_builder_den_def
        pp_t_next_classifier_cycle_builder_def
        pp_t_symmetrized_negation_closed_classifier_def
        pp_t_family_probe_for_stock_def
      by simp
    show ?thesis
      using identity
        pp_t_symmetrized_probe_stable_under_negation_closure
        pp_t_symmetrized_closed_stock_probe_eq_forced_value
      by simp
  qed
  have output_eqv:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        pp_t_next_classifier_cycle_forced_value
        (f \<acute> x)"
  using f_eqv
  proof
    assume first:
        "pp_t_eqv pp_t_first_cyclic_builder_type w
          pp_t_symmetrized_builder_den f"
    have related:
        "pp_t_eqv pp_t_first_cyclic_unary_type w
          (pp_t_symmetrized_builder_den
            \<acute> pp_t_symmetrized_negation_closed_classifier)
          (f \<acute> x)"
      using pp_t_app_respects[
        OF first
          pp_t_symmetrized_negation_closed_classifier_in_domain
          x x_eqv] .
    show ?thesis
      using related unfolding stable .
  next
    assume second:
        "pp_t_eqv pp_t_first_cyclic_builder_type w
          pp_t_complemented_symmetrized_builder_den f"
    have related:
        "pp_t_eqv pp_t_first_cyclic_unary_type w
          (pp_t_complemented_symmetrized_builder_den
            \<acute> pp_t_symmetrized_negation_closed_classifier)
          (f \<acute> x)"
      using pp_t_app_respects[
        OF second
          pp_t_symmetrized_negation_closed_classifier_in_domain
          x x_eqv] .
    show ?thesis
      using related
      unfolding pp_t_complemented_symmetrized_builder_stable .
  qed
  have probe_stock:
      "pp_t_symmetrized_negation_closed_stock w
        pp_t_next_classifier_cycle_forced_value"
    unfolding pp_t_symmetrized_negation_closed_stock_def
      pp_t_symmetrized_closed_stock_probe_eq_forced_value
    using pp_t_eqv_reflexive[
      OF pp_t_next_classifier_cycle_forced_value_in_domain]
    by blast
  have output_stock:
      "pp_t_symmetrized_negation_closed_stock w (f \<acute> x)"
    using pp_t_symmetrized_negation_closed_stock_admissible
      probe_stock output_eqv
      pp_t_next_classifier_cycle_forced_value_in_domain
      pp_t_app_closed[OF f x]
    unfolding pp_t_predicate_admissible_def
    by blast
  show ?thesis
    using output_stock
    by (rule pp_t_symmetrized_model_pure_unary[THEN iffD2])
qed

lemma pp_t_symmetrized_model_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_symmetrized_model_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_symmetrized_model_pure
            (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
          \<and> pp_t_symmetrized_model_pure \<sigma> w x
        \<longrightarrow>
        pp_t_symmetrized_model_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_symmetrized_model_application_closure_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_first_cyclic_classifier_type
      pp_t_first_cyclic_unary_type)"
proof (rule SymmetrizedModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (SymmetrizedModelConstants.pp_t_den
        (pp_application_closure
          pp_t_first_cyclic_classifier_type
          pp_t_first_cyclic_unary_type) env) w"
    unfolding SymmetrizedModelConstants.pp_t_den_def
      pp_t_symmetrized_model_application_closure_holds_iff
    using pp_t_symmetrized_model_application_absorbed by blast
qed

lemma pp_t_symmetrized_model_output_negator_application_absorbed:
  assumes f:
      "Elem f
        (pp_t_domain
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type))"
    and x:
      "Elem x (pp_t_domain pp_t_first_cyclic_unary_type)"
    and pure_f:
      "pp_t_symmetrized_model_pure
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w f"
    and pure_x:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_unary_type w x"
  shows "pp_t_symmetrized_model_pure
    pp_t_first_cyclic_unary_type w (f \<acute> x)"
proof -
  have f_eqv:
      "pp_t_eqv
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type) w
        pp_t_unary_output_negator_den f"
    using pure_f
    by (rule
      pp_t_symmetrized_model_pure_output_negator[THEN iffD1])
  have x_stock:
      "pp_t_symmetrized_negation_closed_stock w x"
    using pure_x
    by (rule pp_t_symmetrized_model_pure_unary[THEN iffD1])
  have complement_stock:
      "pp_t_symmetrized_negation_closed_stock w
        (pp_t_unary_complement x)"
    by (rule
      pp_t_symmetrized_negation_closed_stock_complement[
        OF x x_stock])
  have related:
      "pp_t_eqv pp_t_first_cyclic_unary_type w
        (pp_t_unary_complement x) (f \<acute> x)"
  proof -
    have applications:
        "pp_t_eqv pp_t_first_cyclic_unary_type w
          (pp_t_unary_output_negator_den \<acute> x)
          (f \<acute> x)"
      using pp_t_app_respects[
        OF f_eqv x x pp_t_eqv_reflexive[OF x]] .
    show ?thesis
      using applications
      unfolding pp_t_unary_output_negator_den_def
      by (simp only: pp_t_unary_output_negator_apply[OF x])
  qed
  have complement_domain:
      "Elem (pp_t_unary_complement x)
        (pp_t_domain pp_t_first_cyclic_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF x])
  have output_stock:
      "pp_t_symmetrized_negation_closed_stock w (f \<acute> x)"
    using pp_t_symmetrized_negation_closed_stock_admissible
      complement_stock related complement_domain
      pp_t_app_closed[OF f x]
    unfolding pp_t_predicate_admissible_def
    by blast
  show ?thesis
    by (rule pp_t_symmetrized_model_pure_unary[THEN iffD2])
      (rule output_stock)
qed

theorem
  pp_t_symmetrized_model_output_negator_application_closure_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure
      pp_t_first_cyclic_unary_type
      pp_t_first_cyclic_unary_type)"
proof (rule SymmetrizedModelConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (SymmetrizedModelConstants.pp_t_den
        (pp_application_closure
          pp_t_first_cyclic_unary_type
          pp_t_first_cyclic_unary_type) env) w"
    unfolding SymmetrizedModelConstants.pp_t_den_def
      pp_t_symmetrized_model_application_closure_holds_iff
    using
      pp_t_symmetrized_model_output_negator_application_absorbed
    by blast
qed

lemma pp_t_symmetrized_model_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_t_symmetrized_negation_closed_seed_at w"
  have base: "pp_t_env_typed [] \<rho>"
    by (rule pp_t_empty_env_typed)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[
      OF base
        pp_t_symmetrized_negation_closed_seed_at_in_domain] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval pp_t_symmetrized_model_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      using pp_t_eqv_reflexive[
        OF
          pp_t_symmetrized_negation_closed_seed_at_in_domain] .
    show ?thesis
      using pp_t_symmetrized_model_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_symmetrized_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_t_domain Prop)"
    have yr_env:
        "pp_t_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_t_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_symmetrized_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_symmetrized_model_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval pp_t_symmetrized_model_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_symmetrized_model_constants
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_t_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_t_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_t_symmetrized_negation_closed_seed_at_in_domain
      r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

theorem pp_t_symmetrized_model_unique_fundamental_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using pp_t_symmetrized_model_unique_fundamental_holds by blast

lemma pp_t_symmetrized_model_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      pp_zeroary_recombination) w"
  by (simp add: pp_zeroary_recombination_def pp_pure_def
      pp_t_classifier_holds extend_env.simps
      pp_t_symmetrized_model_pure_def)

theorem pp_t_symmetrized_model_zeroary_recombination_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using pp_t_symmetrized_model_zeroary_recombination_holds
  by blast

lemma pp_t_symmetrized_model_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_symmetrized_model_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_first_cyclic_unary_type)
      \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_symmetrized_model_pure
            pp_t_first_cyclic_unary_type w X
          \<and> pp_t_seeded_fundamental_at
            pp_t_symmetrized_negation_closed_seed_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v)
          \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_symmetrized_model_fundamental_recombines:
  assumes X: "Elem X
      (pp_t_domain pp_t_first_cyclic_unary_type)"
    and X_pure:
      "pp_t_symmetrized_model_pure
        pp_t_first_cyclic_unary_type w X"
    and r: "Elem r (pp_t_domain Prop)"
    and r_fundamental:
      "pp_t_seeded_fundamental_at
        pp_t_symmetrized_negation_closed_seed_at Prop w r"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w"
proof -
  let ?seed = "pp_t_symmetrized_negation_closed_seed_at w"
  have seed: "Elem ?seed (pp_t_domain Prop)"
    by (rule
      pp_t_symmetrized_negation_closed_seed_at_in_domain)
  have r_seed: "pp_t_eqv Prop w r ?seed"
    using r_fundamental by simp
  have seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> ?seed) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have related:
        "pp_t_eqv Prop v r ?seed"
      using pp_t_eqv_persistent[OF r_seed wv] .
    have applications:
        "pp_t_eqv Prop v (X \<acute> r) (X \<acute> ?seed)"
      using pp_t_arrow_member_respects[
        OF X r seed related] .
    show "pp_t_holds (X \<acute> ?seed) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        necessary[rule_format, OF wv]
      by simp
  qed
  have X_stock:
      "pp_t_symmetrized_negation_closed_stock w X"
    using X_pure
    by (rule pp_t_symmetrized_model_pure_unary[THEN iffD1])
  show ?thesis
    using
      pp_t_symmetrized_negation_closed_seed_recombines_at_every_world[
      of w] X X_stock seed_necessary
    unfolding pp_t_unary_recombines_at_def by blast
qed

lemma pp_t_symmetrized_model_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_symmetrized_model_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_symmetrized_model_unary_recombination_holds_iff
  using pp_t_symmetrized_model_fundamental_recombines by blast

theorem pp_t_symmetrized_model_unary_recombination_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_def
    SymmetrizedModelConstants.pp_t_den_def
  using pp_t_symmetrized_model_unary_recombination_holds
  by blast

theorem pp_t_symmetrized_model_package_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid_set
    pp_finite_next_cyclic_package"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_finite_next_cyclic_package"
  from A consider
      (target) "A = pp_target_PP"
    | (unique) "A = pp_unique_fundamental Prop"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
    | (builder)
        "A = pp_pure pp_t_first_cyclic_builder_type
          pp_t_next_classifier_cycle_builder"
    | (application)
        "A = pp_application_closure
          pp_t_first_cyclic_classifier_type
          pp_t_first_cyclic_unary_type"
    unfolding pp_finite_next_cyclic_package_def
      pp_recombination_fixed_axioms_def
    by blast
  then show
      "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case target
    then show ?thesis
      using pp_t_symmetrized_model_target_PP_gvalid by simp
  next
    case unique
    then show ?thesis
      using pp_t_symmetrized_model_unique_fundamental_gvalid
      by simp
  next
    case zeroary
    then show ?thesis
      using pp_t_symmetrized_model_zeroary_recombination_gvalid
      by simp
  next
    case unary
    then show ?thesis
      using pp_t_symmetrized_model_unary_recombination_gvalid
      by simp
  next
    case builder
    then show ?thesis
      using pp_t_symmetrized_model_builder_purity_gvalid by simp
  next
    case application
    then show ?thesis
      using pp_t_symmetrized_model_application_closure_gvalid
      by simp
  qed
qed

theorem pp_finite_next_cyclic_package_consistent:
  "CEV_axiom_consistent [] pp_finite_next_cyclic_package"
  using SymmetrizedModelConstants.pp_t_base_sound
    SymmetrizedModelConstants.pp_t_zeta_sound
    pp_t_symmetrized_model_package_gvalid
  by (rule
    SymmetrizedModelConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

section \<open>The joint symmetrized and complemented package\<close>

definition pp_finite_two_family_cyclic_package :: "oterm set" where
  "pp_finite_two_family_cyclic_package =
    pp_finite_next_cyclic_package
    \<union> {
      pp_pure pp_t_first_cyclic_builder_type
        (pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder)}"

lemma pp_finite_two_family_cyclic_package_finite:
  "finite pp_finite_two_family_cyclic_package"
  unfolding pp_finite_two_family_cyclic_package_def
  using pp_finite_next_cyclic_package_finite by simp

lemma pp_finite_two_family_cyclic_package_subset:
  "pp_finite_two_family_cyclic_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have builder_typed:
      "[] \<turnstile>
        pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder :
        pp_t_first_cyclic_builder_type"
    using pp_t_family_probe_builder_typed[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed]
    .
  have builder_logical:
      "pp_logical_vocabulary
        (pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder)"
    using pp_t_family_probe_builder_logical[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_logical]
    .
  have purity:
      "pp_pure pp_t_first_cyclic_builder_type
        (pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder)
      \<in> pp_purity_schema"
    using builder_typed builder_logical
    unfolding pp_purity_schema_def by blast
  show ?thesis
    using pp_finite_next_cyclic_package_subset purity
    unfolding pp_finite_two_family_cyclic_package_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

theorem pp_t_symmetrized_model_two_family_package_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid_set
    pp_finite_two_family_cyclic_package"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_finite_two_family_cyclic_package"
  then have
      "A \<in> pp_finite_next_cyclic_package
      \<or>
      A = pp_pure pp_t_first_cyclic_builder_type
        (pp_t_family_probe_builder
          pp_t_complemented_symmetrized_singleton_family_builder)"
    unfolding pp_finite_two_family_cyclic_package_def by blast
  then show
      "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof
    assume "A \<in> pp_finite_next_cyclic_package"
    then show ?thesis
      using pp_t_symmetrized_model_package_gvalid
      unfolding
        SymmetrizedModelConstants.TreeHenkin.gvalid_set_def
      by blast
  next
    assume "A = pp_pure pp_t_first_cyclic_builder_type
      (pp_t_family_probe_builder
        pp_t_complemented_symmetrized_singleton_family_builder)"
    then show ?thesis
      using
        pp_t_symmetrized_model_complemented_builder_purity_gvalid
      by simp
  qed
qed

theorem pp_finite_two_family_cyclic_package_consistent:
  "CEV_axiom_consistent [] pp_finite_two_family_cyclic_package"
  using SymmetrizedModelConstants.pp_t_base_sound
    SymmetrizedModelConstants.pp_t_zeta_sound
    pp_t_symmetrized_model_two_family_package_gvalid
  by (rule
    SymmetrizedModelConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

section \<open>Closure of the cyclic package under output negation\<close>

definition pp_finite_negation_closed_cyclic_package ::
    "oterm set"
where
  "pp_finite_negation_closed_cyclic_package =
    pp_finite_two_family_cyclic_package
    \<union> {
      pp_pure
        (pp_t_first_cyclic_unary_type
          \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
        pp_t_unary_output_negator,
      pp_application_closure
        pp_t_first_cyclic_unary_type
        pp_t_first_cyclic_unary_type}"

lemma pp_finite_negation_closed_cyclic_package_finite:
  "finite pp_finite_negation_closed_cyclic_package"
  unfolding pp_finite_negation_closed_cyclic_package_def
  using pp_finite_two_family_cyclic_package_finite
  by simp

lemma pp_finite_negation_closed_cyclic_package_subset:
  "pp_finite_negation_closed_cyclic_package
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have negator_purity:
      "pp_pure
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
          pp_t_unary_output_negator
        \<in> pp_purity_schema"
    using pp_t_unary_output_negator_typed
      pp_t_unary_output_negator_logical
    unfolding pp_purity_schema_def
    by blast
  have unary_application:
      "pp_application_closure
          pp_t_first_cyclic_unary_type
          pp_t_first_cyclic_unary_type
        \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def
    by blast
  show ?thesis
    using pp_finite_two_family_cyclic_package_subset
      negator_purity unary_application
    unfolding pp_finite_negation_closed_cyclic_package_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

theorem
  pp_t_symmetrized_model_negation_closed_package_gvalid:
  "SymmetrizedModelConstants.TreeHenkin.gvalid_set
    pp_finite_negation_closed_cyclic_package"
  unfolding SymmetrizedModelConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A:
      "A \<in> pp_finite_negation_closed_cyclic_package"
  then have cases:
      "A \<in> pp_finite_two_family_cyclic_package
      \<or>
      A =
        pp_pure
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
          pp_t_unary_output_negator
      \<or>
      A =
        pp_application_closure
          pp_t_first_cyclic_unary_type
          pp_t_first_cyclic_unary_type"
    unfolding
      pp_finite_negation_closed_cyclic_package_def
    by blast
  then show
      "SymmetrizedModelConstants.TreeHenkin.gvalid \<Gamma> A"
  proof
    assume old:
        "A \<in> pp_finite_two_family_cyclic_package"
    show ?thesis
      using pp_t_symmetrized_model_two_family_package_gvalid
        old
      unfolding
        SymmetrizedModelConstants.TreeHenkin.gvalid_set_def
      by blast
  next
    assume new:
        "A =
          pp_pure
            (pp_t_first_cyclic_unary_type
              \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
            pp_t_unary_output_negator
        \<or>
        A =
          pp_application_closure
            pp_t_first_cyclic_unary_type
            pp_t_first_cyclic_unary_type"
    then show ?thesis
    proof
      assume "A =
        pp_pure
          (pp_t_first_cyclic_unary_type
            \<rightarrow>\<^sub>o pp_t_first_cyclic_unary_type)
          pp_t_unary_output_negator"
      then show ?thesis
        using
          pp_t_symmetrized_model_output_negator_purity_gvalid
        by simp
    next
      assume "A =
        pp_application_closure
          pp_t_first_cyclic_unary_type
          pp_t_first_cyclic_unary_type"
      then show ?thesis
        using
          pp_t_symmetrized_model_output_negator_application_closure_gvalid
        by simp
    qed
  qed
qed

theorem pp_finite_negation_closed_cyclic_package_consistent:
  "CEV_axiom_consistent []
    pp_finite_negation_closed_cyclic_package"
  using SymmetrizedModelConstants.pp_t_base_sound
    SymmetrizedModelConstants.pp_t_zeta_sound
    pp_t_symmetrized_model_negation_closed_package_gvalid
  by (rule
    SymmetrizedModelConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

end
