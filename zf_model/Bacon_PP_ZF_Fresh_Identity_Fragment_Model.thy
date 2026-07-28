theory Bacon_PP_ZF_Fresh_Identity_Fragment_Model
  imports
    Bacon_PP_ZF_Fresh_Sparse_Fragment_Model
    Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers
begin

section \<open>Adding purity of the proposition identity operator\<close>

text \<open>
  We add the logical-purity instance for the closed identity operator on
  propositions.  Closure of purity under application and PP then require
  three equivalence classes: the identity operator, the true proposition,
  and the classifier of the identity class.  No further class is generated
  by application.
\<close>

abbreviation pp_t_identity_unary_type :: otype where
  "pp_t_identity_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_identity_classifier_type :: otype where
  "pp_t_identity_classifier_type \<equiv>
    pp_t_identity_unary_type \<rightarrow>\<^sub>o Prop"

definition pp_t_identity_operator :: ZF where
  "pp_t_identity_operator =
    Lambda (pp_t_domain Prop) (\<lambda>x. x)"

lemma pp_t_identity_operator_in_domain:
  "Elem pp_t_identity_operator
    (pp_t_domain pp_t_identity_unary_type)"
proof (unfold pp_t_identity_operator_def, rule pp_t_lambda_closed)
  show "\<And>x. Elem x (pp_t_domain Prop) \<Longrightarrow>
      Elem x (pp_t_domain Prop)"
    by simp
  show "\<And>w x y.
      Elem x (pp_t_domain Prop) \<Longrightarrow>
      Elem y (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w x y \<Longrightarrow>
      pp_t_eqv Prop w x y"
    by simp
qed

lemma pp_t_eval_prop_id[simp]:
  "pp_t_eval C \<rho> prop_id = pp_t_identity_operator"
  unfolding prop_id_def pp_t_identity_operator_def
  by simp

definition pp_t_identity_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_identity_unary_pure w x \<longleftrightarrow>
    pp_t_eqv pp_t_identity_unary_type
      w pp_t_identity_operator x"

lemma pp_t_identity_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_identity_unary_type
    pp_t_identity_unary_pure"
  unfolding pp_t_identity_unary_pure_def
  using pp_t_eqv_classifier_admissible[
    OF pp_t_identity_operator_in_domain] .

definition pp_t_identity_stock_classifier :: ZF where
  "pp_t_identity_stock_classifier =
    pp_t_classifier pp_t_identity_unary_type
      pp_t_identity_unary_pure"

lemma pp_t_identity_stock_classifier_in_domain:
  "Elem pp_t_identity_stock_classifier
    (pp_t_domain pp_t_identity_classifier_type)"
  unfolding pp_t_identity_stock_classifier_def
  using pp_t_classifier_in_domain[
    OF pp_t_identity_unary_pure_admissible] .

definition pp_t_identity_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_identity_fragment_pure \<sigma> w x \<longleftrightarrow>
    (\<sigma> = Prop
      \<and> pp_t_eqv Prop w (pp_zf_truth True) x)
    \<or>
    (\<sigma> = pp_t_identity_unary_type
      \<and> pp_t_identity_unary_pure w x)
    \<or>
    (\<sigma> = pp_t_identity_classifier_type
      \<and> pp_t_eqv pp_t_identity_classifier_type
        w pp_t_identity_stock_classifier x)"

lemma pp_t_identity_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_identity_fragment_pure \<sigma>)"
proof -
  have truth:
      "pp_t_predicate_admissible Prop
        (\<lambda>w x. pp_t_eqv Prop w (pp_zf_truth True) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_truth_in_domain] .
  have identity:
      "pp_t_predicate_admissible pp_t_identity_unary_type
        pp_t_identity_unary_pure"
    by (rule pp_t_identity_unary_pure_admissible)
  have classifier:
      "pp_t_predicate_admissible pp_t_identity_classifier_type
        (\<lambda>w x.
          pp_t_eqv pp_t_identity_classifier_type
            w pp_t_identity_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_identity_stock_classifier_in_domain] .
  show ?thesis
    using truth identity classifier
    unfolding pp_t_predicate_admissible_def
      pp_t_identity_fragment_pure_def
    by blast
qed

lemma pp_t_identity_is_pure[simp]:
  "pp_t_identity_fragment_pure pp_t_identity_unary_type
    w pp_t_identity_operator"
  unfolding pp_t_identity_fragment_pure_def
  apply (rule disjI2)
  apply (rule disjI1)
  apply (intro conjI)
   apply (rule refl)
  unfolding pp_t_identity_unary_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_identity_operator_in_domain] .

lemma pp_t_truth_is_pure[simp]:
  "pp_t_identity_fragment_pure Prop w (pp_zf_truth True)"
  unfolding pp_t_identity_fragment_pure_def
  apply (rule disjI1)
  apply (intro conjI)
   apply (rule refl)
  using pp_t_eqv_reflexive[OF pp_t_truth_in_domain] .

lemma pp_t_identity_classifier_is_pure[simp]:
  "pp_t_identity_fragment_pure pp_t_identity_classifier_type
    w pp_t_identity_stock_classifier"
  unfolding pp_t_identity_fragment_pure_def
  apply (rule disjI2)
  apply (rule disjI2)
  apply (intro conjI)
   apply (rule refl)
  using pp_t_eqv_reflexive[
    OF pp_t_identity_stock_classifier_in_domain] .

lemma pp_t_identity_stock_classifier_on_identity:
  "pp_t_eqv Prop w
    (pp_t_identity_stock_classifier \<acute> pp_t_identity_operator)
    (pp_zf_truth True)"
proof -
  have identity_all:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_identity_unary_pure v pp_t_identity_operator"
    unfolding pp_t_identity_unary_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_identity_operator_in_domain]
    by blast
  show ?thesis
    unfolding pp_t_identity_stock_classifier_def
      pp_t_prop_eqv_truth_iff
    using pp_t_classifier_holds[
      OF pp_t_identity_operator_in_domain,
      of pp_t_identity_unary_pure]
      identity_all
    by simp
qed

lemma pp_t_identity_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_identity_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x: "pp_t_identity_fragment_pure \<sigma> w x"
  shows "pp_t_identity_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (identity)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_identity_unary_type
          w pp_t_identity_operator f"
    | (classifier)
        "\<sigma> = pp_t_identity_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_identity_classifier_type
          w pp_t_identity_stock_classifier f"
    unfolding pp_t_identity_fragment_pure_def
      pp_t_identity_unary_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case identity
    have f_domain:
        "Elem f (pp_t_domain pp_t_identity_unary_type)"
      using f identity by simp
    have x_domain: "Elem x (pp_t_domain Prop)"
      using x identity by simp
    have x_truth:
        "pp_t_eqv Prop w (pp_zf_truth True) x"
      using pure_x identity
      unfolding pp_t_identity_fragment_pure_def
      by auto
    have outputs:
        "pp_t_eqv Prop w
          (pp_t_identity_operator \<acute> (pp_zf_truth True))
          (f \<acute> x)"
      using pp_t_app_respects[
        OF identity(3)
          pp_t_truth_in_domain x_domain x_truth] .
    have identity_truth:
        "pp_t_identity_operator \<acute> (pp_zf_truth True) =
          pp_zf_truth True"
      using pp_t_truth_in_domain
      by (simp add: pp_t_identity_operator_def Lambda_app)
    have f_truth:
        "pp_t_eqv Prop w (pp_zf_truth True) (f \<acute> x)"
      using outputs identity_truth by simp
    show ?thesis
      using identity f_truth
      unfolding pp_t_identity_fragment_pure_def
      by simp
  next
    case classifier
    have f_domain:
        "Elem f (pp_t_domain pp_t_identity_classifier_type)"
      using f classifier by simp
    have x_domain:
        "Elem x (pp_t_domain pp_t_identity_unary_type)"
      using x classifier by simp
    have x_identity:
        "pp_t_eqv pp_t_identity_unary_type
          w pp_t_identity_operator x"
      using pure_x classifier
      unfolding pp_t_identity_fragment_pure_def
        pp_t_identity_unary_pure_def
      by auto
    have outputs:
        "pp_t_eqv Prop w
          (pp_t_identity_stock_classifier \<acute>
            pp_t_identity_operator)
          (f \<acute> x)"
      using pp_t_app_respects[
        OF classifier(3)
          pp_t_identity_operator_in_domain x_domain x_identity] .
    have truth_output:
        "pp_t_eqv Prop w
          (pp_zf_truth True) (f \<acute> x)"
      using pp_t_identity_stock_classifier_on_identity
        outputs
        pp_t_truth_in_domain
        pp_t_app_closed[
          OF pp_t_identity_stock_classifier_in_domain
            pp_t_identity_operator_in_domain]
        pp_t_app_closed[OF f_domain x_domain]
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    show ?thesis
      using classifier truth_output
      unfolding pp_t_identity_fragment_pure_def
      by simp
  qed
qed

section \<open>The induced interpretation\<close>

definition pp_t_identity_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_identity_fragment_constants =
    pp_t_seeded_internal_constants
      pp_t_identity_fragment_pure pp_t_fresh_seed"

interpretation IdentityFragmentConstants:
  pp_t_constants pp_t_identity_fragment_constants
proof
  fix c \<sigma>
  show "Elem (pp_t_identity_fragment_constants c \<sigma>)
      (pp_t_domain \<sigma>)"
  proof (cases \<sigma>)
    case Ind
    show ?thesis
      unfolding Ind pp_t_identity_fragment_constants_def
      using pp_t_default_in_domain[of Ind] by simp
  next
    case Prop
    show ?thesis
      unfolding Prop pp_t_identity_fragment_constants_def
      using pp_t_default_in_domain[of Prop] by simp
  next
    case (Arr \<sigma> \<tau>)
    have pure_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_identity_fragment_pure \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF pp_t_identity_fragment_pure_admissible] .
    have fundamental_admissible:
        "pp_t_predicate_admissible \<sigma>
          (pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>)"
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
          and future: "prefix w v"
        have xy_v: "pp_t_eqv Prop v x y"
          using pp_t_eqv_persistent[OF xy future] .
        have seed_refl:
            "pp_t_eqv Prop v
              (pp_t_fresh_seed v) (pp_t_fresh_seed v)"
          using pp_t_eqv_reflexive[OF pp_t_fresh_seed_typed] .
        show "pp_t_seeded_fundamental_at
              pp_t_fresh_seed Prop v x =
            pp_t_seeded_fundamental_at
              pp_t_fresh_seed Prop v y"
          using pp_t_eqv_congruence[
            OF x y pp_t_fresh_seed_typed
              pp_t_fresh_seed_typed xy_v seed_refl]
          by simp
      qed
    next
      case (Arr \<sigma> \<tau>)
      then show ?thesis
        by (simp add: pp_t_predicate_admissible_def)
    qed
    have fun_classifier:
        "Elem
          (pp_t_classifier \<sigma>
            (pp_t_seeded_fundamental_at
              pp_t_fresh_seed \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF fundamental_admissible] .
    have default:
        "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using pp_t_default_in_domain .
    show ?thesis
      using Arr pure_classifier fun_classifier default
      by (auto simp: pp_t_identity_fragment_constants_def)
  qed
qed

lemma pp_t_identity_eval_Pure[simp]:
  "pp_t_eval pp_t_identity_fragment_constants \<rho>
      (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_identity_fragment_pure \<sigma>)"
  by (simp add: pp_t_identity_fragment_constants_def
      pp_Pure_def pp_pure_name_def)

lemma pp_t_identity_eval_Fun[simp]:
  "pp_t_eval pp_t_identity_fragment_constants \<rho>
      (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>)"
  by (simp add: pp_t_identity_fragment_constants_def
      pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_identity_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_identity_fragment_pure \<sigma> w
        (pp_t_eval pp_t_identity_fragment_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_identity_fragment_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using IdentityFragmentConstants.pp_t_eval_type[
      OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_identity_fragment_pure \<sigma>" w]
    by simp
qed

lemma pp_t_identity_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma> w
        (pp_t_eval pp_t_identity_fragment_constants \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval pp_t_identity_fragment_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using IdentityFragmentConstants.pp_t_eval_type[
      OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>" w]
    by simp
qed

lemma pp_t_identity_logical_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      (pp_pure pp_t_identity_unary_type prop_id)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using pp_t_identity_eval_pure_holds[
      OF typed_prop_id env, of w]
    by simp
qed

theorem pp_t_identity_logical_purity_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_identity_unary_type prop_id)"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_logical_purity_holds by blast

lemma pp_t_identity_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have classifier:
      "pp_t_classifier pp_t_identity_unary_type
        (pp_t_identity_fragment_pure
          pp_t_identity_unary_type) =
        pp_t_identity_stock_classifier"
    unfolding pp_t_identity_stock_classifier_def
      pp_t_identity_unary_pure_def
      pp_t_identity_fragment_pure_def
    by simp
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_identity_stock_classifier_in_domain,
      of "pp_t_identity_fragment_pure
        pp_t_identity_classifier_type" w]
    by (simp add: classifier)
qed

theorem pp_t_identity_target_PP_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_target_PP_holds by blast

lemma pp_t_identity_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_identity_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_identity_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_identity_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_identity_application_closure_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule IdentityFragmentConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (IdentityFragmentConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding IdentityFragmentConstants.pp_t_den_def
      pp_t_identity_application_closure_holds_iff
    using pp_t_identity_fragment_application by blast
qed

lemma pp_t_identity_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  have eval_same:
      "pp_t_eval pp_t_identity_fragment_constants \<rho>
          (pp_unique_fundamental Prop) =
        pp_t_eval pp_t_fresh_sparse_constants \<rho>
          (pp_unique_fundamental Prop)"
    unfolding pp_unique_fundamental_def pp_fun_def
      pp_Fun_def pp_t_identity_fragment_constants_def
      pp_t_fresh_sparse_constants_def
      pp_fun_name_def pp_pure_name_def
    by (simp add: pp_fun_name_def pp_pure_name_def)
  show ?thesis
    using pp_t_fresh_unique_fundamental_holds
    unfolding eval_same .
qed

lemma pp_t_identity_no_fundamentals_holds:
  assumes "\<sigma> \<noteq> Prop"
  shows "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have eval_same:
      "pp_t_eval pp_t_identity_fragment_constants \<rho>
          (pp_no_fundamentals \<sigma>) =
        pp_t_eval pp_t_fresh_sparse_constants \<rho>
          (pp_no_fundamentals \<sigma>)"
    unfolding pp_no_fundamentals_def pp_fun_def pp_Fun_def
      pp_t_identity_fragment_constants_def
      pp_t_fresh_sparse_constants_def
      pp_fun_name_def pp_pure_name_def
    by (simp add: pp_fun_name_def pp_pure_name_def)
  show ?thesis
    using pp_t_fresh_no_fundamentals_holds[OF assms]
    unfolding eval_same .
qed

theorem pp_t_identity_unique_fundamental_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_unique_fundamental_holds by blast

theorem pp_t_identity_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_no_fundamentals_holds[OF assms]
  by blast

section \<open>Recombination and Exhaustion\<close>

lemma pp_t_identity_fragment_pure_Prop_iff:
  "pp_t_identity_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_eqv Prop w (pp_zf_truth True) P"
  unfolding pp_t_identity_fragment_pure_def
  by simp

lemma pp_t_identity_fragment_pure_unary_iff:
  "pp_t_identity_fragment_pure pp_t_identity_unary_type w X
    \<longleftrightarrow>
    pp_t_identity_unary_pure w X"
  unfolding pp_t_identity_fragment_pure_def
  by simp

lemma pp_t_identity_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      pp_zeroary_recombination) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_recombination_def
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
          (pp_t_eval pp_t_identity_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_identity_fragment_pure Prop w P"
      using pp_t_identity_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
    proof -
      assume box: "pp_t_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_t_holds P w
            \<longleftrightarrow>
            pp_t_holds (pp_zf_truth True) w"
        using pp_t_prop_eqv_at[OF box, of w] by simp
      show "pp_t_holds P w"
        using at_w by simp
    qed
    show "pp_t_holds
        (pp_t_eval pp_t_identity_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_identity_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      pp_zeroary_exhaustion) w"
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
          (pp_t_eval pp_t_identity_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_identity_fragment_pure Prop w P"
      using pp_t_identity_eval_pure_holds[
        OF var_type extended, of w] by simp
    have pure_box:
        "pp_t_identity_fragment_pure Prop w P
          \<Longrightarrow>
        pp_t_eqv Prop w P (pp_zf_truth True)"
    proof -
      assume pure:
          "pp_t_identity_fragment_pure Prop w P"
      have truth_P:
          "pp_t_eqv Prop w (pp_zf_truth True) P"
        using pure
        unfolding pp_t_identity_fragment_pure_Prop_iff .
      show "pp_t_eqv Prop w P (pp_zf_truth True)"
        using pp_t_eqv_symmetric[
          OF pp_t_truth_in_domain P truth_P] .
    qed
    show "pp_t_holds
        (pp_t_eval pp_t_identity_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff pure_box
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_identity_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_identity_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_identity_fragment_pure
            pp_t_identity_unary_type w X
          \<and> pp_t_seeded_fundamental_at
            pp_t_fresh_seed Prop w r)
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

lemma pp_t_identity_fundamental_not_necessary:
  assumes X: "Elem X (pp_t_domain pp_t_identity_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and X_pure:
      "pp_t_identity_fragment_pure
        pp_t_identity_unary_type w X"
    and r_fundamental:
      "pp_t_seeded_fundamental_at
        pp_t_fresh_seed Prop w r"
  shows "\<not> (\<forall>v. prefix w v \<longrightarrow>
    pp_t_holds (X \<acute> r) v)"
proof
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  have identity_X:
      "pp_t_eqv pp_t_identity_unary_type
        w pp_t_identity_operator X"
    using X_pure
    unfolding pp_t_identity_fragment_pure_unary_iff
      pp_t_identity_unary_pure_def .
  have r_seed:
      "pp_t_eqv Prop w r (pp_t_fresh_seed w)"
    using r_fundamental by simp
  have seed_r:
      "pp_t_eqv Prop w (pp_t_fresh_seed w) r"
    using pp_t_eqv_symmetric[
      OF r pp_t_fresh_seed_typed r_seed] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> pp_t_fresh_seed w)
        (X \<acute> r)"
    using pp_t_app_respects[
      OF identity_X pp_t_fresh_seed_typed r seed_r] .
  have identity_seed:
      "pp_t_identity_operator \<acute> pp_t_fresh_seed w =
        pp_t_fresh_seed w"
    using pp_t_fresh_seed_typed
    by (simp add: pp_t_identity_operator_def Lambda_app)
  have seed_true: "pp_t_holds (pp_t_fresh_seed w) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      necessary
    unfolding identity_seed by simp
  have seed_false:
      "\<not> pp_t_holds (pp_t_fresh_seed w) w"
    unfolding pp_t_fresh_seed_def pp_t_holds_def pp_t_default.simps
    by (rule Empty)
  show False
    using seed_true seed_false by blast
qed

theorem pp_t_identity_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_identity_unary_recombination_holds_iff
  using pp_t_identity_fundamental_not_necessary
  by blast

lemma pp_t_identity_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_identity_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_identity_fragment_pure
            pp_t_identity_unary_type w X
          \<and> pp_t_seeded_fundamental_at
            pp_t_fresh_seed Prop w r)
        \<longrightarrow>
        ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w)
          \<longrightarrow>
          (\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v))))"
  by (simp add: pp_unary_exhaustion_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

lemma pp_t_identity_not_universally_true:
  assumes X: "Elem X (pp_t_domain pp_t_identity_unary_type)"
    and X_pure:
      "pp_t_identity_fragment_pure
        pp_t_identity_unary_type w X"
  shows "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w)"
proof
  assume universal:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
  have identity_X:
      "pp_t_eqv pp_t_identity_unary_type
        w pp_t_identity_operator X"
    using X_pure
    unfolding pp_t_identity_fragment_pure_unary_iff
      pp_t_identity_unary_pure_def .
  have false_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth False) (pp_zf_truth False)"
    using pp_t_eqv_reflexive[
      OF pp_t_truth_in_domain[of False]] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> pp_zf_truth False)
        (X \<acute> pp_zf_truth False)"
    using pp_t_app_respects[
      OF identity_X
        pp_t_truth_in_domain pp_t_truth_in_domain false_refl] .
  have identity_false:
      "pp_t_identity_operator \<acute> pp_zf_truth False =
        pp_zf_truth False"
    using pp_t_truth_in_domain[of False]
    by (simp add: pp_t_identity_operator_def Lambda_app)
  have false_true: "pp_t_holds (pp_zf_truth False) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      universal[rule_format, OF pp_t_truth_in_domain]
    unfolding identity_false by simp
  show False
    using false_true by simp
qed

theorem pp_t_identity_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_identity_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_identity_unary_exhaustion_holds_iff
  using pp_t_identity_not_universally_true
  by blast

theorem pp_t_identity_zeroary_recombination_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_zeroary_recombination_holds by blast

theorem pp_t_identity_zeroary_exhaustion_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_zeroary_exhaustion_holds by blast

theorem pp_t_identity_unary_recombination_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_unary_recombination_holds by blast

theorem pp_t_identity_unary_exhaustion_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_def
    IdentityFragmentConstants.pp_t_den_def
  using pp_t_identity_unary_exhaustion_holds by blast

section \<open>Modalized Functionality and the enlarged axiom stock\<close>

lemma pp_t_identity_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_identity_fragment_constants \<rho>
        (pp_modalized_functionality \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>g.
        Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
          (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
            pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> x)))
        \<longrightarrow>
        pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g)))"
  by (simp add: pp_modalized_functionality_def
      pp_t_eval_ObjBox_holds pp_t_prop_eqv_truth_iff
      extend_env.simps pp_t_three_extensions_index_two)

theorem pp_t_identity_modalized_functionality_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule IdentityFragmentConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (IdentityFragmentConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding IdentityFragmentConstants.pp_t_den_def
      pp_t_identity_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

definition pp_identity_fragment_PP_axioms :: "oterm set" where
  "pp_identity_fragment_PP_axioms =
    insert (pp_pure pp_t_identity_unary_type prop_id)
      pp_fresh_sparse_PP_axioms"

theorem pp_t_identity_fragment_PP_gvalid:
  "IdentityFragmentConstants.TreeHenkin.gvalid_set
    pp_identity_fragment_PP_axioms"
  unfolding IdentityFragmentConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_identity_fragment_PP_axioms"
  from A consider
      (identity_purity)
        "A = pp_pure pp_t_identity_unary_type prop_id"
    | (target) "A = pp_target_PP"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> pp_modalized_functionality_schema"
    unfolding pp_identity_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show "IdentityFragmentConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case identity_purity
    then show ?thesis
      using pp_t_identity_logical_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_identity_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_identity_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_identity_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_identity_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_identity_zeroary_recombination_gvalid by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_identity_unary_recombination_gvalid by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_identity_zeroary_exhaustion_gvalid by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_identity_unary_exhaustion_gvalid by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_identity_modalized_functionality_gvalid)
  qed
qed

theorem pp_identity_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent [] pp_identity_fragment_PP_axioms"
  using IdentityFragmentConstants.pp_t_base_sound
    IdentityFragmentConstants.pp_t_zeta_sound
    pp_t_identity_fragment_PP_gvalid
  by (rule
    IdentityFragmentConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_identity_fragment_consistent:
  assumes "U \<subseteq> pp_identity_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "IdentityFragmentConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_identity_fragment_PP_gvalid
    unfolding IdentityFragmentConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using IdentityFragmentConstants.pp_t_base_sound
      IdentityFragmentConstants.pp_t_zeta_sound valid
    by (rule
      IdentityFragmentConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
