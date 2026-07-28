theory Bacon_PP_ZF_Fresh_Identity_Negation_Fragment_Model
  imports Bacon_PP_ZF_Fresh_Identity_Fragment_Model
begin

section \<open>Adding purity of propositional negation\<close>

text \<open>
  We retain purity of the proposition identity operator and add purity of
  propositional negation.  PP and closure of purity under application then
  require five equivalence classes: truth and falsity at proposition type,
  identity and negation at unary proposition type, and the predicate that
  classifies the identity-negation pair.
\<close>

abbreviation pp_t_idneg_unary_type :: otype where
  "pp_t_idneg_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_idneg_classifier_type :: otype where
  "pp_t_idneg_classifier_type \<equiv>
    pp_t_idneg_unary_type \<rightarrow>\<^sub>o Prop"

definition pp_t_negation_operator :: ZF where
  "pp_t_negation_operator =
    Lambda (pp_t_domain Prop)
      (\<lambda>p. pp_t_prop (\<lambda>w. \<not> pp_t_holds p w))"

lemma pp_t_negation_operator_in_domain:
  "Elem pp_t_negation_operator
    (pp_t_domain pp_t_idneg_unary_type)"
proof (unfold pp_t_negation_operator_def, rule pp_t_lambda_closed)
  show "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_t_prop (\<lambda>w. \<not> pp_t_holds p w))
        (pp_t_domain Prop)"
    by (rule pp_t_prop_in_domain)
  show "\<And>w p q.
      Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem q (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w p q \<Longrightarrow>
      pp_t_eqv Prop w
        (pp_t_prop (\<lambda>v. \<not> pp_t_holds p v))
        (pp_t_prop (\<lambda>v. \<not> pp_t_holds q v))"
    unfolding pp_t_prop_eqv_pp_t_prop_iff
    using pp_t_prop_eqv_at by blast
qed

lemma pp_t_negation_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_negation_operator \<acute> p =
    pp_t_prop (\<lambda>w. \<not> pp_t_holds p w)"
  using p
  by (simp add: pp_t_negation_operator_def Lambda_app)

lemma pp_t_negation_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_negation_operator \<acute> p) w
    \<longleftrightarrow> \<not> pp_t_holds p w"
  unfolding pp_t_negation_operator_apply[OF p]
  by simp

lemma pp_t_eval_pp_negation_operator[simp]:
  "pp_t_eval C \<rho> pp_negation_operator =
    pp_t_negation_operator"
  unfolding pp_negation_operator_def pp_t_negation_operator_def
  by simp

definition pp_t_idneg_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_idneg_unary_pure w x \<longleftrightarrow>
    pp_t_eqv pp_t_idneg_unary_type
      w pp_t_identity_operator x
    \<or>
    pp_t_eqv pp_t_idneg_unary_type
      w pp_t_negation_operator x"

lemma pp_t_idneg_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_idneg_unary_type
    pp_t_idneg_unary_pure"
proof -
  have identity:
      "pp_t_predicate_admissible pp_t_idneg_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_idneg_unary_type
          w pp_t_identity_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_identity_operator_in_domain] .
  have negation:
      "pp_t_predicate_admissible pp_t_idneg_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_idneg_unary_type
          w pp_t_negation_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_negation_operator_in_domain] .
  show ?thesis
    using identity negation
    unfolding pp_t_predicate_admissible_def
      pp_t_idneg_unary_pure_def
    by blast
qed

definition pp_t_idneg_stock_classifier :: ZF where
  "pp_t_idneg_stock_classifier =
    pp_t_classifier pp_t_idneg_unary_type
      pp_t_idneg_unary_pure"

lemma pp_t_idneg_stock_classifier_in_domain:
  "Elem pp_t_idneg_stock_classifier
    (pp_t_domain pp_t_idneg_classifier_type)"
  unfolding pp_t_idneg_stock_classifier_def
  using pp_t_classifier_in_domain[
    OF pp_t_idneg_unary_pure_admissible] .

definition pp_t_idneg_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_idneg_fragment_pure \<sigma> w x \<longleftrightarrow>
    (\<sigma> = Prop
      \<and>
      (pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x))
    \<or>
    (\<sigma> = pp_t_idneg_unary_type
      \<and> pp_t_idneg_unary_pure w x)
    \<or>
    (\<sigma> = pp_t_idneg_classifier_type
      \<and> pp_t_eqv pp_t_idneg_classifier_type
        w pp_t_idneg_stock_classifier x)"

lemma pp_t_idneg_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_idneg_fragment_pure \<sigma>)"
proof -
  have truth:
      "pp_t_predicate_admissible Prop
        (\<lambda>w x. pp_t_eqv Prop w (pp_zf_truth True) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_truth_in_domain] .
  have falsity:
      "pp_t_predicate_admissible Prop
        (\<lambda>w x. pp_t_eqv Prop w (pp_zf_truth False) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_truth_in_domain] .
  have unary:
      "pp_t_predicate_admissible pp_t_idneg_unary_type
        pp_t_idneg_unary_pure"
    by (rule pp_t_idneg_unary_pure_admissible)
  have classifier:
      "pp_t_predicate_admissible pp_t_idneg_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_idneg_classifier_type
          w pp_t_idneg_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_idneg_stock_classifier_in_domain] .
  show ?thesis
    using truth falsity unary classifier
    unfolding pp_t_predicate_admissible_def
      pp_t_idneg_fragment_pure_def
    by blast
qed

lemma pp_t_idneg_truth_is_pure[simp]:
  "pp_t_idneg_fragment_pure Prop w (pp_zf_truth True)"
  unfolding pp_t_idneg_fragment_pure_def
  using pp_t_eqv_reflexive[OF pp_t_truth_in_domain]
  by blast

lemma pp_t_idneg_falsity_is_pure[simp]:
  "pp_t_idneg_fragment_pure Prop w (pp_zf_truth False)"
  unfolding pp_t_idneg_fragment_pure_def
  using pp_t_eqv_reflexive[OF pp_t_truth_in_domain]
  by blast

lemma pp_t_idneg_identity_is_pure[simp]:
  "pp_t_idneg_fragment_pure pp_t_idneg_unary_type
    w pp_t_identity_operator"
  unfolding pp_t_idneg_fragment_pure_def
    pp_t_idneg_unary_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_identity_operator_in_domain]
  by blast

lemma pp_t_idneg_negation_is_pure[simp]:
  "pp_t_idneg_fragment_pure pp_t_idneg_unary_type
    w pp_t_negation_operator"
  unfolding pp_t_idneg_fragment_pure_def
    pp_t_idneg_unary_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_negation_operator_in_domain]
  by blast

lemma pp_t_idneg_classifier_is_pure[simp]:
  "pp_t_idneg_fragment_pure pp_t_idneg_classifier_type
    w pp_t_idneg_stock_classifier"
  unfolding pp_t_idneg_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_idneg_stock_classifier_in_domain]
  by blast

lemma pp_t_negation_truth_eqv:
  "pp_t_eqv Prop w
    (pp_t_negation_operator \<acute> pp_zf_truth b)
    (pp_zf_truth (\<not> b))"
  using pp_t_negation_operator_holds[
    OF pp_t_truth_in_domain, of b]
  by simp

lemma pp_t_idneg_classifier_on_pure:
  assumes x: "Elem x (pp_t_domain pp_t_idneg_unary_type)"
    and pure: "pp_t_idneg_unary_pure w x"
  shows "pp_t_eqv Prop w
    (pp_t_idneg_stock_classifier \<acute> x)
    (pp_zf_truth True)"
proof -
  have pure_future:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_idneg_unary_pure v x"
    using pure
    unfolding pp_t_idneg_unary_pure_def
    using pp_t_eqv_persistent by blast
  show ?thesis
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_idneg_stock_classifier_def
    using pp_t_classifier_holds[
      OF x, of pp_t_idneg_unary_pure]
      pure_future
    by simp
qed

lemma pp_t_idneg_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_idneg_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x: "pp_t_idneg_fragment_pure \<sigma> w x"
  shows "pp_t_idneg_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (unary)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_idneg_unary_pure w f"
    | (classifier)
        "\<sigma> = pp_t_idneg_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_idneg_classifier_type
          w pp_t_idneg_stock_classifier f"
    unfolding pp_t_idneg_fragment_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case unary
    have f_domain:
        "Elem f (pp_t_domain pp_t_idneg_unary_type)"
      using f unary by simp
    have x_domain: "Elem x (pp_t_domain Prop)"
      using x unary by simp
    from unary(3) consider
        (identity)
          "pp_t_eqv pp_t_idneg_unary_type
            w pp_t_identity_operator f"
      | (negation)
          "pp_t_eqv pp_t_idneg_unary_type
            w pp_t_negation_operator f"
      unfolding pp_t_idneg_unary_pure_def by blast
    then show ?thesis
    proof cases
      case identity
      from pure_x unary consider
          (truth) "pp_t_eqv Prop w (pp_zf_truth True) x"
        | (falsity) "pp_t_eqv Prop w (pp_zf_truth False) x"
        unfolding pp_t_idneg_fragment_pure_def by blast
      then show ?thesis
      proof cases
        case truth
        have applications:
            "pp_t_eqv Prop w
              (pp_t_identity_operator \<acute> pp_zf_truth True)
              (f \<acute> x)"
          using pp_t_app_respects[
            OF identity pp_t_truth_in_domain x_domain truth] .
        have identity_truth:
            "pp_t_identity_operator \<acute> pp_zf_truth True =
              pp_zf_truth True"
          using pp_t_truth_in_domain
          by (simp add: pp_t_identity_operator_def Lambda_app)
        show ?thesis
          using unary applications
          unfolding identity_truth pp_t_idneg_fragment_pure_def
          by blast
      next
        case falsity
        have applications:
            "pp_t_eqv Prop w
              (pp_t_identity_operator \<acute> pp_zf_truth False)
              (f \<acute> x)"
          using pp_t_app_respects[
            OF identity pp_t_truth_in_domain x_domain falsity] .
        have identity_falsity:
            "pp_t_identity_operator \<acute> pp_zf_truth False =
              pp_zf_truth False"
          using pp_t_truth_in_domain
          by (simp add: pp_t_identity_operator_def Lambda_app)
        show ?thesis
          using unary applications
          unfolding identity_falsity pp_t_idneg_fragment_pure_def
          by blast
      qed
    next
      case negation
      from pure_x unary consider
          (truth) "pp_t_eqv Prop w (pp_zf_truth True) x"
        | (falsity) "pp_t_eqv Prop w (pp_zf_truth False) x"
        unfolding pp_t_idneg_fragment_pure_def by blast
      then show ?thesis
      proof cases
        case truth
        have applications:
            "pp_t_eqv Prop w
              (pp_t_negation_operator \<acute> pp_zf_truth True)
              (f \<acute> x)"
          using pp_t_app_respects[
            OF negation pp_t_truth_in_domain x_domain truth] .
        have result:
            "pp_t_eqv Prop w
              (pp_zf_truth False) (f \<acute> x)"
          using pp_t_negation_truth_eqv[of w True]
            applications
            pp_t_app_closed[
              OF pp_t_negation_operator_in_domain
                pp_t_truth_in_domain]
            pp_t_app_closed[OF f_domain x_domain]
            pp_t_truth_in_domain
          by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
        show ?thesis
          using unary result
          unfolding pp_t_idneg_fragment_pure_def by blast
      next
        case falsity
        have applications:
            "pp_t_eqv Prop w
              (pp_t_negation_operator \<acute> pp_zf_truth False)
              (f \<acute> x)"
          using pp_t_app_respects[
            OF negation pp_t_truth_in_domain x_domain falsity] .
        have result:
            "pp_t_eqv Prop w
              (pp_zf_truth True) (f \<acute> x)"
          using pp_t_negation_truth_eqv[of w False]
            applications
            pp_t_app_closed[
              OF pp_t_negation_operator_in_domain
                pp_t_truth_in_domain]
            pp_t_app_closed[OF f_domain x_domain]
            pp_t_truth_in_domain
          by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
        show ?thesis
          using unary result
          unfolding pp_t_idneg_fragment_pure_def by blast
      qed
    qed
  next
    case classifier
    have f_domain:
        "Elem f (pp_t_domain pp_t_idneg_classifier_type)"
      using f classifier by simp
    have x_domain:
        "Elem x (pp_t_domain pp_t_idneg_unary_type)"
      using x classifier by simp
    have x_pure: "pp_t_idneg_unary_pure w x"
      using pure_x classifier
      unfolding pp_t_idneg_fragment_pure_def by simp
    have x_refl:
        "pp_t_eqv pp_t_idneg_unary_type w x x"
      using pp_t_eqv_reflexive[OF x_domain] .
    have applications:
        "pp_t_eqv Prop w
          (pp_t_idneg_stock_classifier \<acute> x)
          (f \<acute> x)"
      using pp_t_app_respects[
        OF classifier(3) x_domain x_domain x_refl] .
    have result:
        "pp_t_eqv Prop w
          (pp_zf_truth True) (f \<acute> x)"
      using pp_t_idneg_classifier_on_pure[OF x_domain x_pure]
        applications pp_t_truth_in_domain
        pp_t_app_closed[
          OF pp_t_idneg_stock_classifier_in_domain x_domain]
        pp_t_app_closed[OF f_domain x_domain]
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    show ?thesis
      using classifier result
      unfolding pp_t_idneg_fragment_pure_def by blast
  qed
qed

theorem pp_t_idneg_false_seed_does_not_recombine:
  "\<not> pp_t_unary_recombines_at
    pp_t_idneg_unary_pure (pp_zf_truth False) w"
proof
  assume recombines:
      "pp_t_unary_recombines_at
        pp_t_idneg_unary_pure (pp_zf_truth False) w"
  have negation_pure:
      "pp_t_idneg_unary_pure w pp_t_negation_operator"
    unfolding pp_t_idneg_unary_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_negation_operator_in_domain]
    by blast
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds
          (pp_t_negation_operator \<acute> pp_zf_truth False) v"
    using pp_t_negation_operator_holds[
      OF pp_t_truth_in_domain[of False]]
    by simp
  have universal:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_negation_operator \<acute> q) w"
    using recombines pp_t_negation_operator_in_domain
      negation_pure necessary
    unfolding pp_t_unary_recombines_at_def
    by blast
  have negation_truth:
      "pp_t_holds
        (pp_t_negation_operator \<acute> pp_zf_truth True) w"
    using universal pp_t_truth_in_domain by blast
  show False
    using negation_truth
      pp_t_negation_operator_holds[
        OF pp_t_truth_in_domain[of True], of w]
    by simp
qed

section \<open>The moving-fundamental interpretation\<close>

interpretation IdNegFragment:
  pp_t_moving_internal_parameters pp_t_idneg_fragment_pure
  by standard (rule pp_t_idneg_fragment_pure_admissible)

abbreviation pp_t_idneg_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_idneg_constants \<equiv>
    pp_t_moving_internal_constants pp_t_idneg_fragment_pure"

lemma pp_t_idneg_identity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
      (pp_pure pp_t_idneg_unary_type prop_id)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using IdNegFragment.pp_t_moving_eval_pure_holds[
      OF typed_prop_id env, of w]
    by simp
qed

theorem pp_t_idneg_identity_purity_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_idneg_unary_type prop_id)"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_identity_purity_holds by blast

lemma pp_t_idneg_negation_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
      (pp_pure pp_t_idneg_unary_type pp_negation_operator)) w"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator : pp_t_idneg_unary_type"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using IdNegFragment.pp_t_moving_eval_pure_holds[
      OF typed env, of w]
    by simp
qed

theorem pp_t_idneg_negation_purity_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_idneg_unary_type pp_negation_operator)"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_negation_purity_holds by blast

lemma pp_t_idneg_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho> pp_target_PP) w"
proof -
  have classifier:
      "pp_t_classifier pp_t_idneg_unary_type
        (pp_t_idneg_fragment_pure pp_t_idneg_unary_type) =
        pp_t_idneg_stock_classifier"
    unfolding pp_t_idneg_stock_classifier_def
      pp_t_idneg_unary_pure_def
      pp_t_idneg_fragment_pure_def
    by simp
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_idneg_stock_classifier_in_domain,
      of "pp_t_idneg_fragment_pure
        pp_t_idneg_classifier_type" w]
    by (simp add: classifier)
qed

theorem pp_t_idneg_target_PP_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_target_PP_holds by blast

lemma pp_t_idneg_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_idneg_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_idneg_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_idneg_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_idneg_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_idneg_application_closure_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (IdNegFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      IdNegFragment.MovingTreeConstants.pp_t_den_def
      pp_t_idneg_application_closure_holds_iff
    using pp_t_idneg_fragment_application by blast
qed

theorem pp_t_idneg_unique_fundamental_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using IdNegFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_idneg_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using IdNegFragment.pp_t_moving_no_fundamentals_holds[
    OF assms]
  by blast

section \<open>Recombination and Exhaustion\<close>

lemma pp_t_idneg_fragment_pure_Prop_iff:
  "pp_t_idneg_fragment_pure Prop w P
    \<longleftrightarrow>
    (pp_t_eqv Prop w (pp_zf_truth True) P
      \<or> pp_t_eqv Prop w (pp_zf_truth False) P)"
  unfolding pp_t_idneg_fragment_pure_def by simp

lemma pp_t_idneg_fragment_pure_unary_iff:
  "pp_t_idneg_fragment_pure pp_t_idneg_unary_type w X
    \<longleftrightarrow>
    pp_t_idneg_unary_pure w X"
  unfolding pp_t_idneg_fragment_pure_def by simp

lemma pp_t_idneg_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
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
          (pp_t_eval pp_t_idneg_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_idneg_fragment_pure Prop w P"
      using IdNegFragment.pp_t_moving_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
    proof -
      assume box:
          "pp_t_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_t_holds P w
            \<longleftrightarrow>
            pp_t_holds (pp_zf_truth True) w"
        using pp_t_prop_eqv_at[OF box, of w] by simp
      show "pp_t_holds P w"
        using at_w by simp
    qed
    show "pp_t_holds
        (pp_t_eval pp_t_idneg_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_idneg_pure_true_implies_necessary:
  assumes P: "Elem P (pp_t_domain Prop)"
    and pure: "pp_t_idneg_fragment_pure Prop w P"
    and true_now: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  from pure consider
      (truth) "pp_t_eqv Prop w (pp_zf_truth True) P"
    | (falsity) "pp_t_eqv Prop w (pp_zf_truth False) P"
    unfolding pp_t_idneg_fragment_pure_Prop_iff by blast
  then show ?thesis
  proof cases
    case truth
    show ?thesis
      using pp_t_eqv_symmetric[
        OF pp_t_truth_in_domain P truth] .
  next
    case falsity
    have false_now:
        "\<not> pp_t_holds P w"
    proof -
      have iff:
          "pp_t_holds (pp_zf_truth False) w
            \<longleftrightarrow> pp_t_holds P w"
        using pp_t_prop_eqv_at[OF falsity, of w] by simp
      show ?thesis using iff by simp
    qed
    show ?thesis
      using true_now false_now by blast
  qed
qed

lemma pp_t_idneg_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
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
          (pp_t_eval pp_t_idneg_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_idneg_fragment_pure Prop w P"
      using IdNegFragment.pp_t_moving_eval_pure_holds[
        OF var_type extended, of w] by simp
    show "pp_t_holds
        (pp_t_eval pp_t_idneg_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_idneg_pure_true_implies_necessary[OF P]
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_idneg_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_idneg_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_idneg_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_idneg_fragment_pure
            pp_t_idneg_unary_type w X
          \<and> pp_t_moving_fundamental_at Prop w r)
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

lemma pp_t_idneg_fundamental_not_necessary:
  assumes X: "Elem X (pp_t_domain pp_t_idneg_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and X_pure:
      "pp_t_idneg_fragment_pure
        pp_t_idneg_unary_type w X"
    and r_fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  shows "\<not> (\<forall>v. prefix w v \<longrightarrow>
    pp_t_holds (X \<acute> r) v)"
proof
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  have r_seed:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using r_fundamental by simp
  have seed_r:
      "pp_t_eqv Prop w (pp_t_moving_seed w) r"
    using pp_t_eqv_symmetric[
      OF r pp_t_moving_seed_in_domain r_seed] .
  from X_pure consider
      (identity)
        "pp_t_eqv pp_t_idneg_unary_type
          w pp_t_identity_operator X"
    | (negation)
        "pp_t_eqv pp_t_idneg_unary_type
          w pp_t_negation_operator X"
    unfolding pp_t_idneg_fragment_pure_unary_iff
      pp_t_idneg_unary_pure_def
    by blast
  then show False
  proof cases
    case identity
    have applications:
        "pp_t_eqv Prop w
          (pp_t_identity_operator \<acute> pp_t_moving_seed w)
          (X \<acute> r)"
      using pp_t_app_respects[
        OF identity pp_t_moving_seed_in_domain r seed_r] .
    let ?v = "w @ [False]"
    have future: "prefix w ?v" by simp
    have Xr_true: "pp_t_holds (X \<acute> r) ?v"
      using necessary future by blast
    have transfer:
        "pp_t_holds
          (pp_t_identity_operator \<acute> pp_t_moving_seed w) ?v
        \<longleftrightarrow>
        pp_t_holds (X \<acute> r) ?v"
      using pp_t_prop_eqv_at[OF applications future] .
    have identity_seed:
        "pp_t_identity_operator \<acute> pp_t_moving_seed w =
          pp_t_moving_seed w"
      using pp_t_moving_seed_in_domain
      by (simp add: pp_t_identity_operator_def Lambda_app)
    have seed_false:
        "\<not> pp_t_holds (pp_t_moving_seed w) ?v"
      by simp
    show False
      using Xr_true transfer seed_false
      unfolding identity_seed by blast
  next
    case negation
    have applications:
        "pp_t_eqv Prop w
          (pp_t_negation_operator \<acute> pp_t_moving_seed w)
          (X \<acute> r)"
      using pp_t_app_respects[
        OF negation pp_t_moving_seed_in_domain r seed_r] .
    let ?v = "w @ [True]"
    have future: "prefix w ?v" by simp
    have Xr_true: "pp_t_holds (X \<acute> r) ?v"
      using necessary future by blast
    have transfer:
        "pp_t_holds
          (pp_t_negation_operator \<acute> pp_t_moving_seed w) ?v
        \<longleftrightarrow>
        pp_t_holds (X \<acute> r) ?v"
      using pp_t_prop_eqv_at[OF applications future] .
    have negation_false:
        "\<not> pp_t_holds
          (pp_t_negation_operator \<acute> pp_t_moving_seed w) ?v"
      using pp_t_negation_operator_holds[
        OF pp_t_moving_seed_in_domain, of w ?v]
      by simp
    show False
      using Xr_true transfer negation_false by blast
  qed
qed

theorem pp_t_idneg_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_idneg_unary_recombination_holds_iff
  using pp_t_idneg_fundamental_not_necessary
  by blast

lemma pp_t_idneg_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_idneg_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_idneg_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_idneg_fragment_pure
            pp_t_idneg_unary_type w X
          \<and> pp_t_moving_fundamental_at Prop w r)
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

lemma pp_t_idneg_not_universally_true:
  assumes X: "Elem X (pp_t_domain pp_t_idneg_unary_type)"
    and X_pure:
      "pp_t_idneg_fragment_pure
        pp_t_idneg_unary_type w X"
  shows "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w)"
proof
  assume universal:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
  from X_pure consider
      (identity)
        "pp_t_eqv pp_t_idneg_unary_type
          w pp_t_identity_operator X"
    | (negation)
        "pp_t_eqv pp_t_idneg_unary_type
          w pp_t_negation_operator X"
    unfolding pp_t_idneg_fragment_pure_unary_iff
      pp_t_idneg_unary_pure_def
    by blast
  then show False
  proof cases
    case identity
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
        OF identity pp_t_truth_in_domain
          pp_t_truth_in_domain false_refl] .
    have identity_false:
        "pp_t_identity_operator \<acute> pp_zf_truth False =
          pp_zf_truth False"
      using pp_t_truth_in_domain[of False]
      by (simp add: pp_t_identity_operator_def Lambda_app)
    have false_true: "pp_t_holds (pp_zf_truth False) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        universal[rule_format, OF pp_t_truth_in_domain]
      unfolding identity_false by simp
    show False using false_true by simp
  next
    case negation
    have true_refl:
        "pp_t_eqv Prop w
          (pp_zf_truth True) (pp_zf_truth True)"
      using pp_t_eqv_reflexive[
        OF pp_t_truth_in_domain[of True]] .
    have applications:
        "pp_t_eqv Prop w
          (pp_t_negation_operator \<acute> pp_zf_truth True)
          (X \<acute> pp_zf_truth True)"
      using pp_t_app_respects[
        OF negation pp_t_truth_in_domain
          pp_t_truth_in_domain true_refl] .
    have negation_false:
        "\<not> pp_t_holds
          (pp_t_negation_operator \<acute> pp_zf_truth True) w"
      using pp_t_negation_operator_holds[
        OF pp_t_truth_in_domain[of True], of w]
      by simp
    have negation_true:
        "pp_t_holds
          (pp_t_negation_operator \<acute> pp_zf_truth True) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        universal[rule_format, OF pp_t_truth_in_domain]
      by simp
    show False using negation_false negation_true by blast
  qed
qed

theorem pp_t_idneg_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_idneg_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_idneg_unary_exhaustion_holds_iff
  using pp_t_idneg_not_universally_true
  by blast

theorem pp_t_idneg_zeroary_recombination_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_zeroary_recombination_holds by blast

theorem pp_t_idneg_zeroary_exhaustion_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_zeroary_exhaustion_holds by blast

theorem pp_t_idneg_unary_recombination_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_unary_recombination_holds by blast

theorem pp_t_idneg_unary_exhaustion_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    IdNegFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_idneg_unary_exhaustion_holds by blast

section \<open>Modalized Functionality and consistency\<close>

lemma pp_t_idneg_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_idneg_constants \<rho>
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

theorem pp_t_idneg_modalized_functionality_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (IdNegFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      IdNegFragment.MovingTreeConstants.pp_t_den_def
      pp_t_idneg_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

definition pp_identity_negation_fragment_PP_axioms ::
    "oterm set"
where
  "pp_identity_negation_fragment_PP_axioms =
    insert
      (pp_pure pp_t_idneg_unary_type prop_id)
      (insert
        (pp_pure pp_t_idneg_unary_type pp_negation_operator)
        pp_fresh_sparse_PP_axioms)"

theorem pp_t_identity_negation_fragment_PP_gvalid:
  "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_identity_negation_fragment_PP_axioms"
  unfolding
    IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_identity_negation_fragment_PP_axioms"
  from A consider
      (identity_purity)
        "A = pp_pure pp_t_idneg_unary_type prop_id"
    | (negation_purity)
        "A = pp_pure pp_t_idneg_unary_type
          pp_negation_operator"
    | (target) "A = pp_target_PP"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> pp_modalized_functionality_schema"
    unfolding pp_identity_negation_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show
      "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case identity_purity
    then show ?thesis
      using pp_t_idneg_identity_purity_gvalid by simp
  next
    case negation_purity
    then show ?thesis
      using pp_t_idneg_negation_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_idneg_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_idneg_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_idneg_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_idneg_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_idneg_zeroary_recombination_gvalid by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_idneg_unary_recombination_gvalid by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_idneg_zeroary_exhaustion_gvalid by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_idneg_unary_exhaustion_gvalid by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_idneg_modalized_functionality_gvalid)
  qed
qed

theorem pp_identity_negation_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_identity_negation_fragment_PP_axioms"
  using
    IdNegFragment.MovingTreeConstants.pp_t_base_sound
    IdNegFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_identity_negation_fragment_PP_gvalid
  by (rule
    IdNegFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_identity_negation_fragment_consistent:
  assumes
    "U \<subseteq> pp_identity_negation_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_identity_negation_fragment_PP_gvalid
    unfolding
      IdNegFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      IdNegFragment.MovingTreeConstants.pp_t_base_sound
      IdNegFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      IdNegFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
