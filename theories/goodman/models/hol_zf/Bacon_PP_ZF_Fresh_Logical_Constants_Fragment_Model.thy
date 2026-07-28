theory Bacon_PP_ZF_Fresh_Logical_Constants_Fragment_Model
  imports Bacon_PP_ZF_Fresh_Identity_Negation_Fragment_Model
begin

section \<open>Adding the constant-truth and constant-falsity operators\<close>

text \<open>
  We retain the preceding pure objects and add the closed unary operators
  that return truth and falsity, respectively, on every proposition.
  Application closure then has seven equivalence classes: truth and falsity,
  identity, negation, constant truth, constant falsity, and the predicate
  classifying those four unary operators.
\<close>

abbreviation pp_t_constants_unary_type :: otype where
  "pp_t_constants_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_constants_classifier_type :: otype where
  "pp_t_constants_classifier_type \<equiv>
    pp_t_constants_unary_type \<rightarrow>\<^sub>o Prop"

definition pp_t_constant_operator :: "bool \<Rightarrow> ZF" where
  "pp_t_constant_operator b =
    Lambda (pp_t_domain Prop) (\<lambda>_. pp_zf_truth b)"

lemma pp_t_constant_operator_in_domain:
  "Elem (pp_t_constant_operator b)
    (pp_t_domain pp_t_constants_unary_type)"
proof (unfold pp_t_constant_operator_def, rule pp_t_lambda_closed)
  show "\<And>x. Elem x (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_zf_truth b) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  show "\<And>w x y.
      Elem x (pp_t_domain Prop) \<Longrightarrow>
      Elem y (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w x y \<Longrightarrow>
      pp_t_eqv Prop w (pp_zf_truth b) (pp_zf_truth b)"
    using pp_t_eqv_reflexive[OF pp_t_truth_in_domain] .
qed

lemma pp_t_constant_operator_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_constant_operator b \<acute> p = pp_zf_truth b"
  using p
  by (simp add: pp_t_constant_operator_def Lambda_app)

lemma pp_t_constant_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_constant_operator b \<acute> p) w
    \<longleftrightarrow> b"
  unfolding pp_t_constant_operator_apply[OF p]
  by simp

lemma pp_t_eval_constant_truth_operator[simp]:
  "pp_t_eval C \<rho> (pp_constant_operator ObjTrue) =
    pp_t_constant_operator True"
proof -
  have argument:
      "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  show ?thesis
    unfolding pp_constant_operator_def pp_constant_builder_def
      pp_t_constant_operator_def
    using argument
    by (simp add: pp_t_eval_ObjTrue Lambda_app Lambda_ext)
qed

lemma pp_t_eval_constant_falsity_operator[simp]:
  "pp_t_eval C \<rho> (pp_constant_operator ObjFalse) =
    pp_t_constant_operator False"
proof -
  have eval_false:
      "pp_t_eval C \<rho> ObjFalse = pp_zf_truth False"
    unfolding ObjFalse_def
    apply (simp only: pp_t_eval.simps)
    apply (rule pp_t_prop_ext)
      apply (rule pp_t_prop_in_domain)
     apply (rule pp_t_truth_in_domain)
    by (simp add: pp_t_eval_ObjTrue)
  have argument:
      "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  show ?thesis
    unfolding pp_constant_operator_def pp_constant_builder_def
      pp_t_constant_operator_def
    using argument
    by (simp add: eval_false Lambda_app Lambda_ext)
qed

definition pp_t_constants_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_constants_unary_pure w x \<longleftrightarrow>
    pp_t_idneg_unary_pure w x
    \<or>
    pp_t_eqv pp_t_constants_unary_type
      w (pp_t_constant_operator True) x
    \<or>
    pp_t_eqv pp_t_constants_unary_type
      w (pp_t_constant_operator False) x"

lemma pp_t_constants_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    pp_t_constants_unary_pure"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        pp_t_idneg_unary_pure"
    by (rule pp_t_idneg_unary_pure_admissible)
  have truth:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator True) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_constant_operator_in_domain] .
  have falsity:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator False) x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_constant_operator_in_domain] .
  show ?thesis
    using old truth falsity
    unfolding pp_t_predicate_admissible_def
      pp_t_constants_unary_pure_def
    by blast
qed

definition pp_t_constants_stock_classifier :: ZF where
  "pp_t_constants_stock_classifier =
    pp_t_classifier pp_t_constants_unary_type
      pp_t_constants_unary_pure"

lemma pp_t_constants_stock_classifier_in_domain:
  "Elem pp_t_constants_stock_classifier
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_constants_stock_classifier_def
  using pp_t_classifier_in_domain[
    OF pp_t_constants_unary_pure_admissible] .

definition pp_t_constants_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_constants_fragment_pure \<sigma> w x \<longleftrightarrow>
    (\<sigma> = Prop
      \<and>
      (pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x))
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> pp_t_constants_unary_pure w x)
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type
        w pp_t_constants_stock_classifier x)"

lemma pp_t_constants_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_constants_fragment_pure \<sigma>)"
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
      "pp_t_predicate_admissible pp_t_constants_unary_type
        pp_t_constants_unary_pure"
    by (rule pp_t_constants_unary_pure_admissible)
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type
          w pp_t_constants_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_constants_stock_classifier_in_domain] .
  show ?thesis
    using truth falsity unary classifier
    unfolding pp_t_predicate_admissible_def
      pp_t_constants_fragment_pure_def
    by blast
qed

lemma pp_t_constants_truth_is_pure[simp]:
  "pp_t_constants_fragment_pure Prop w (pp_zf_truth b)"
proof (cases b)
  case True
  then show ?thesis
    unfolding pp_t_constants_fragment_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_truth_in_domain[of True]]
    by simp
next
  case False
  then show ?thesis
    unfolding pp_t_constants_fragment_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_truth_in_domain[of False]]
    by simp
qed

lemma pp_t_constants_identity_is_pure[simp]:
  "pp_t_constants_fragment_pure pp_t_constants_unary_type
    w pp_t_identity_operator"
  unfolding pp_t_constants_fragment_pure_def
    pp_t_constants_unary_pure_def pp_t_idneg_unary_pure_def
  using pp_t_eqv_reflexive[OF pp_t_identity_operator_in_domain]
  by blast

lemma pp_t_constants_negation_is_pure[simp]:
  "pp_t_constants_fragment_pure pp_t_constants_unary_type
    w pp_t_negation_operator"
  unfolding pp_t_constants_fragment_pure_def
    pp_t_constants_unary_pure_def pp_t_idneg_unary_pure_def
  using pp_t_eqv_reflexive[OF pp_t_negation_operator_in_domain]
  by blast

lemma pp_t_constants_constant_is_pure[simp]:
  "pp_t_constants_fragment_pure pp_t_constants_unary_type
    w (pp_t_constant_operator b)"
proof (cases b)
  case True
  have reflexive:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_constant_operator True) (pp_t_constant_operator True)"
    by (rule pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain])
  show ?thesis
    apply (subst True)
    unfolding pp_t_constants_fragment_pure_def
      pp_t_constants_unary_pure_def
    apply (rule disjI2)
    apply (rule disjI1)
    apply (rule conjI)
     apply (rule refl)
    apply (rule disjI2)
    apply (rule disjI1)
    by (rule reflexive)
next
  case False
  have reflexive:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_constant_operator False) (pp_t_constant_operator False)"
    by (rule pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain])
  show ?thesis
    apply (subst False)
    unfolding pp_t_constants_fragment_pure_def
      pp_t_constants_unary_pure_def
    apply (rule disjI2)
    apply (rule disjI1)
    apply (rule conjI)
     apply (rule refl)
    apply (rule disjI2)
    apply (rule disjI2)
    by (rule reflexive)
qed

lemma pp_t_constants_classifier_is_pure[simp]:
  "pp_t_constants_fragment_pure pp_t_constants_classifier_type
    w pp_t_constants_stock_classifier"
  unfolding pp_t_constants_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_constants_stock_classifier_in_domain]
  by blast

lemma pp_t_constants_fragment_pure_Prop_iff:
  "pp_t_constants_fragment_pure Prop w P
    \<longleftrightarrow>
    (pp_t_eqv Prop w (pp_zf_truth True) P
      \<or> pp_t_eqv Prop w (pp_zf_truth False) P)"
  unfolding pp_t_constants_fragment_pure_def by simp

lemma pp_t_constants_Prop_pure_eq_idneg:
  "pp_t_constants_fragment_pure Prop w P
    \<longleftrightarrow> pp_t_idneg_fragment_pure Prop w P"
  unfolding pp_t_constants_fragment_pure_def
    pp_t_idneg_fragment_pure_def by simp

lemma pp_t_constants_fragment_pure_unary_iff:
  "pp_t_constants_fragment_pure pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_constants_unary_pure w X"
  unfolding pp_t_constants_fragment_pure_def by simp

lemma pp_t_constants_fragment_pure_respects:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> w x y"
    and pure: "pp_t_constants_fragment_pure \<sigma> w x"
  shows "pp_t_constants_fragment_pure \<sigma> w y"
proof -
  have future: "prefix w w" by simp
  have iff:
      "pp_t_constants_fragment_pure \<sigma> w x
        \<longleftrightarrow>
       pp_t_constants_fragment_pure \<sigma> w y"
    using pp_t_constants_fragment_pure_admissible
      x y xy future
    unfolding pp_t_predicate_admissible_def
    by blast
  show ?thesis using iff pure by blast
qed

lemma pp_t_constants_stock_classifier_on_pure:
  assumes x: "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and pure: "pp_t_constants_unary_pure w x"
  shows "pp_t_eqv Prop w
    (pp_t_constants_stock_classifier \<acute> x)
    (pp_zf_truth True)"
proof -
  have pure_future:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_constants_unary_pure v x"
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    from pure consider
        (old) "pp_t_idneg_unary_pure w x"
      | (truth)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator True) x"
      | (falsity)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator False) x"
      unfolding pp_t_constants_unary_pure_def by blast
    then show "pp_t_constants_unary_pure v x"
    proof cases
      case old
      have "pp_t_idneg_unary_pure v x"
        using old pp_t_eqv_persistent[OF _ future]
        unfolding pp_t_idneg_unary_pure_def by blast
      then show ?thesis
        unfolding pp_t_constants_unary_pure_def by blast
    next
      case truth
      have "pp_t_eqv pp_t_constants_unary_type
          v (pp_t_constant_operator True) x"
        by (rule pp_t_eqv_persistent[OF truth future])
      then show ?thesis
        unfolding pp_t_constants_unary_pure_def by blast
    next
      case falsity
      have "pp_t_eqv pp_t_constants_unary_type
          v (pp_t_constant_operator False) x"
        by (rule pp_t_eqv_persistent[OF falsity future])
      then show ?thesis
        unfolding pp_t_constants_unary_pure_def by blast
    qed
  qed
  show ?thesis
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_constants_stock_classifier_def
    using pp_t_classifier_holds[
      OF x, of pp_t_constants_unary_pure]
      pure_future
    by simp
qed

lemma pp_t_constants_idneg_application:
  assumes f: "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and pure_f: "pp_t_idneg_unary_pure w f"
    and pure_x: "pp_t_constants_fragment_pure Prop w x"
  shows "pp_t_constants_fragment_pure Prop w (f \<acute> x)"
proof -
  have old_f:
      "pp_t_idneg_fragment_pure pp_t_idneg_unary_type w f"
    using pure_f
    unfolding pp_t_idneg_fragment_pure_def by simp
  have old_x: "pp_t_idneg_fragment_pure Prop w x"
    using pure_x
    unfolding pp_t_constants_Prop_pure_eq_idneg .
  have old_result:
      "pp_t_idneg_fragment_pure Prop w (f \<acute> x)"
    using pp_t_idneg_fragment_application[
      OF f x old_f old_x] .
  show ?thesis
    using old_result
    unfolding pp_t_constants_Prop_pure_eq_idneg .
qed

lemma pp_t_constants_constant_application:
  assumes f: "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator b) f"
  shows "pp_t_constants_fragment_pure Prop w (f \<acute> x)"
proof -
  have x_refl: "pp_t_eqv Prop w x x"
    using pp_t_eqv_reflexive[OF x] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_constant_operator b \<acute> x) (f \<acute> x)"
    using pp_t_app_respects[
      OF representative x x x_refl] .
  have constant_eval:
      "pp_t_constant_operator b \<acute> x = pp_zf_truth b"
    by (rule pp_t_constant_operator_apply[OF x])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth b) (f \<acute> x)"
    using applications unfolding constant_eval .
  show ?thesis
    unfolding pp_t_constants_fragment_pure_Prop_iff
    using result by (cases b) simp_all
qed

lemma pp_t_constants_classifier_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_classifier_type)"
    and x: "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_constants_stock_classifier f"
    and pure_x: "pp_t_constants_unary_pure w x"
  shows "pp_t_constants_fragment_pure Prop w (f \<acute> x)"
proof -
  have x_refl:
      "pp_t_eqv pp_t_constants_unary_type w x x"
    using pp_t_eqv_reflexive[OF x] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_constants_stock_classifier \<acute> x)
        (f \<acute> x)"
    using pp_t_app_respects[
      OF representative x x x_refl] .
  have result:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (f \<acute> x)"
    using pp_t_constants_stock_classifier_on_pure[
        OF x pure_x]
      applications pp_t_truth_in_domain
      pp_t_app_closed[
        OF pp_t_constants_stock_classifier_in_domain x]
      pp_t_app_closed[OF f x]
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_constants_fragment_pure_Prop_iff
    using result by blast
qed

lemma pp_t_constants_unary_application:
  assumes f: "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and pure_f: "pp_t_constants_unary_pure w f"
    and pure_x: "pp_t_constants_fragment_pure Prop w x"
  shows "pp_t_constants_fragment_pure Prop w (f \<acute> x)"
proof -
  from pure_f consider
      (old) "pp_t_idneg_unary_pure w f"
    | (truth)
        "pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator True) f"
    | (falsity)
        "pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator False) f"
    unfolding pp_t_constants_unary_pure_def by blast
  then show ?thesis
  proof cases
    case old
    show ?thesis
      by (rule pp_t_constants_idneg_application[
        OF f x old pure_x])
  next
    case truth
    show ?thesis
      by (rule pp_t_constants_constant_application[
        OF f x truth])
  next
    case falsity
    show ?thesis
      by (rule pp_t_constants_constant_application[
        OF f x falsity])
  qed
qed

lemma pp_t_constants_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_constants_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x: "pp_t_constants_fragment_pure \<sigma> w x"
  shows "pp_t_constants_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (unary)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_constants_unary_pure w f"
    | (classifier)
        "\<sigma> = pp_t_constants_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_constants_stock_classifier f"
    unfolding pp_t_constants_fragment_pure_def
    by auto
  then show ?thesis
  proof cases
    case unary
    show ?thesis
      using pp_t_constants_unary_application[
        OF _ _ unary(3)] f x pure_x unary
      by simp
  next
    case classifier
    have x_pure: "pp_t_constants_unary_pure w x"
      using pure_x classifier
      unfolding pp_t_constants_fragment_pure_def by simp
    show ?thesis
      using pp_t_constants_classifier_application[
        OF _ _ classifier(3) x_pure] f x classifier
      by simp
  qed
qed

section \<open>The moving-fundamental interpretation\<close>

interpretation ConstantsFragment:
  pp_t_moving_internal_parameters pp_t_constants_fragment_pure
  by standard (rule pp_t_constants_fragment_pure_admissible)

abbreviation pp_t_constants_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_constants_fragment_constants \<equiv>
    pp_t_moving_internal_constants pp_t_constants_fragment_pure"

lemma pp_t_constants_identity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type prop_id)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using ConstantsFragment.pp_t_moving_eval_pure_holds[
      OF typed_prop_id env, of w]
    by simp
qed

theorem pp_t_constants_identity_purity_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type prop_id)"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_identity_purity_holds by blast

lemma pp_t_constants_negation_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type pp_negation_operator)) w"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator : pp_t_constants_unary_type"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using ConstantsFragment.pp_t_moving_eval_pure_holds[
      OF typed env, of w]
    by simp
qed

theorem pp_t_constants_negation_purity_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type pp_negation_operator)"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_negation_purity_holds by blast

lemma pp_t_constants_constant_truth_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        (pp_constant_operator ObjTrue))) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_operator ObjTrue :
        pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjTrue]
    unfolding pp_unary_ty_def .
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using ConstantsFragment.pp_t_moving_eval_pure_holds[
      OF typed env, of w]
    by simp
qed

theorem pp_t_constants_constant_truth_purity_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjTrue))"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_constant_truth_purity_holds by blast

lemma pp_t_constants_constant_falsity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        (pp_constant_operator ObjFalse))) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_operator ObjFalse :
        pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjFalse]
    unfolding pp_unary_ty_def .
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using ConstantsFragment.pp_t_moving_eval_pure_holds[
      OF typed env, of w]
    by simp
qed

theorem pp_t_constants_constant_falsity_purity_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjFalse))"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_constant_falsity_purity_holds by blast

lemma pp_t_constants_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho> pp_target_PP) w"
proof -
  have classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_constants_fragment_pure pp_t_constants_unary_type) =
        pp_t_constants_stock_classifier"
    unfolding pp_t_constants_stock_classifier_def
      pp_t_constants_fragment_pure_def
    by simp
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_constants_stock_classifier_in_domain,
      of "pp_t_constants_fragment_pure
        pp_t_constants_classifier_type" w]
    by (simp add: classifier)
qed

theorem pp_t_constants_target_PP_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_target_PP_holds by blast

lemma pp_t_constants_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_constants_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_constants_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_constants_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_constants_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_constants_application_closure_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ConstantsFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      ConstantsFragment.MovingTreeConstants.pp_t_den_def
      pp_t_constants_application_closure_holds_iff
    using pp_t_constants_fragment_application by blast
qed

theorem pp_t_constants_unique_fundamental_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using ConstantsFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_constants_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using ConstantsFragment.pp_t_moving_no_fundamentals_holds[
    OF assms]
  by blast

section \<open>Zeroary Recombination and Exhaustion\<close>

lemma pp_t_constants_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
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
          (pp_t_eval pp_t_constants_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_constants_fragment_pure Prop w P"
      using ConstantsFragment.pp_t_moving_eval_pure_holds[
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
        (pp_t_eval pp_t_constants_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_constants_pure_true_implies_necessary:
  assumes P: "Elem P (pp_t_domain Prop)"
    and pure: "pp_t_constants_fragment_pure Prop w P"
    and true_now: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  from pure consider
      (truth) "pp_t_eqv Prop w (pp_zf_truth True) P"
    | (falsity) "pp_t_eqv Prop w (pp_zf_truth False) P"
    unfolding pp_t_constants_fragment_pure_Prop_iff by blast
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

lemma pp_t_constants_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
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
          (pp_t_eval pp_t_constants_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_constants_fragment_pure Prop w P"
      using ConstantsFragment.pp_t_moving_eval_pure_holds[
        OF var_type extended, of w] by simp
    show "pp_t_holds
        (pp_t_eval pp_t_constants_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_constants_pure_true_implies_necessary[OF P]
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_constants_zeroary_recombination_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_zeroary_recombination_holds by blast

theorem pp_t_constants_zeroary_exhaustion_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_zeroary_exhaustion_holds by blast

section \<open>Unary Recombination and Exhaustion\<close>

lemma pp_t_constants_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_constants_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_constants_fragment_pure
            pp_t_constants_unary_type w X
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

lemma pp_t_constants_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_constants_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_constants_fragment_pure
            pp_t_constants_unary_type w X
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

lemma pp_t_constants_identity_class_QLN:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_identity_operator X"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  shows
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    and
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
proof -
  have old_pure:
      "pp_t_idneg_fragment_pure
        pp_t_idneg_unary_type w X"
    using representative
    unfolding pp_t_idneg_fragment_pure_unary_iff
      pp_t_idneg_unary_pure_def
    by blast
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    by (rule pp_t_idneg_fundamental_not_necessary[
      OF X r old_pure fundamental])
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    by (rule pp_t_idneg_not_universally_true[
      OF X old_pure])
  show
    "(\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using not_necessary by blast
  show
    "(\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using not_universal by blast
qed

lemma pp_t_constants_negation_class_QLN:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_negation_operator X"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  shows
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    and
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
proof -
  have old_pure:
      "pp_t_idneg_fragment_pure
        pp_t_idneg_unary_type w X"
    using representative
    unfolding pp_t_idneg_fragment_pure_unary_iff
      pp_t_idneg_unary_pure_def
    by blast
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    by (rule pp_t_idneg_fundamental_not_necessary[
      OF X r old_pure fundamental])
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    by (rule pp_t_idneg_not_universally_true[
      OF X old_pure])
  show
    "(\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using not_necessary by blast
  show
    "(\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using not_universal by blast
qed

lemma pp_t_constants_constant_class_holds_iff:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and q: "Elem q (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator b) X"
    and future: "prefix w v"
  shows "pp_t_holds (X \<acute> q) v \<longleftrightarrow> b"
proof -
  have q_refl: "pp_t_eqv Prop w q q"
    by (rule pp_t_eqv_reflexive[OF q])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_constant_operator b \<acute> q) (X \<acute> q)"
    by (rule pp_t_app_respects[
      OF representative q q q_refl])
  have transfer:
      "pp_t_holds (pp_t_constant_operator b \<acute> q) v
        \<longleftrightarrow> pp_t_holds (X \<acute> q) v"
    by (rule pp_t_prop_eqv_at[OF applications future])
  show ?thesis
    using transfer pp_t_constant_operator_holds[OF q, of b v]
    by blast
qed

lemma pp_t_constants_constant_truth_class_QLN:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator True) X"
  shows
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    and
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
proof -
  have universal:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
  proof (intro allI impI)
    fix q
    assume q: "Elem q (pp_t_domain Prop)"
    have future: "prefix w w" by simp
    show "pp_t_holds (X \<acute> q) w"
      using pp_t_constants_constant_class_holds_iff[
        OF X q representative future]
      by simp
  qed
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    show "pp_t_holds (X \<acute> r) v"
      using pp_t_constants_constant_class_holds_iff[
        OF X r representative future]
      by simp
  qed
  show
    "(\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using universal by blast
  show
    "(\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using necessary by blast
qed

lemma pp_t_constants_constant_falsity_class_QLN:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator False) X"
  shows
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    and
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
proof -
  have current: "prefix w w" by simp
  have r_false: "\<not> pp_t_holds (X \<acute> r) w"
    using pp_t_constants_constant_class_holds_iff[
      OF X r representative current]
    by simp
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using current r_false by blast
  have truth:
      "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have truth_false:
      "\<not> pp_t_holds (X \<acute> pp_zf_truth True) w"
    using pp_t_constants_constant_class_holds_iff[
      OF X truth representative current]
    by simp
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using truth truth_false by blast
  show
    "(\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using not_necessary by blast
  show
    "(\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using not_universal by blast
qed

lemma pp_t_constants_pure_unary_QLN:
  assumes X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_constants_fragment_pure
        pp_t_constants_unary_type w X"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  shows
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    and
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
proof -
  have unary_pure: "pp_t_constants_unary_pure w X"
    using pure
    unfolding pp_t_constants_fragment_pure_unary_iff .
  have classes:
      "pp_t_eqv pp_t_constants_unary_type
          w pp_t_identity_operator X
        \<or> pp_t_eqv pp_t_constants_unary_type
          w pp_t_negation_operator X
        \<or> pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator True) X
        \<or> pp_t_eqv pp_t_constants_unary_type
          w (pp_t_constant_operator False) X"
    using unary_pure
    unfolding pp_t_constants_unary_pure_def
      pp_t_idneg_unary_pure_def
    by blast
  show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
  proof -
    from classes consider
        (identity)
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_identity_operator X"
      | (negation)
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_negation_operator X"
      | (truth)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator True) X"
      | (falsity)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator False) X"
      by blast
    then show ?thesis
    proof cases
      case identity
      show ?thesis
        by (rule pp_t_constants_identity_class_QLN(1)[
          OF X r identity fundamental])
    next
      case negation
      show ?thesis
        by (rule pp_t_constants_negation_class_QLN(1)[
          OF X r negation fundamental])
    next
      case truth
      show ?thesis
        by (rule pp_t_constants_constant_truth_class_QLN(1)[
          OF X r truth])
    next
      case falsity
      show ?thesis
        by (rule pp_t_constants_constant_falsity_class_QLN(1)[
          OF X r falsity])
    qed
  qed
  show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
  proof -
    from classes consider
        (identity)
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_identity_operator X"
      | (negation)
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_negation_operator X"
      | (truth)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator True) X"
      | (falsity)
          "pp_t_eqv pp_t_constants_unary_type
            w (pp_t_constant_operator False) X"
      by blast
    then show ?thesis
    proof cases
      case identity
      show ?thesis
        by (rule pp_t_constants_identity_class_QLN(2)[
          OF X r identity fundamental])
    next
      case negation
      show ?thesis
        by (rule pp_t_constants_negation_class_QLN(2)[
          OF X r negation fundamental])
    next
      case truth
      show ?thesis
        by (rule pp_t_constants_constant_truth_class_QLN(2)[
          OF X r truth])
    next
      case falsity
      show ?thesis
        by (rule pp_t_constants_constant_falsity_class_QLN(2)[
          OF X r falsity])
    qed
  qed
qed

theorem pp_t_constants_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_constants_unary_recombination_holds_iff
  using pp_t_constants_pure_unary_QLN(1)
  by blast

theorem pp_t_constants_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_constants_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_constants_unary_exhaustion_holds_iff
  using pp_t_constants_pure_unary_QLN(2)
  by blast

theorem pp_t_constants_unary_recombination_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_unary_recombination_holds by blast

theorem pp_t_constants_unary_exhaustion_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConstantsFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_constants_unary_exhaustion_holds by blast

section \<open>Modalized Functionality and consistency\<close>

lemma pp_t_constants_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_constants_fragment_constants \<rho>
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

theorem pp_t_constants_modalized_functionality_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ConstantsFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      ConstantsFragment.MovingTreeConstants.pp_t_den_def
      pp_t_constants_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

definition pp_logical_constants_fragment_PP_axioms ::
    "oterm set"
where
  "pp_logical_constants_fragment_PP_axioms =
    insert
      (pp_pure pp_unary_ty (pp_constant_operator ObjTrue))
      (insert
        (pp_pure pp_unary_ty (pp_constant_operator ObjFalse))
        pp_identity_negation_fragment_PP_axioms)"

theorem pp_t_logical_constants_fragment_PP_gvalid:
  "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_logical_constants_fragment_PP_axioms"
  unfolding
    ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_logical_constants_fragment_PP_axioms"
  from A consider
      (constant_truth)
        "A = pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue)"
    | (constant_falsity)
        "A = pp_pure pp_unary_ty
          (pp_constant_operator ObjFalse)"
    | (identity_purity)
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
    unfolding pp_logical_constants_fragment_PP_axioms_def
      pp_identity_negation_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show
      "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case constant_truth
    then show ?thesis
      using pp_t_constants_constant_truth_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_falsity
    then show ?thesis
      using pp_t_constants_constant_falsity_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case identity_purity
    then show ?thesis
      using pp_t_constants_identity_purity_gvalid by simp
  next
    case negation_purity
    then show ?thesis
      using pp_t_constants_negation_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_constants_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_constants_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_constants_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_constants_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_constants_zeroary_recombination_gvalid by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_constants_unary_recombination_gvalid by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_constants_zeroary_exhaustion_gvalid by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_constants_unary_exhaustion_gvalid by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_constants_modalized_functionality_gvalid)
  qed
qed

theorem pp_logical_constants_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_logical_constants_fragment_PP_axioms"
  using
    ConstantsFragment.MovingTreeConstants.pp_t_base_sound
    ConstantsFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_logical_constants_fragment_PP_gvalid
  by (rule
    ConstantsFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_logical_constants_fragment_consistent:
  assumes
    "U \<subseteq> pp_logical_constants_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_logical_constants_fragment_PP_gvalid
    unfolding
      ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      ConstantsFragment.MovingTreeConstants.pp_t_base_sound
      ConstantsFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      ConstantsFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
