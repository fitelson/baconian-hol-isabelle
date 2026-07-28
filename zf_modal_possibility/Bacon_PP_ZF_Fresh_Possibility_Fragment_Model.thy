theory Bacon_PP_ZF_Fresh_Possibility_Fragment_Model
  imports
    "Higher_Order_Metaphysics_PP_ZF_Necessity.Bacon_PP_ZF_Fresh_Necessity_Fragment_Model"
begin

section \<open>The possibility operator\<close>

definition pp_possibility_operator :: oterm where
  "pp_possibility_operator =
    Lam Prop (\<diamond>\<^sub>o (Var 0))"

lemma pp_possibility_operator_typed:
  "[] \<turnstile> pp_possibility_operator : pp_unary_ty"
  unfolding pp_possibility_operator_def pp_unary_ty_def
  by (intro has_type.Lam typed_ObjDiamond has_type.Var)
    (simp add: lookup_def)

lemma pp_possibility_operator_logical:
  "pp_logical_vocabulary pp_possibility_operator"
  by (simp add: pp_logical_vocabulary_def
      pp_possibility_operator_def ObjDiamond_def
      ObjBox_def ObjTrue_def)

lemma pp_possibility_operator_purity_axiom_in_schema:
  "pp_pure pp_unary_ty pp_possibility_operator
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_possibility_operator : pp_unary_ty"
    by (rule pp_possibility_operator_typed)
  show "pp_logical_vocabulary pp_possibility_operator"
    by (rule pp_possibility_operator_logical)
  show "pp_pure pp_unary_ty pp_possibility_operator =
      pp_pure pp_unary_ty pp_possibility_operator"
    by simp
qed

definition pp_t_possibility_predicate ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_possibility_predicate w p \<longleftrightarrow>
    (\<exists>v. prefix w v \<and> pp_t_holds p v)"

lemma pp_t_possibility_predicate_admissible:
  "pp_t_predicate_admissible Prop
    pp_t_possibility_predicate"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w x y u
  assume x: "Elem x (pp_t_domain Prop)"
    and y: "Elem y (pp_t_domain Prop)"
    and xy: "pp_t_eqv Prop w x y"
    and future: "prefix w u"
  have xy_u: "pp_t_eqv Prop u x y"
    by (rule pp_t_eqv_persistent[OF xy future])
  show "pp_t_possibility_predicate u x =
      pp_t_possibility_predicate u y"
    unfolding pp_t_possibility_predicate_def
  proof
    assume "\<exists>v. prefix u v \<and> pp_t_holds x v"
    then obtain v where uv: "prefix u v"
      and xv: "pp_t_holds x v"
      by blast
    have at_v: "pp_t_holds x v \<longleftrightarrow> pp_t_holds y v"
      by (rule pp_t_prop_eqv_at[OF xy_u uv])
    show "\<exists>v. prefix u v \<and> pp_t_holds y v"
      using uv xv at_v by blast
  next
    assume "\<exists>v. prefix u v \<and> pp_t_holds y v"
    then obtain v where uv: "prefix u v"
      and yv: "pp_t_holds y v"
      by blast
    have at_v: "pp_t_holds x v \<longleftrightarrow> pp_t_holds y v"
      by (rule pp_t_prop_eqv_at[OF xy_u uv])
    show "\<exists>v. prefix u v \<and> pp_t_holds x v"
      using uv yv at_v by blast
  qed
qed

definition pp_t_possibility_operator :: ZF where
  "pp_t_possibility_operator =
    pp_t_classifier Prop pp_t_possibility_predicate"

lemma pp_t_possibility_operator_in_domain:
  "Elem pp_t_possibility_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_possibility_operator_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_possibility_predicate_admissible)

lemma pp_t_possibility_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_possibility_operator \<acute> p) w
    \<longleftrightarrow>
      (\<exists>v. prefix w v \<and> pp_t_holds p v)"
  unfolding pp_t_possibility_operator_def
  using pp_t_classifier_holds[
    OF p, of pp_t_possibility_predicate w]
  by (simp only: pp_t_possibility_predicate_def)

lemma pp_t_eval_possibility_operator:
  "pp_t_eval C \<rho> pp_possibility_operator =
    pp_t_possibility_operator"
  unfolding pp_possibility_operator_def
    pp_t_possibility_operator_def pp_t_classifier_def
  apply (simp only: pp_t_eval.simps Lambda_ext)
  apply (intro conjI allI impI)
   apply simp
  apply (rule pp_t_prop_ext)
  subgoal
    unfolding ObjDiamond_def ObjBox_def
    by (simp only: pp_t_eval.simps; rule pp_t_prop_in_domain)
  subgoal
    by (rule pp_t_prop_in_domain)
  subgoal for p w
    using pp_t_eval_ObjDiamond_holds[
      of C "extend_env p \<rho>" "Var 0" w]
    by (simp add: pp_t_possibility_predicate_def)
  done

lemma pp_t_possibility_truth_eqv:
  "pp_t_eqv Prop w
    (pp_t_possibility_operator \<acute> pp_zf_truth b)
    (pp_zf_truth b)"
  unfolding pp_t_eqv.simps
  using pp_t_possibility_operator_holds[
    OF pp_t_truth_in_domain, of b]
  by (cases b) auto

section \<open>The possibility-closed pure stock\<close>

definition pp_t_possibility_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_possibility_unary_pure w x \<longleftrightarrow>
    pp_t_necessity_fragment_pure
      pp_t_constants_unary_type w x
    \<or>
    pp_t_eqv pp_t_constants_unary_type
      w pp_t_possibility_operator x"

lemma pp_t_possibility_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    pp_t_possibility_unary_pure"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (pp_t_necessity_fragment_pure
          pp_t_constants_unary_type)"
    by (rule pp_t_necessity_fragment_pure_admissible)
  have possibility:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_possibility_operator_in_domain] .
  show ?thesis
    using old possibility
    unfolding pp_t_predicate_admissible_def
      pp_t_possibility_unary_pure_def
    by blast
qed

definition pp_t_possibility_stock_classifier :: ZF where
  "pp_t_possibility_stock_classifier =
    pp_t_classifier pp_t_constants_unary_type
      pp_t_possibility_unary_pure"

lemma pp_t_possibility_stock_classifier_in_domain:
  "Elem pp_t_possibility_stock_classifier
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_possibility_stock_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_possibility_unary_pure_admissible)

definition pp_t_possibility_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_possibility_fragment_pure \<sigma> w x \<longleftrightarrow>
    (pp_t_necessity_fragment_pure \<sigma> w x
      \<and> \<sigma> \<noteq> pp_t_constants_classifier_type)
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> pp_t_eqv pp_t_constants_unary_type
        w pp_t_possibility_operator x)
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type
        w pp_t_possibility_stock_classifier x)"

lemma pp_t_possibility_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_possibility_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_necessity_fragment_pure \<sigma>)"
    by (rule pp_t_necessity_fragment_pure_admissible)
  have possibility:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_possibility_operator_in_domain] .
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type
          w pp_t_possibility_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_possibility_stock_classifier_in_domain] .
  show ?thesis
    unfolding pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_eqv \<sigma> w x y"
      and future: "prefix w v"
    have old_iff:
        "pp_t_necessity_fragment_pure \<sigma> v x
          \<longleftrightarrow>
         pp_t_necessity_fragment_pure \<sigma> v y"
      using old x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have possibility_iff:
        "\<sigma> = pp_t_constants_unary_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_possibility_operator x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_possibility_operator y"
      using possibility x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have classifier_iff:
        "\<sigma> = pp_t_constants_classifier_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_classifier_type
            v pp_t_possibility_stock_classifier x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_classifier_type
            v pp_t_possibility_stock_classifier y"
      using classifier x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    show "pp_t_possibility_fragment_pure \<sigma> v x =
        pp_t_possibility_fragment_pure \<sigma> v y"
      unfolding pp_t_possibility_fragment_pure_def
      using old_iff possibility_iff classifier_iff by blast
  qed
qed

lemma pp_t_possibility_inherits_old_pure:
  assumes old: "pp_t_necessity_fragment_pure \<sigma> w x"
    and not_classifier:
      "\<sigma> \<noteq> pp_t_constants_classifier_type"
  shows "pp_t_possibility_fragment_pure \<sigma> w x"
  unfolding pp_t_possibility_fragment_pure_def
  using old not_classifier by blast

lemma pp_t_possibility_operator_is_pure[simp]:
  "pp_t_possibility_fragment_pure
    pp_t_constants_unary_type w pp_t_possibility_operator"
  unfolding pp_t_possibility_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_possibility_operator_in_domain]
  by blast

lemma pp_t_possibility_classifier_is_pure[simp]:
  "pp_t_possibility_fragment_pure
    pp_t_constants_classifier_type w
    pp_t_possibility_stock_classifier"
  unfolding pp_t_possibility_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_possibility_stock_classifier_in_domain]
  by blast

lemma pp_t_possibility_pure_Prop_iff:
  "pp_t_possibility_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_necessity_fragment_pure Prop w P"
  unfolding pp_t_possibility_fragment_pure_def by simp

lemma pp_t_possibility_pure_unary_iff:
  "pp_t_possibility_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_possibility_unary_pure w X"
  unfolding pp_t_possibility_fragment_pure_def
    pp_t_possibility_unary_pure_def
  by simp

lemma pp_t_possibility_pure_classifier_iff:
  "pp_t_possibility_fragment_pure
      pp_t_constants_classifier_type w X
    \<longleftrightarrow>
    pp_t_eqv pp_t_constants_classifier_type
      w pp_t_possibility_stock_classifier X"
  unfolding pp_t_possibility_fragment_pure_def by simp

lemma pp_t_necessity_pure_function_from_unary:
  assumes pure:
      "pp_t_necessity_fragment_pure
        (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
  shows "\<tau> = Prop"
  using pure
  unfolding pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
  by (cases \<tau>) auto

lemma pp_t_necessity_no_pure_function_from_classifier:
  "\<not> pp_t_necessity_fragment_pure
    (pp_t_constants_classifier_type \<rightarrow>\<^sub>o \<tau>) w f"
  unfolding pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
  by (cases \<tau>) auto

lemma pp_t_possibility_old_input:
  assumes pure_f:
      "pp_t_necessity_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and retained:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
        \<noteq> pp_t_constants_classifier_type"
    and pure_x:
      "pp_t_possibility_fragment_pure \<sigma> w x"
  shows "pp_t_necessity_fragment_pure \<sigma> w x"
proof -
  from pure_x consider
      (old) "pp_t_necessity_fragment_pure \<sigma> w x"
    | (possibility)
        "\<sigma> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator x"
    | (classifier)
        "\<sigma> = pp_t_constants_classifier_type"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_possibility_stock_classifier x"
    unfolding pp_t_possibility_fragment_pure_def
    by blast
  then show ?thesis
  proof cases
    case old
    then show ?thesis .
  next
    case possibility
    have pure_unary:
        "pp_t_necessity_fragment_pure
          (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
      using pure_f possibility by simp
    have tau: "\<tau> = Prop"
      by (rule pp_t_necessity_pure_function_from_unary[
        OF pure_unary])
    have False
      using retained possibility tau by simp
    then show ?thesis by blast
  next
    case classifier
    have False
      using pp_t_necessity_no_pure_function_from_classifier[
        of \<tau> w f] pure_f classifier
      by simp
    then show ?thesis by blast
  qed
qed

lemma pp_t_possibility_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possibility_operator f"
    and pure_x:
      "pp_t_possibility_fragment_pure Prop w x"
  shows "pp_t_possibility_fragment_pure Prop w (f \<acute> x)"
proof -
  have x_class:
      "pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x"
    using pure_x
    unfolding pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff .
  then obtain b where xb:
      "pp_t_eqv Prop w (pp_zf_truth b) x"
    by (metis (full_types) bool.exhaust)
  have applications:
      "pp_t_eqv Prop w
        (pp_t_possibility_operator \<acute> pp_zf_truth b)
        (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative pp_t_truth_in_domain x xb])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth b) (f \<acute> x)"
    using pp_t_possibility_truth_eqv[
        of w b]
      pp_t_app_closed[
        OF pp_t_possibility_operator_in_domain
          pp_t_truth_in_domain]
      pp_t_app_closed[OF f x]
      pp_t_truth_in_domain applications
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by (cases b) simp_all
qed

lemma pp_t_possibility_unary_pure_persistent:
  assumes pure: "pp_t_possibility_unary_pure w x"
    and future: "prefix w v"
  shows "pp_t_possibility_unary_pure v x"
  using pure pp_t_eqv_persistent[OF _ future]
  unfolding pp_t_possibility_unary_pure_def
    pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
    pp_t_constants_unary_pure_def
    pp_t_idneg_unary_pure_def
  by blast

lemma pp_t_possibility_stock_classifier_on_pure:
  assumes x:
      "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and pure: "pp_t_possibility_unary_pure w x"
  shows "pp_t_eqv Prop w
    (pp_t_possibility_stock_classifier \<acute> x)
    (pp_zf_truth True)"
proof -
  have pure_future:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_possibility_unary_pure v x"
    using pp_t_possibility_unary_pure_persistent[
      OF pure] by blast
  show ?thesis
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_possibility_stock_classifier_def
    using pp_t_classifier_holds[
      OF x, of pp_t_possibility_unary_pure]
      pure_future
    by simp
qed

lemma pp_t_possibility_classifier_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_classifier_type)"
    and x:
      "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_possibility_stock_classifier f"
    and pure_x: "pp_t_possibility_unary_pure w x"
  shows "pp_t_possibility_fragment_pure Prop w (f \<acute> x)"
proof -
  have xx:
      "pp_t_eqv pp_t_constants_unary_type w x x"
    by (rule pp_t_eqv_reflexive[OF x])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_possibility_stock_classifier \<acute> x)
        (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative x x xx])
  have result:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (f \<acute> x)"
    using pp_t_possibility_stock_classifier_on_pure[
        OF x pure_x]
      applications pp_t_truth_in_domain
      pp_t_app_closed[
        OF pp_t_possibility_stock_classifier_in_domain x]
      pp_t_app_closed[OF f x]
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by blast
qed

lemma pp_t_possibility_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_possibility_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_possibility_fragment_pure \<sigma> w x"
  shows "pp_t_possibility_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_necessity_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
        "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<noteq> pp_t_constants_classifier_type"
    | (possibility)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator f"
    | (classifier)
        "\<sigma> = pp_t_constants_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_possibility_stock_classifier f"
    unfolding pp_t_possibility_fragment_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_necessity_fragment_pure \<sigma> w x"
      by (rule pp_t_possibility_old_input[
        OF old pure_x])
    have old_result:
        "pp_t_necessity_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_necessity_fragment_application[
        OF f x old(1) old_x])
    have not_classifier:
        "\<tau> \<noteq> pp_t_constants_classifier_type"
    proof
      assume tau:
          "\<tau> = pp_t_constants_classifier_type"
      have no_old:
          "\<not> pp_t_necessity_fragment_pure
            (\<sigma> \<rightarrow>\<^sub>o
              pp_t_constants_classifier_type) w f"
        unfolding pp_t_necessity_fragment_pure_def
          pp_t_binary_truth_fragment_pure_def
          pp_t_conjunction_fragment_pure_def
          pp_t_constant_builder_fragment_pure_def
          pp_t_constants_fragment_pure_def
        by (cases \<sigma>) auto
      show False
        using no_old old(1) unfolding tau by blast
    qed
    show ?thesis
      by (rule pp_t_possibility_inherits_old_pure[
        OF old_result not_classifier])
  next
    case possibility
    show ?thesis
      using pp_t_possibility_application[
        OF _ _ possibility(3)] f x pure_x possibility
      by simp
  next
    case classifier
    have pure_unary_fragment:
        "pp_t_possibility_fragment_pure
          pp_t_constants_unary_type w x"
      using pure_x classifier by simp
    have unary_pure:
        "pp_t_possibility_unary_pure w x"
      using pp_t_possibility_pure_unary_iff[
        of w x] pure_unary_fragment
      by blast
    show ?thesis
      using pp_t_possibility_classifier_application[
        OF _ _ classifier(3) unary_pure] f x classifier
      by simp
  qed
qed

section \<open>The moving-fundamental interpretation\<close>

interpretation PossibilityFragment:
  pp_t_moving_internal_parameters
    pp_t_possibility_fragment_pure
  by standard
    (rule pp_t_possibility_fragment_pure_admissible)

abbreviation pp_t_possibility_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_possibility_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_possibility_fragment_pure"

lemma pp_t_possibility_old_purity_holds:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and representative: "Elem a (pp_t_domain \<sigma>)"
    and related:
      "pp_t_eqv \<sigma> w a
        (pp_t_eval pp_t_possibility_fragment_constants \<rho> M)"
    and old_pure:
      "pp_t_necessity_fragment_pure \<sigma> w a"
    and not_classifier:
      "\<sigma> \<noteq> pp_t_constants_classifier_type"
  shows "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure \<sigma> M)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have evaluated:
      "Elem
        (pp_t_eval pp_t_possibility_fragment_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using
      PossibilityFragment.MovingTreeConstants.pp_t_eval_type[
        OF typed env]
    by (simp add: pp_t_dom_def)
  have pure_a:
      "pp_t_possibility_fragment_pure \<sigma> w a"
    by (rule pp_t_possibility_inherits_old_pure[
      OF old_pure not_classifier])
  have same_purity:
      "pp_t_possibility_fragment_pure \<sigma> w a
        \<longleftrightarrow>
       pp_t_possibility_fragment_pure \<sigma> w
        (pp_t_eval pp_t_possibility_fragment_constants \<rho> M)"
    using pp_t_possibility_fragment_pure_admissible
      representative evaluated related
    unfolding pp_t_predicate_admissible_def
    by simp
  have pure_evaluated:
      "pp_t_possibility_fragment_pure \<sigma> w
        (pp_t_eval pp_t_possibility_fragment_constants \<rho> M)"
    using same_purity pure_a by blast
  show ?thesis
    using
      PossibilityFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure_evaluated
    by simp
qed

lemma pp_t_possibility_truth_function_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        (pp_truth_function_builder F))) w"
proof -
  have typed:
      "[] \<turnstile> pp_truth_function_builder F :
        pp_t_binary_truth_builder_type"
    using typed_pp_truth_function_builder[
      of "[]" F]
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have representative:
      "Elem (pp_t_truth_function_builder F)
        (pp_t_domain pp_t_binary_truth_builder_type)"
    by (rule pp_t_truth_function_builder_in_domain)
  have related:
      "pp_t_eqv pp_t_binary_truth_builder_type w
        (pp_t_truth_function_builder F)
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          (pp_truth_function_builder F))"
    by (rule pp_t_eval_truth_function_builder_eqv[
      OF PossibilityFragment.MovingTreeConstants.C_typed env])
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_binary_truth_builder_type w
        (pp_t_truth_function_builder F)"
    by (rule pp_t_necessity_inherits_old_pure[
      OF pp_t_truth_function_is_pure])
      simp
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed representative related old_pure])
      simp
qed

theorem pp_t_possibility_truth_function_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type
      (pp_truth_function_builder F))"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_truth_function_purity_holds by blast

lemma pp_t_possibility_conjunction_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        pp_conjunction_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_conjunction_builder :
        pp_t_binary_truth_builder_type"
    using typed_pp_conjunction_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have representative:
      "Elem pp_t_conjunction_builder
        (pp_t_domain pp_t_binary_truth_builder_type)"
    by (rule pp_t_conjunction_builder_in_domain)
  have related:
      "pp_t_eqv pp_t_binary_truth_builder_type w
        pp_t_conjunction_builder
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          pp_conjunction_builder)"
    apply (simp only: pp_t_eval_conjunction_builder)
    by (rule pp_t_eqv_reflexive[OF representative])
  have binary_pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_conjunction_builder"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (rule pp_t_conjunction_is_pure)
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_conjunction_builder"
    by (rule pp_t_necessity_inherits_old_pure[
      OF binary_pure])
      simp
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed representative related old_pure])
      simp
qed

theorem pp_t_possibility_conjunction_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type
      pp_conjunction_builder)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_conjunction_purity_holds by blast

lemma pp_t_possibility_constant_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_binary_truth_builder_type
        pp_constant_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_builder :
        pp_t_binary_truth_builder_type"
    using typed_pp_constant_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have representative:
      "Elem pp_t_constant_builder
        (pp_t_domain pp_t_binary_truth_builder_type)"
    by (rule pp_t_constant_builder_in_domain)
  have related:
      "pp_t_eqv pp_t_binary_truth_builder_type w
        pp_t_constant_builder
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          pp_constant_builder)"
    apply (simp only: pp_t_eval_constant_builder)
    by (rule pp_t_eqv_reflexive[OF representative])
  have binary_pure:
      "pp_t_binary_truth_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_constant_builder"
    by (rule pp_t_binary_truth_inherits_old_pure)
      (unfold pp_t_conjunction_fragment_pure_def,
       rule disjI1, rule pp_t_constant_builder_is_pure)
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_binary_truth_builder_type w pp_t_constant_builder"
    by (rule pp_t_necessity_inherits_old_pure[
      OF binary_pure])
      simp
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed representative related old_pure])
      simp
qed

theorem pp_t_possibility_constant_builder_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_binary_truth_builder_type
      pp_constant_builder)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_constant_builder_purity_holds by blast

lemma pp_t_possibility_identity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type prop_id)) w"
proof -
  have representative:
      "Elem pp_t_identity_operator
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_identity_operator_in_domain)
  have related:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_identity_operator
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          prop_id)"
    apply (simp only: pp_t_eval_prop_id)
    by (rule pp_t_eqv_reflexive[OF representative])
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_constants_unary_type w pp_t_identity_operator"
    apply (rule pp_t_necessity_inherits_old_pure)
     apply (rule pp_t_binary_truth_inherits_old_pure)
     apply (rule pp_t_conjunction_inherits_constants_pure)
     apply (rule pp_t_constants_identity_is_pure)
    apply simp
    done
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed_prop_id representative related old_pure])
      simp
qed

theorem pp_t_possibility_identity_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type prop_id)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_identity_purity_holds by blast

lemma pp_t_possibility_negation_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_negation_operator)) w"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator :
        pp_t_constants_unary_type"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have representative:
      "Elem pp_t_negation_operator
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_negation_operator_in_domain)
  have related:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_negation_operator
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          pp_negation_operator)"
    apply (simp only: pp_t_eval_pp_negation_operator)
    by (rule pp_t_eqv_reflexive[OF representative])
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_constants_unary_type w pp_t_negation_operator"
    apply (rule pp_t_necessity_inherits_old_pure)
     apply (rule pp_t_binary_truth_inherits_old_pure)
     apply (rule pp_t_conjunction_inherits_constants_pure)
     apply (rule pp_t_constants_negation_is_pure)
    apply simp
    done
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed representative related old_pure])
      simp
qed

theorem pp_t_possibility_negation_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      pp_negation_operator)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_negation_purity_holds by blast

lemma pp_t_possibility_constant_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        (pp_constant_operator
          (if b then ObjTrue else ObjFalse)))) w"
proof -
  have object_typed:
      "[] \<turnstile>
        (if b then ObjTrue else ObjFalse) : Prop"
    by (cases b)
      (simp_all add: typed_ObjTrue typed_ObjFalse)
  have typed:
      "[] \<turnstile>
        pp_constant_operator (if b then ObjTrue else ObjFalse) :
        pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF object_typed]
    unfolding pp_unary_ty_def .
  have representative:
      "Elem (pp_t_constant_operator b)
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_constant_operator_in_domain)
  have related:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_constant_operator b)
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          (pp_constant_operator
            (if b then ObjTrue else ObjFalse)))"
  proof (cases b)
    case False
    show ?thesis
      apply (simp only: False if_False
        pp_t_eval_constant_falsity_operator)
      by (rule pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain])
  next
    case True
    show ?thesis
      apply (simp only: True if_True
        pp_t_eval_constant_truth_operator)
      by (rule pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain])
  qed
  have old_pure:
      "pp_t_necessity_fragment_pure
        pp_t_constants_unary_type w (pp_t_constant_operator b)"
    apply (rule pp_t_necessity_inherits_old_pure)
     apply (rule pp_t_binary_truth_inherits_old_pure)
     apply (rule pp_t_conjunction_inherits_constants_pure)
     apply (rule pp_t_constants_constant_is_pure)
    apply simp
    done
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF typed representative related old_pure])
      simp
qed

theorem pp_t_possibility_constant_truth_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjTrue))"
proof -
  have holds:
      "\<And>\<rho> w. pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          (pp_pure pp_t_constants_unary_type
            (pp_constant_operator ObjTrue))) w"
    using pp_t_possibility_constant_purity_holds[
      where b=True] by simp
  show ?thesis
    unfolding
      PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
      PossibilityFragment.MovingTreeConstants.pp_t_den_def
    using holds by blast
qed

theorem pp_t_possibility_constant_falsity_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjFalse))"
proof -
  have holds:
      "\<And>\<rho> w. pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          (pp_pure pp_t_constants_unary_type
            (pp_constant_operator ObjFalse))) w"
    using pp_t_possibility_constant_purity_holds[
      where b=False] by simp
  show ?thesis
    unfolding
      PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
      PossibilityFragment.MovingTreeConstants.pp_t_den_def
    using holds by blast
qed

lemma pp_t_possibility_necessity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_zf_eq_truth_operator)) w"
proof -
  have representative:
      "Elem pp_t_necessity_operator
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_necessity_operator_in_domain)
  have related:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_necessity_operator
        (pp_t_eval pp_t_possibility_fragment_constants \<rho>
          pp_zf_eq_truth_operator)"
    apply (simp only: pp_t_eval_eq_truth_logical_operator)
    by (rule pp_t_eqv_reflexive[OF representative])
  show ?thesis
    by (rule pp_t_possibility_old_purity_holds[
      OF pp_zf_eq_truth_operator_typed representative
        related pp_t_necessity_operator_is_pure])
      simp
qed

theorem pp_t_possibility_necessity_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      pp_zf_eq_truth_operator)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_necessity_purity_holds by blast

lemma pp_t_possibility_operator_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_possibility_operator)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using
      PossibilityFragment.pp_t_moving_eval_pure_holds[
        OF pp_possibility_operator_typed env, of w]
      pp_t_possibility_operator_is_pure
    by (simp add: pp_unary_ty_def
      pp_t_eval_possibility_operator)
qed

theorem pp_t_possibility_operator_purity_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      pp_possibility_operator)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_operator_purity_holds by blast

section \<open>PP, application closure, and fundamentality\<close>

lemma pp_t_possibility_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_possibility_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_possibility_stock_classifier"
    unfolding pp_t_possibility_stock_classifier_def
      pp_t_classifier_def
    by (simp add: pp_t_possibility_pure_unary_iff)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_possibility_stock_classifier_in_domain,
      of "pp_t_possibility_fragment_pure
        pp_t_constants_classifier_type" w]
      pp_t_possibility_classifier_is_pure
    by (simp add: unary_classifier)
qed

theorem pp_t_possibility_target_PP_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_target_PP_holds by blast

lemma pp_t_possibility_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_possibility_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_possibility_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_possibility_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_possibility_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_possibility_application_closure_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (PossibilityFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      PossibilityFragment.MovingTreeConstants.pp_t_den_def
      pp_t_possibility_application_closure_holds_iff
    using pp_t_possibility_fragment_application by blast
qed

theorem pp_t_possibility_unique_fundamental_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using
    PossibilityFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_possibility_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows
    "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
      (pp_no_fundamentals \<sigma>)"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using
    PossibilityFragment.pp_t_moving_no_fundamentals_holds[
      OF assms]
  by blast

section \<open>Recombination, Exhaustion, and functionality\<close>

lemma pp_t_possibility_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
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
    have pure_iff:
        "pp_t_holds
          (pp_t_eval pp_t_possibility_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_possibility_fragment_pure Prop w P"
      using
        PossibilityFragment.pp_t_moving_eval_pure_holds[
          of "[Prop]" "Var 0" Prop
            "extend_env P \<rho>" w]
        extended
      by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
      using pp_t_prop_eqv_at[of w P
        "pp_zf_truth True" w]
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
        pp_t_possibility_pure_Prop_iff
        pp_t_necessity_pure_Prop_iff
        pp_t_binary_truth_pure_Prop_iff
        pp_t_constant_builder_pure_Prop_iff
        pp_t_constants_fragment_pure_Prop_iff
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_possibility_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
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
    have pure_iff:
        "pp_t_holds
          (pp_t_eval pp_t_possibility_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_possibility_fragment_pure Prop w P"
      using
        PossibilityFragment.pp_t_moving_eval_pure_holds[
          of "[Prop]" "Var 0" Prop
            "extend_env P \<rho>" w]
        extended
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_binary_truth_pure_true_implies_necessary[OF P]
      unfolding pp_t_possibility_pure_Prop_iff
        pp_t_necessity_pure_Prop_iff
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_possibility_zeroary_recombination_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_zeroary_recombination_holds by blast

theorem pp_t_possibility_zeroary_exhaustion_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_zeroary_exhaustion_holds by blast

lemma pp_t_possibility_class_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possibility_operator X"
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
  let ?u = "w @ [False]"
  have wu: "prefix w ?u"
    by simp
  have r_seed_w:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using fundamental by simp
  have r_seed_u:
      "pp_t_eqv Prop ?u r (pp_t_moving_seed w)"
    by (rule pp_t_eqv_persistent[OF r_seed_w wu])
  have seed_false_u:
      "pp_t_eqv Prop ?u
        (pp_t_moving_seed w) (pp_zf_truth False)"
    by (rule pp_t_moving_seed_false_on_right)
  have r_false_u:
      "pp_t_eqv Prop ?u r (pp_zf_truth False)"
    by (rule pp_t_eqv_transitive[
      OF r pp_t_moving_seed_in_domain pp_t_truth_in_domain
        r_seed_u seed_false_u])
  have possibility_r_false:
      "\<not> pp_t_holds (pp_t_possibility_operator \<acute> r) ?u"
  proof
    assume possible:
        "pp_t_holds (pp_t_possibility_operator \<acute> r) ?u"
    then obtain v where uv: "prefix ?u v"
      and rv: "pp_t_holds r v"
      using pp_t_possibility_operator_holds[OF r, of ?u]
      by blast
    have at_v:
        "pp_t_holds r v \<longleftrightarrow>
          pp_t_holds (pp_zf_truth False) v"
      by (rule pp_t_prop_eqv_at[OF r_false_u uv])
    show False using rv at_v by simp
  qed
  have representative_u:
      "pp_t_eqv pp_t_constants_unary_type
        ?u pp_t_possibility_operator X"
    by (rule pp_t_eqv_persistent[OF representative wu])
  have rr_u: "pp_t_eqv Prop ?u r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have applications_u:
      "pp_t_eqv Prop ?u
        (pp_t_possibility_operator \<acute> r) (X \<acute> r)"
    by (rule pp_t_app_respects[
      OF representative_u r r rr_u])
  have Xr_false_u: "\<not> pp_t_holds (X \<acute> r) ?u"
  proof
    assume Xr: "pp_t_holds (X \<acute> r) ?u"
    have at_u:
        "pp_t_holds (pp_t_possibility_operator \<acute> r) ?u
          \<longleftrightarrow> pp_t_holds (X \<acute> r) ?u"
      using pp_t_prop_eqv_at[OF applications_u, of ?u]
      by simp
    show False using possibility_r_false Xr at_u by blast
  qed
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using wu Xr_false_u by blast
  have false_domain:
      "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have false_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth False) (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF false_domain])
  have false_applications:
      "pp_t_eqv Prop w
        (pp_t_possibility_operator \<acute> pp_zf_truth False)
        (X \<acute> pp_zf_truth False)"
    by (rule pp_t_app_respects[
      OF representative false_domain false_domain false_refl])
  have possibility_false:
      "\<not> pp_t_holds
        (pp_t_possibility_operator \<acute> pp_zf_truth False) w"
    using pp_t_possibility_operator_holds[
        OF false_domain, of w]
    by simp
  have X_false:
      "\<not> pp_t_holds (X \<acute> pp_zf_truth False) w"
  proof
    assume Xf:
        "pp_t_holds (X \<acute> pp_zf_truth False) w"
    have at_w:
        "pp_t_holds
            (pp_t_possibility_operator \<acute> pp_zf_truth False) w
          \<longleftrightarrow>
         pp_t_holds (X \<acute> pp_zf_truth False) w"
      using pp_t_prop_eqv_at[
        OF false_applications, of w]
      by simp
    show False using possibility_false Xf at_w by blast
  qed
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using false_domain X_false by blast
  show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    using not_necessary by blast
  show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
    using not_universal by blast
qed

lemma pp_t_possibility_pure_unary_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_possibility_fragment_pure
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
  have unary_pure:
      "pp_t_possibility_unary_pure w X"
    using pp_t_possibility_pure_unary_iff[
      of w X] pure by blast
  have classes:
      "pp_t_necessity_fragment_pure
          pp_t_constants_unary_type w X
        \<or>
       pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator X"
    using unary_pure
    unfolding pp_t_possibility_unary_pure_def .
  from classes show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
  proof
    assume old:
        "pp_t_necessity_fragment_pure
          pp_t_constants_unary_type w X"
    show
      "((\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (X \<acute> r) v)
        \<longrightarrow>
        (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) w))"
      by (rule pp_t_necessity_pure_unary_QLN(1)[
        OF X r old fundamental])
  next
    assume possibility:
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator X"
    show
      "((\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (X \<acute> r) v)
        \<longrightarrow>
        (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) w))"
      by (rule pp_t_possibility_class_QLN(1)[
        OF X r possibility fundamental])
  qed
  from classes show
      "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) w)
        \<longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (X \<acute> r) v))"
  proof
    assume old:
        "pp_t_necessity_fragment_pure
          pp_t_constants_unary_type w X"
    show
      "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) w)
        \<longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (X \<acute> r) v))"
      by (rule pp_t_necessity_pure_unary_QLN(2)[
        OF X r old fundamental])
  next
    assume possibility:
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator X"
    show
      "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (X \<acute> q) w)
        \<longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (X \<acute> r) v))"
      by (rule pp_t_possibility_class_QLN(2)[
        OF X r possibility fundamental])
  qed
qed

lemma pp_t_possibility_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_possibility_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_possibility_fragment_pure
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

lemma pp_t_possibility_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_possibility_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_possibility_fragment_pure
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

theorem pp_t_possibility_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_possibility_unary_recombination_holds_iff
  using pp_t_possibility_pure_unary_QLN(1)
  by blast

theorem pp_t_possibility_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_possibility_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_possibility_unary_exhaustion_holds_iff
  using pp_t_possibility_pure_unary_QLN(2)
  by blast

theorem pp_t_possibility_unary_recombination_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_unary_recombination_holds by blast

theorem pp_t_possibility_unary_exhaustion_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    PossibilityFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_possibility_unary_exhaustion_holds by blast

lemma pp_t_possibility_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_possibility_fragment_constants \<rho>
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

theorem pp_t_possibility_modalized_functionality_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (PossibilityFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      PossibilityFragment.MovingTreeConstants.pp_t_den_def
      pp_t_possibility_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

section \<open>The possibility fragment\<close>

definition pp_possibility_purity_axiom :: oterm where
  "pp_possibility_purity_axiom =
    pp_pure pp_unary_ty pp_possibility_operator"

lemma pp_possibility_purity_axiom_in_schema:
  "pp_possibility_purity_axiom \<in> pp_purity_schema"
  unfolding pp_possibility_purity_axiom_def
  by (rule pp_possibility_operator_purity_axiom_in_schema)

definition pp_possibility_fragment_PP_axioms ::
    "oterm set"
where
  "pp_possibility_fragment_PP_axioms =
    pp_necessity_fragment_PP_axioms
      \<union> {pp_possibility_purity_axiom}"

theorem pp_t_possibility_binary_axioms_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_binary_truth_fragment_PP_axioms"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_binary_truth_fragment_PP_axioms"
  from A consider
      (truth_function) F where
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          (pp_truth_function_builder F)"
    | (builder)
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_conjunction_builder"
    | (constant_builder)
        "A = pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
          pp_constant_builder"
    | (constant_truth)
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
    unfolding pp_binary_truth_fragment_PP_axioms_def
      pp_truth_function_purity_axioms_def
      pp_conjunction_fragment_PP_axioms_def
      pp_constant_builder_fragment_PP_axioms_def
      pp_logical_constants_fragment_PP_axioms_def
      pp_identity_negation_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show
      "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case truth_function
    then show ?thesis
      using pp_t_possibility_truth_function_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case builder
    then show ?thesis
      using pp_t_possibility_conjunction_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_builder
    then show ?thesis
      using pp_t_possibility_constant_builder_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_truth
    then show ?thesis
      using pp_t_possibility_constant_truth_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_falsity
    then show ?thesis
      using pp_t_possibility_constant_falsity_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case identity_purity
    then show ?thesis
      using pp_t_possibility_identity_purity_gvalid by simp
  next
    case negation_purity
    then show ?thesis
      using pp_t_possibility_negation_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_possibility_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_possibility_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_possibility_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_possibility_no_fundamentals_gvalid[
        OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_possibility_zeroary_recombination_gvalid
      by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_possibility_unary_recombination_gvalid
      by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_possibility_zeroary_exhaustion_gvalid
      by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_possibility_unary_exhaustion_gvalid
      by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule
        pp_t_possibility_modalized_functionality_gvalid)
  qed
qed

theorem pp_t_possibility_necessity_axioms_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_necessity_fragment_PP_axioms"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "A \<in> pp_necessity_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_binary_truth_fragment_PP_axioms"
    | (necessity) "A = pp_necessity_purity_axiom"
    unfolding pp_necessity_fragment_PP_axioms_def by blast
  then show
      "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case old
    show ?thesis
      using pp_t_possibility_binary_axioms_gvalid old
      unfolding
        PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
      by blast
  next
    case necessity
    show ?thesis
      unfolding necessity pp_necessity_purity_axiom_def
        pp_unary_ty_def
      by (rule pp_t_possibility_necessity_purity_gvalid)
  qed
qed

theorem pp_t_possibility_fragment_PP_gvalid:
  "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_possibility_fragment_PP_axioms"
  unfolding
    PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume "A \<in> pp_possibility_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_necessity_fragment_PP_axioms"
    | (possibility) "A = pp_possibility_purity_axiom"
    unfolding pp_possibility_fragment_PP_axioms_def by blast
  then show
      "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case old
    show ?thesis
      using pp_t_possibility_necessity_axioms_gvalid old
      unfolding
        PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
      by blast
  next
    case possibility
    show ?thesis
      unfolding possibility pp_possibility_purity_axiom_def
        pp_unary_ty_def
      by (rule pp_t_possibility_operator_purity_gvalid)
  qed
qed

theorem pp_possibility_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_possibility_fragment_PP_axioms"
  using
    PossibilityFragment.MovingTreeConstants.pp_t_base_sound
    PossibilityFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_possibility_fragment_PP_gvalid
  by (rule
    PossibilityFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_possibility_fragment_consistent:
  assumes "U \<subseteq> pp_possibility_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_possibility_fragment_PP_gvalid
    unfolding
      PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      PossibilityFragment.MovingTreeConstants.pp_t_base_sound
      PossibilityFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      PossibilityFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
