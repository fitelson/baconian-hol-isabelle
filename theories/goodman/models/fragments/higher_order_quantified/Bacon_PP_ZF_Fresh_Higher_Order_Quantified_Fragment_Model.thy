theory Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model
  imports
    "Higher_Order_Metaphysics_PP_ZF_Possibility.Bacon_PP_ZF_Fresh_Possibility_Fragment_Model"
    "Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers"
begin

section \<open>The two additional modal denotations\<close>

definition pp_t_necessary_falsity_predicate ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_necessary_falsity_predicate w p \<longleftrightarrow>
    pp_t_eqv Prop w p (pp_zf_truth False)"

definition pp_t_possible_falsity_predicate ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_possible_falsity_predicate w p \<longleftrightarrow>
    \<not> pp_t_eqv Prop w p (pp_zf_truth True)"

lemma pp_t_necessary_falsity_predicate_admissible:
  "pp_t_predicate_admissible Prop
    pp_t_necessary_falsity_predicate"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_t_domain Prop)"
    and y: "Elem y (pp_t_domain Prop)"
    and xy: "pp_t_eqv Prop w x y"
    and future: "prefix w v"
  have xy_v: "pp_t_eqv Prop v x y"
    by (rule pp_t_eqv_persistent[OF xy future])
  have yx_v: "pp_t_eqv Prop v y x"
    by (rule pp_t_eqv_symmetric[OF x y xy_v])
  show "pp_t_necessary_falsity_predicate v x =
      pp_t_necessary_falsity_predicate v y"
    unfolding pp_t_necessary_falsity_predicate_def
    using pp_t_eqv_transitive[
        OF x y pp_t_truth_in_domain xy_v]
      pp_t_eqv_transitive[
        OF y x pp_t_truth_in_domain yx_v]
    by blast
qed

lemma pp_t_possible_falsity_predicate_admissible:
  "pp_t_predicate_admissible Prop
    pp_t_possible_falsity_predicate"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_t_domain Prop)"
    and y: "Elem y (pp_t_domain Prop)"
    and xy: "pp_t_eqv Prop w x y"
    and future: "prefix w v"
  have xy_v: "pp_t_eqv Prop v x y"
    by (rule pp_t_eqv_persistent[OF xy future])
  have yx_v: "pp_t_eqv Prop v y x"
    by (rule pp_t_eqv_symmetric[OF x y xy_v])
  show "pp_t_possible_falsity_predicate v x =
      pp_t_possible_falsity_predicate v y"
    unfolding pp_t_possible_falsity_predicate_def
    using pp_t_eqv_transitive[
        OF x y pp_t_truth_in_domain xy_v]
      pp_t_eqv_transitive[
        OF y x pp_t_truth_in_domain yx_v]
    by blast
qed

definition pp_t_necessary_falsity_operator :: ZF where
  "pp_t_necessary_falsity_operator =
    pp_t_classifier Prop pp_t_necessary_falsity_predicate"

definition pp_t_possible_falsity_operator :: ZF where
  "pp_t_possible_falsity_operator =
    pp_t_classifier Prop pp_t_possible_falsity_predicate"

lemma pp_t_necessary_falsity_operator_in_domain:
  "Elem pp_t_necessary_falsity_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_necessary_falsity_operator_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_necessary_falsity_predicate_admissible)

lemma pp_t_possible_falsity_operator_in_domain:
  "Elem pp_t_possible_falsity_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_possible_falsity_operator_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_possible_falsity_predicate_admissible)

lemma pp_t_necessary_falsity_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) w
    \<longleftrightarrow>
      pp_t_eqv Prop w p (pp_zf_truth False)"
  unfolding pp_t_necessary_falsity_operator_def
    pp_t_necessary_falsity_predicate_def
  using pp_t_classifier_holds[OF p] by simp

lemma pp_t_possible_falsity_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_possible_falsity_operator \<acute> p) w
    \<longleftrightarrow>
      \<not> pp_t_eqv Prop w p (pp_zf_truth True)"
  unfolding pp_t_possible_falsity_operator_def
    pp_t_possible_falsity_predicate_def
  using pp_t_classifier_holds[OF p] by simp

lemma pp_t_falsity_operators_truth_eqv:
  "pp_t_eqv Prop w
    (pp_t_necessary_falsity_operator \<acute> pp_zf_truth b)
    (pp_zf_truth (\<not> b))"
  "pp_t_eqv Prop w
    (pp_t_possible_falsity_operator \<acute> pp_zf_truth b)
    (pp_zf_truth (\<not> b))"
proof -
  show "pp_t_eqv Prop w
      (pp_t_necessary_falsity_operator \<acute> pp_zf_truth b)
      (pp_zf_truth (\<not> b))"
    unfolding pp_t_eqv.simps
    using pp_t_necessary_falsity_operator_holds[
      OF pp_t_truth_in_domain, of b]
    by (cases b)
      (auto simp: pp_t_truth_eqv_truth_iff)
  show "pp_t_eqv Prop w
      (pp_t_possible_falsity_operator \<acute> pp_zf_truth b)
      (pp_zf_truth (\<not> b))"
    unfolding pp_t_eqv.simps
    using pp_t_possible_falsity_operator_holds[
      OF pp_t_truth_in_domain, of b]
    by (cases b)
      (auto simp: pp_t_truth_eqv_truth_iff)
qed

section \<open>The higher-order-quantified pure stock\<close>

definition pp_t_quantified_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_quantified_unary_pure w x \<longleftrightarrow>
    pp_t_possibility_fragment_pure
      pp_t_constants_unary_type w x
    \<or>
    pp_t_eqv pp_t_constants_unary_type
      w pp_t_necessary_falsity_operator x
    \<or>
    pp_t_eqv pp_t_constants_unary_type
      w pp_t_possible_falsity_operator x"

lemma pp_t_quantified_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    pp_t_quantified_unary_pure"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (pp_t_possibility_fragment_pure
          pp_t_constants_unary_type)"
    by (rule pp_t_possibility_fragment_pure_admissible)
  have necessary_falsity:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_necessary_falsity_operator_in_domain] .
  have possible_falsity:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_possible_falsity_operator_in_domain] .
  show ?thesis
    using old necessary_falsity possible_falsity
    unfolding pp_t_predicate_admissible_def
      pp_t_quantified_unary_pure_def
    by blast
qed

definition pp_t_quantified_stock_classifier :: ZF where
  "pp_t_quantified_stock_classifier =
    pp_t_classifier pp_t_constants_unary_type
      pp_t_quantified_unary_pure"

lemma pp_t_quantified_stock_classifier_in_domain:
  "Elem pp_t_quantified_stock_classifier
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_quantified_stock_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_quantified_unary_pure_admissible)

definition pp_t_quantified_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_quantified_fragment_pure \<sigma> w x \<longleftrightarrow>
    (pp_t_possibility_fragment_pure \<sigma> w x
      \<and> \<sigma> \<noteq> pp_t_constants_classifier_type)
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> (pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator x
        \<or> pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator x))
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type
        w pp_t_quantified_stock_classifier x)"

lemma pp_t_quantified_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_quantified_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_possibility_fragment_pure \<sigma>)"
    by (rule pp_t_possibility_fragment_pure_admissible)
  have necessary_falsity:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_necessary_falsity_operator_in_domain] .
  have possible_falsity:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_possible_falsity_operator_in_domain] .
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type
          w pp_t_quantified_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_quantified_stock_classifier_in_domain] .
  show ?thesis
    unfolding pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_eqv \<sigma> w x y"
      and future: "prefix w v"
    have old_iff:
        "pp_t_possibility_fragment_pure \<sigma> v x
          \<longleftrightarrow>
         pp_t_possibility_fragment_pure \<sigma> v y"
      using old x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have necessary_iff:
        "\<sigma> = pp_t_constants_unary_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_necessary_falsity_operator x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_necessary_falsity_operator y"
      using necessary_falsity x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have possible_iff:
        "\<sigma> = pp_t_constants_unary_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_possible_falsity_operator x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_possible_falsity_operator y"
      using possible_falsity x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have classifier_iff:
        "\<sigma> = pp_t_constants_classifier_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_classifier_type
            v pp_t_quantified_stock_classifier x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_classifier_type
            v pp_t_quantified_stock_classifier y"
      using classifier x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    show "pp_t_quantified_fragment_pure \<sigma> v x =
        pp_t_quantified_fragment_pure \<sigma> v y"
      unfolding pp_t_quantified_fragment_pure_def
      using old_iff necessary_iff possible_iff classifier_iff
      by blast
  qed
qed

lemma pp_t_quantified_inherits_old_pure:
  assumes old: "pp_t_possibility_fragment_pure \<sigma> w x"
    and not_classifier:
      "\<sigma> \<noteq> pp_t_constants_classifier_type"
  shows "pp_t_quantified_fragment_pure \<sigma> w x"
  unfolding pp_t_quantified_fragment_pure_def
  using old not_classifier by blast

lemma pp_t_quantified_necessary_falsity_is_pure[simp]:
  "pp_t_quantified_fragment_pure
    pp_t_constants_unary_type w pp_t_necessary_falsity_operator"
  unfolding pp_t_quantified_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_necessary_falsity_operator_in_domain]
  by blast

lemma pp_t_quantified_possible_falsity_is_pure[simp]:
  "pp_t_quantified_fragment_pure
    pp_t_constants_unary_type w pp_t_possible_falsity_operator"
  unfolding pp_t_quantified_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_possible_falsity_operator_in_domain]
  by blast

lemma pp_t_quantified_classifier_is_pure[simp]:
  "pp_t_quantified_fragment_pure
    pp_t_constants_classifier_type w
    pp_t_quantified_stock_classifier"
  unfolding pp_t_quantified_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_quantified_stock_classifier_in_domain]
  by blast

lemma pp_t_quantified_pure_Prop_iff:
  "pp_t_quantified_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_possibility_fragment_pure Prop w P"
  unfolding pp_t_quantified_fragment_pure_def by simp

lemma pp_t_quantified_pure_unary_iff:
  "pp_t_quantified_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_quantified_unary_pure w X"
  unfolding pp_t_quantified_fragment_pure_def
    pp_t_quantified_unary_pure_def
  by simp

lemma pp_t_quantified_pure_classifier_iff:
  "pp_t_quantified_fragment_pure
      pp_t_constants_classifier_type w X
    \<longleftrightarrow>
    pp_t_eqv pp_t_constants_classifier_type
      w pp_t_quantified_stock_classifier X"
  unfolding pp_t_quantified_fragment_pure_def by simp

lemma pp_t_possibility_pure_function_from_unary:
  assumes pure:
      "pp_t_possibility_fragment_pure
        (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
  shows "\<tau> = Prop"
  using pure
  unfolding pp_t_possibility_fragment_pure_def
    pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
  by (cases \<tau>) auto

lemma pp_t_possibility_no_pure_function_from_classifier:
  "\<not> pp_t_possibility_fragment_pure
    (pp_t_constants_classifier_type \<rightarrow>\<^sub>o \<tau>) w f"
  unfolding pp_t_possibility_fragment_pure_def
    pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
  by (cases \<tau>) auto

lemma pp_t_quantified_old_input:
  assumes pure_f:
      "pp_t_possibility_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and retained:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
        \<noteq> pp_t_constants_classifier_type"
    and pure_x:
      "pp_t_quantified_fragment_pure \<sigma> w x"
  shows "pp_t_possibility_fragment_pure \<sigma> w x"
proof -
  from pure_x consider
      (old) "pp_t_possibility_fragment_pure \<sigma> w x"
    | (necessary_falsity)
        "\<sigma> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator x"
    | (possible_falsity)
        "\<sigma> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator x"
    | (classifier)
        "\<sigma> = pp_t_constants_classifier_type"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_quantified_stock_classifier x"
    unfolding pp_t_quantified_fragment_pure_def
    by blast
  then show ?thesis
  proof cases
    case old
    then show ?thesis .
  next
    case necessary_falsity
    have pure_unary:
        "pp_t_possibility_fragment_pure
          (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
      using pure_f necessary_falsity by simp
    have tau: "\<tau> = Prop"
      by (rule pp_t_possibility_pure_function_from_unary[
        OF pure_unary])
    have False
      using retained necessary_falsity tau by simp
    then show ?thesis by blast
  next
    case possible_falsity
    have pure_unary:
        "pp_t_possibility_fragment_pure
          (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
      using pure_f possible_falsity by simp
    have tau: "\<tau> = Prop"
      by (rule pp_t_possibility_pure_function_from_unary[
        OF pure_unary])
    have False
      using retained possible_falsity tau by simp
    then show ?thesis by blast
  next
    case classifier
    have False
      using pp_t_possibility_no_pure_function_from_classifier[
        of \<tau> w f] pure_f classifier
      by simp
    then show ?thesis by blast
  qed
qed

lemma pp_t_quantified_necessary_falsity_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator f"
    and pure_x:
      "pp_t_quantified_fragment_pure Prop w x"
  shows "pp_t_quantified_fragment_pure Prop w (f \<acute> x)"
proof -
  have x_class:
      "pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x"
    using pure_x
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
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
        (pp_t_necessary_falsity_operator \<acute> pp_zf_truth b)
        (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative pp_t_truth_in_domain x xb])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth (\<not> b)) (f \<acute> x)"
    using pp_t_falsity_operators_truth_eqv(1)[of w b]
      pp_t_app_closed[
        OF pp_t_necessary_falsity_operator_in_domain
          pp_t_truth_in_domain]
      pp_t_app_closed[OF f x]
      pp_t_truth_in_domain applications
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by (cases b) simp_all
qed

lemma pp_t_quantified_possible_falsity_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possible_falsity_operator f"
    and pure_x:
      "pp_t_quantified_fragment_pure Prop w x"
  shows "pp_t_quantified_fragment_pure Prop w (f \<acute> x)"
proof -
  have x_class:
      "pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x"
    using pure_x
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
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
        (pp_t_possible_falsity_operator \<acute> pp_zf_truth b)
        (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative pp_t_truth_in_domain x xb])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth (\<not> b)) (f \<acute> x)"
    using pp_t_falsity_operators_truth_eqv(2)[of w b]
      pp_t_app_closed[
        OF pp_t_possible_falsity_operator_in_domain
          pp_t_truth_in_domain]
      pp_t_app_closed[OF f x]
      pp_t_truth_in_domain applications
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by (cases b) simp_all
qed

lemma pp_t_quantified_unary_pure_persistent:
  assumes pure: "pp_t_quantified_unary_pure w x"
    and future: "prefix w v"
  shows "pp_t_quantified_unary_pure v x"
  using pure pp_t_eqv_persistent[OF _ future]
  unfolding pp_t_quantified_unary_pure_def
    pp_t_possibility_fragment_pure_def
    pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
    pp_t_constants_unary_pure_def
    pp_t_idneg_unary_pure_def
  by blast

lemma pp_t_quantified_stock_classifier_on_pure:
  assumes x:
      "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and pure: "pp_t_quantified_unary_pure w x"
  shows "pp_t_eqv Prop w
    (pp_t_quantified_stock_classifier \<acute> x)
    (pp_zf_truth True)"
proof -
  have pure_future:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_quantified_unary_pure v x"
    using pp_t_quantified_unary_pure_persistent[
      OF pure] by blast
  show ?thesis
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_quantified_stock_classifier_def
    using pp_t_classifier_holds[
      OF x, of pp_t_quantified_unary_pure]
      pure_future
    by simp
qed

lemma pp_t_quantified_classifier_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_classifier_type)"
    and x:
      "Elem x (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_quantified_stock_classifier f"
    and pure_x: "pp_t_quantified_unary_pure w x"
  shows "pp_t_quantified_fragment_pure Prop w (f \<acute> x)"
proof -
  have xx:
      "pp_t_eqv pp_t_constants_unary_type w x x"
    by (rule pp_t_eqv_reflexive[OF x])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_quantified_stock_classifier \<acute> x)
        (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative x x xx])
  have result:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (f \<acute> x)"
    using pp_t_quantified_stock_classifier_on_pure[
        OF x pure_x]
      applications pp_t_truth_in_domain
      pp_t_app_closed[
        OF pp_t_quantified_stock_classifier_in_domain x]
      pp_t_app_closed[OF f x]
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by blast
qed

lemma pp_t_quantified_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_quantified_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_quantified_fragment_pure \<sigma> w x"
  shows "pp_t_quantified_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_possibility_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
        "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<noteq> pp_t_constants_classifier_type"
    | (necessary_falsity)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator f"
    | (possible_falsity)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator f"
    | (classifier)
        "\<sigma> = pp_t_constants_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_quantified_stock_classifier f"
    unfolding pp_t_quantified_fragment_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_possibility_fragment_pure \<sigma> w x"
      by (rule pp_t_quantified_old_input[
        OF old pure_x])
    have old_result:
        "pp_t_possibility_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_possibility_fragment_application[
        OF f x old(1) old_x])
    have not_classifier:
        "\<tau> \<noteq> pp_t_constants_classifier_type"
    proof
      assume tau:
          "\<tau> = pp_t_constants_classifier_type"
      have no_old:
          "\<not> pp_t_possibility_fragment_pure
            (\<sigma> \<rightarrow>\<^sub>o
              pp_t_constants_classifier_type) w f"
        unfolding pp_t_possibility_fragment_pure_def
          pp_t_necessity_fragment_pure_def
          pp_t_binary_truth_fragment_pure_def
          pp_t_conjunction_fragment_pure_def
          pp_t_constant_builder_fragment_pure_def
          pp_t_constants_fragment_pure_def
        by (cases \<sigma>) auto
      show False
        using no_old old(1) unfolding tau by blast
    qed
    show ?thesis
      by (rule pp_t_quantified_inherits_old_pure[
        OF old_result not_classifier])
  next
    case necessary_falsity
    show ?thesis
      using pp_t_quantified_necessary_falsity_application[
        OF _ _ necessary_falsity(3)]
        f x pure_x necessary_falsity
      by simp
  next
    case possible_falsity
    show ?thesis
      using pp_t_quantified_possible_falsity_application[
        OF _ _ possible_falsity(3)]
        f x pure_x possible_falsity
      by simp
  next
    case classifier
    have pure_unary_fragment:
        "pp_t_quantified_fragment_pure
          pp_t_constants_unary_type w x"
      using pure_x classifier by simp
    have unary_pure:
        "pp_t_quantified_unary_pure w x"
      using pp_t_quantified_pure_unary_iff[
        of w x] pure_unary_fragment
      by blast
    show ?thesis
      using pp_t_quantified_classifier_application[
        OF _ _ classifier(3) unary_pure] f x classifier
      by simp
  qed
qed

section \<open>The six higher-order quantified terms\<close>

interpretation QuantifiedFragment:
  pp_t_moving_internal_parameters
    pp_t_quantified_fragment_pure
  by standard
    (rule pp_t_quantified_fragment_pure_admissible)

abbreviation pp_t_quantified_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_quantified_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_quantified_fragment_pure"

lemma pp_t_HO_leibniz_truth_eqv_necessity:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_leibniz_truth_term)
    pp_t_necessity_operator"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_closed_den pp_t_HO_leibniz_truth_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(1)]
    by simp
  show "Elem pp_t_necessity_operator
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_necessity_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_leibniz_truth_term \<acute> p)
          (pp_t_necessity_operator \<acute> p))"
    unfolding pp_t_eqv.simps
    using pp_t_HO_leibniz_truth_holds
      pp_t_necessity_operator_holds
    by blast
qed

lemma pp_t_HO_leibniz_false_eqv_necessary_falsity:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_leibniz_false_term)
    pp_t_necessary_falsity_operator"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_closed_den pp_t_HO_leibniz_false_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(2)]
    by simp
  show "Elem pp_t_necessary_falsity_operator
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_necessary_falsity_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_leibniz_false_term \<acute> p)
          (pp_t_necessary_falsity_operator \<acute> p))"
    unfolding pp_t_eqv.simps
    using pp_t_HO_leibniz_false_holds
      pp_t_necessary_falsity_operator_holds
    by blast
qed

lemma pp_t_HO_not_leibniz_truth_eqv_possible_falsity:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
    pp_t_possible_falsity_operator"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem
      (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(3)]
    by simp
  show "Elem pp_t_possible_falsity_operator
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_possible_falsity_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_not_leibniz_truth_term \<acute> p)
          (pp_t_possible_falsity_operator \<acute> p))"
    unfolding pp_t_eqv.simps
    using pp_t_HO_not_leibniz_truth_holds
      pp_t_possible_falsity_operator_holds
    by blast
qed

lemma pp_t_HO_not_leibniz_false_eqv_possibility:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_not_leibniz_false_term)
    pp_t_possibility_operator"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem
      (pp_t_closed_den pp_t_HO_not_leibniz_false_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(4)]
    by simp
  show "Elem pp_t_possibility_operator
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_possibility_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_not_leibniz_false_term \<acute> p)
          (pp_t_possibility_operator \<acute> p))"
  proof (intro allI impI)
    fix v p
    assume "prefix w v"
      and p: "Elem p (pp_t_domain Prop)"
    show "pp_t_eqv Prop v
        (pp_t_closed_den pp_t_HO_not_leibniz_false_term \<acute> p)
        (pp_t_possibility_operator \<acute> p)"
    proof (simp only: pp_t_eqv.simps, intro allI impI)
      fix u
      assume "prefix v u"
      have term_semantics:
          "pp_t_holds
              (pp_t_closed_den
                pp_t_HO_not_leibniz_false_term \<acute> p) u
            \<longleftrightarrow>
           \<not> pp_t_eqv Prop u p (pp_zf_truth False)"
        by (rule pp_t_HO_not_leibniz_false_holds[OF p])
      have possible:
          "pp_t_holds (pp_t_possibility_operator \<acute> p) u
            \<longleftrightarrow>
           (\<exists>z. prefix u z \<and> pp_t_holds p z)"
        by (rule pp_t_possibility_operator_holds[OF p])
      have not_false:
          "(\<not> pp_t_eqv Prop u p (pp_zf_truth False))
            \<longleftrightarrow>
           (\<exists>z. prefix u z \<and> pp_t_holds p z)"
        unfolding pp_t_eqv.simps
        by auto
      show "pp_t_holds
          (pp_t_closed_den
            pp_t_HO_not_leibniz_false_term \<acute> p) u =
        pp_t_holds (pp_t_possibility_operator \<acute> p) u"
        using term_semantics possible not_false by blast
    qed
  qed
qed

lemma pp_t_HO_forall_application_eqv_constant_falsity:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_forall_application_term)
    (pp_t_constant_operator False)"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_closed_den pp_t_HO_forall_application_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_application_terms_typed(1)]
    by simp
  show "Elem (pp_t_constant_operator False)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_constant_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_forall_application_term \<acute> p)
          (pp_t_constant_operator False \<acute> p))"
  proof (intro allI impI)
    fix v p
    assume "prefix w v"
      and p: "Elem p (pp_t_domain Prop)"
    show "pp_t_eqv Prop v
        (pp_t_closed_den pp_t_HO_forall_application_term \<acute> p)
        (pp_t_constant_operator False \<acute> p)"
      unfolding pp_t_eqv.simps
      using pp_t_HO_forall_application_never_holds[OF p]
        pp_t_constant_operator_holds[OF p, of False]
      by simp
  qed
qed

lemma pp_t_HO_exists_application_eqv_constant_truth:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_exists_application_term)
    (pp_t_constant_operator True)"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_closed_den pp_t_HO_exists_application_term)
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_application_terms_typed(2)]
    by simp
  show "Elem (pp_t_constant_operator True)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_constant_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den pp_t_HO_exists_application_term \<acute> p)
          (pp_t_constant_operator True \<acute> p))"
  proof (intro allI impI)
    fix v p
    assume "prefix w v"
      and p: "Elem p (pp_t_domain Prop)"
    show "pp_t_eqv Prop v
        (pp_t_closed_den pp_t_HO_exists_application_term \<acute> p)
        (pp_t_constant_operator True \<acute> p)"
      unfolding pp_t_eqv.simps
      using pp_t_HO_exists_application_always_holds[OF p]
        pp_t_constant_operator_holds[OF p, of True]
      by simp
  qed
qed

lemma pp_t_quantified_closed_logical_eval_eqv:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_eqv \<sigma> w
    (pp_t_closed_den M)
    (pp_t_eval pp_t_quantified_fragment_constants \<rho> M)"
proof -
  have const_free: "consts_of M = {}"
    using logical unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval pp_t_quantified_fragment_constants \<rho> M =
        pp_t_eval pp_t_default_constants \<rho> M"
    using pp_t_eval_const_free[OF const_free] .
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)
        (pp_t_eval pp_t_default_constants \<rho> M)"
    by (rule DefaultTreeConstants.pp_t_eval_respects[
      OF typed pp_t_empty_env_eqv])
  show ?thesis
    using related change_constants
    by (simp add: pp_t_closed_den_def)
qed

lemma pp_t_quantified_logical_purity_holds:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and pure:
      "pp_t_quantified_fragment_pure
        \<sigma> w (pp_t_closed_den M)"
  shows "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure \<sigma> M)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have closed_domain:
      "Elem (pp_t_closed_den M) (pp_t_domain \<sigma>)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have evaluated:
      "Elem
        (pp_t_eval pp_t_quantified_fragment_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using
      QuantifiedFragment.MovingTreeConstants.pp_t_eval_type[
        OF typed env]
    by (simp add: pp_t_dom_def)
  have related:
      "pp_t_eqv \<sigma> w (pp_t_closed_den M)
        (pp_t_eval pp_t_quantified_fragment_constants \<rho> M)"
    by (rule pp_t_quantified_closed_logical_eval_eqv[
      OF typed logical])
  have same_purity:
      "pp_t_quantified_fragment_pure
          \<sigma> w (pp_t_closed_den M)
        \<longleftrightarrow>
       pp_t_quantified_fragment_pure \<sigma> w
        (pp_t_eval pp_t_quantified_fragment_constants \<rho> M)"
    using pp_t_quantified_fragment_pure_admissible
      closed_domain evaluated related
    unfolding pp_t_predicate_admissible_def
    by simp
  have pure_evaluated:
      "pp_t_quantified_fragment_pure \<sigma> w
        (pp_t_eval pp_t_quantified_fragment_constants \<rho> M)"
    using same_purity pure by blast
  show ?thesis
    using
      QuantifiedFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
      pure_evaluated
    by simp
qed

lemma pp_t_quantified_pure_if_eqv:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> w x y"
    and pure_y: "pp_t_quantified_fragment_pure \<sigma> w y"
  shows "pp_t_quantified_fragment_pure \<sigma> w x"
  using pp_t_quantified_fragment_pure_admissible
    x y xy pure_y
  unfolding pp_t_predicate_admissible_def
  by blast

lemma pp_t_quantified_necessity_is_pure:
  "pp_t_quantified_fragment_pure
    pp_t_constants_unary_type w pp_t_necessity_operator"
proof -
  have old:
      "pp_t_possibility_fragment_pure
        pp_t_constants_unary_type w pp_t_necessity_operator"
    apply (rule pp_t_possibility_inherits_old_pure)
     apply (rule pp_t_necessity_operator_is_pure)
    apply simp
    done
  show ?thesis
    by (rule pp_t_quantified_inherits_old_pure[OF old])
      simp
qed

lemma pp_t_quantified_possibility_is_pure:
  "pp_t_quantified_fragment_pure
    pp_t_constants_unary_type w pp_t_possibility_operator"
  by (rule pp_t_quantified_inherits_old_pure)
    simp_all

lemma pp_t_quantified_constant_is_pure:
  "pp_t_quantified_fragment_pure
    pp_t_constants_unary_type w (pp_t_constant_operator b)"
proof -
  have binary:
      "pp_t_binary_truth_fragment_pure
        pp_t_constants_unary_type w (pp_t_constant_operator b)"
    apply (rule pp_t_binary_truth_inherits_old_pure)
    apply (rule pp_t_conjunction_inherits_constants_pure)
    apply (rule pp_t_constants_constant_is_pure)
    done
  have necessity:
      "pp_t_necessity_fragment_pure
        pp_t_constants_unary_type w (pp_t_constant_operator b)"
    by (rule pp_t_necessity_inherits_old_pure[OF binary])
      simp
  have possibility:
      "pp_t_possibility_fragment_pure
        pp_t_constants_unary_type w (pp_t_constant_operator b)"
    by (rule pp_t_possibility_inherits_old_pure[OF necessity])
      simp
  show ?thesis
    by (rule pp_t_quantified_inherits_old_pure[OF possibility])
      simp
qed

lemma pp_t_HO_quantified_terms_are_pure:
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_leibniz_truth_term)"
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_leibniz_false_term)"
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)"
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_not_leibniz_false_term)"
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_forall_application_term)"
  "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
    (pp_t_closed_den pp_t_HO_exists_application_term)"
proof -
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_leibniz_truth_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(1)]
        pp_t_necessity_operator_in_domain
        pp_t_HO_leibniz_truth_eqv_necessity
        pp_t_quantified_necessity_is_pure])
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_leibniz_false_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(2)]
        pp_t_necessary_falsity_operator_in_domain
        pp_t_HO_leibniz_false_eqv_necessary_falsity
        pp_t_quantified_necessary_falsity_is_pure])
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(3)]
        pp_t_possible_falsity_operator_in_domain
        pp_t_HO_not_leibniz_truth_eqv_possible_falsity
        pp_t_quantified_possible_falsity_is_pure])
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_not_leibniz_false_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_leibniz_terms_typed(4)]
        pp_t_possibility_operator_in_domain
        pp_t_HO_not_leibniz_false_eqv_possibility
        pp_t_quantified_possibility_is_pure])
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_forall_application_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_application_terms_typed(1)]
        pp_t_constant_operator_in_domain
        pp_t_HO_forall_application_eqv_constant_falsity
        pp_t_quantified_constant_is_pure])
  show "pp_t_quantified_fragment_pure pp_t_constants_unary_type w
      (pp_t_closed_den pp_t_HO_exists_application_term)"
    by (rule pp_t_quantified_pure_if_eqv[
      OF pp_t_closed_den_in_domain[
          OF pp_t_HO_application_terms_typed(2)]
        pp_t_constant_operator_in_domain
        pp_t_HO_exists_application_eqv_constant_truth
        pp_t_quantified_constant_is_pure])
qed

lemma pp_t_HO_quantified_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty pp_t_HO_leibniz_truth_term)) w"
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty pp_t_HO_leibniz_false_term)) w"
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty
        pp_t_HO_not_leibniz_truth_term)) w"
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty
        pp_t_HO_not_leibniz_false_term)) w"
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty
        pp_t_HO_forall_application_term)) w"
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      (pp_pure pp_unary_ty
        pp_t_HO_exists_application_term)) w"
  unfolding pp_unary_ty_def
  by (rule pp_t_quantified_logical_purity_holds;
      rule pp_t_HO_leibniz_terms_typed
        pp_t_HO_leibniz_terms_logical
        pp_t_HO_application_terms_typed
        pp_t_HO_application_terms_logical
        pp_t_HO_quantified_terms_are_pure)+

theorem pp_t_HO_quantified_purity_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_leibniz_truth_term)"
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_leibniz_false_term)"
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_not_leibniz_truth_term)"
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_not_leibniz_false_term)"
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_forall_application_term)"
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_unary_ty pp_t_HO_exists_application_term)"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_HO_quantified_purity_holds
  by blast+

section \<open>Recombination and Exhaustion for the enlarged stock\<close>

lemma pp_t_necessary_falsity_class_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator X"
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
  have r_seed:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using fundamental by simp
  have r_not_false:
      "\<not> pp_t_eqv Prop w r (pp_zf_truth False)"
  proof
    assume r_false:
        "pp_t_eqv Prop w r (pp_zf_truth False)"
    have at_left:
        "pp_t_holds r (w @ [True])
          \<longleftrightarrow>
         pp_t_holds (pp_t_moving_seed w) (w @ [True])"
      using pp_t_prop_eqv_at[OF r_seed, of "w @ [True]"]
      by simp
    have false_left:
        "pp_t_holds r (w @ [True])
          \<longleftrightarrow>
         pp_t_holds (pp_zf_truth False) (w @ [True])"
      using pp_t_prop_eqv_at[OF r_false, of "w @ [True]"]
      by simp
    show False using at_left false_left by simp
  qed
  have operator_r_false:
      "\<not> pp_t_holds (pp_t_necessary_falsity_operator \<acute> r) w"
    using pp_t_necessary_falsity_operator_holds[OF r]
      r_not_false by blast
  have rr: "pp_t_eqv Prop w r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_necessary_falsity_operator \<acute> r) (X \<acute> r)"
    by (rule pp_t_app_respects[
      OF representative r r rr])
  have Xr_false: "\<not> pp_t_holds (X \<acute> r) w"
  proof
    assume Xr: "pp_t_holds (X \<acute> r) w"
    have at_w:
        "pp_t_holds (pp_t_necessary_falsity_operator \<acute> r) w
          \<longleftrightarrow> pp_t_holds (X \<acute> r) w"
      using pp_t_prop_eqv_at[OF applications, of w]
      by simp
    show False using operator_r_false Xr at_w by blast
  qed
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using Xr_false by blast
  have true_domain:
      "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have true_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF true_domain])
  have true_applications:
      "pp_t_eqv Prop w
        (pp_t_necessary_falsity_operator \<acute> pp_zf_truth True)
        (X \<acute> pp_zf_truth True)"
    by (rule pp_t_app_respects[
      OF representative true_domain true_domain true_refl])
  have operator_true_false:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> pp_zf_truth True) w"
  proof -
    have not_equal:
        "\<not> pp_t_eqv Prop w
          (pp_zf_truth True) (pp_zf_truth False)"
    proof
      assume equal:
          "pp_t_eqv Prop w
            (pp_zf_truth True) (pp_zf_truth False)"
      have at_w:
          "pp_t_holds (pp_zf_truth True) w
            \<longleftrightarrow>
           pp_t_holds (pp_zf_truth False) w"
        using pp_t_prop_eqv_at[OF equal, of w] by simp
      show False using at_w by simp
    qed
    show ?thesis
      using pp_t_necessary_falsity_operator_holds[
        OF true_domain, of w] not_equal
      by blast
  qed
  have X_true_false:
      "\<not> pp_t_holds (X \<acute> pp_zf_truth True) w"
  proof
    assume Xt: "pp_t_holds (X \<acute> pp_zf_truth True) w"
    have at_w:
        "pp_t_holds
            (pp_t_necessary_falsity_operator \<acute> pp_zf_truth True) w
          \<longleftrightarrow>
         pp_t_holds (X \<acute> pp_zf_truth True) w"
      using pp_t_prop_eqv_at[OF true_applications, of w]
      by simp
    show False using operator_true_false Xt at_w by blast
  qed
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using true_domain X_true_false by blast
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

lemma pp_t_possible_falsity_class_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possible_falsity_operator X"
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
  let ?u = "w @ [True]"
  have wu: "prefix w ?u"
    by simp
  have r_seed_w:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using fundamental by simp
  have r_seed_u:
      "pp_t_eqv Prop ?u r (pp_t_moving_seed w)"
    by (rule pp_t_eqv_persistent[OF r_seed_w wu])
  have seed_true_u:
      "pp_t_eqv Prop ?u
        (pp_t_moving_seed w) (pp_zf_truth True)"
    by (rule pp_t_moving_seed_true_on_left)
  have r_true_u:
      "pp_t_eqv Prop ?u r (pp_zf_truth True)"
    by (rule pp_t_eqv_transitive[
      OF r pp_t_moving_seed_in_domain pp_t_truth_in_domain
        r_seed_u seed_true_u])
  have operator_r_false:
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute> r) ?u"
    using pp_t_possible_falsity_operator_holds[OF r]
      r_true_u by blast
  have representative_u:
      "pp_t_eqv pp_t_constants_unary_type
        ?u pp_t_possible_falsity_operator X"
    by (rule pp_t_eqv_persistent[OF representative wu])
  have rr_u: "pp_t_eqv Prop ?u r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have applications_u:
      "pp_t_eqv Prop ?u
        (pp_t_possible_falsity_operator \<acute> r) (X \<acute> r)"
    by (rule pp_t_app_respects[
      OF representative_u r r rr_u])
  have Xr_false_u: "\<not> pp_t_holds (X \<acute> r) ?u"
  proof
    assume Xr: "pp_t_holds (X \<acute> r) ?u"
    have at_u:
        "pp_t_holds (pp_t_possible_falsity_operator \<acute> r) ?u
          \<longleftrightarrow> pp_t_holds (X \<acute> r) ?u"
      using pp_t_prop_eqv_at[OF applications_u, of ?u]
      by simp
    show False using operator_r_false Xr at_u by blast
  qed
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using wu Xr_false_u by blast
  have true_domain:
      "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have true_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF true_domain])
  have true_applications:
      "pp_t_eqv Prop w
        (pp_t_possible_falsity_operator \<acute> pp_zf_truth True)
        (X \<acute> pp_zf_truth True)"
    by (rule pp_t_app_respects[
      OF representative true_domain true_domain true_refl])
  have operator_true_false:
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute> pp_zf_truth True) w"
  proof -
    have equal:
        "pp_t_eqv Prop w
          (pp_zf_truth True) (pp_zf_truth True)"
      by (rule pp_t_eqv_reflexive[OF true_domain])
    show ?thesis
      using pp_t_possible_falsity_operator_holds[
        OF true_domain, of w] equal
      by blast
  qed
  have X_true_false:
      "\<not> pp_t_holds (X \<acute> pp_zf_truth True) w"
  proof
    assume Xt: "pp_t_holds (X \<acute> pp_zf_truth True) w"
    have at_w:
        "pp_t_holds
            (pp_t_possible_falsity_operator \<acute> pp_zf_truth True) w
          \<longleftrightarrow>
         pp_t_holds (X \<acute> pp_zf_truth True) w"
      using pp_t_prop_eqv_at[OF true_applications, of w]
      by simp
    show False using operator_true_false Xt at_w by blast
  qed
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using true_domain X_true_false by blast
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

lemma pp_t_quantified_pure_unary_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_quantified_fragment_pure
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
  have classes:
      "pp_t_possibility_fragment_pure
          pp_t_constants_unary_type w X
        \<or>
       pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator X
        \<or>
       pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator X"
    using pure
    unfolding pp_t_quantified_pure_unary_iff
      pp_t_quantified_unary_pure_def .
  show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
    using classes
      pp_t_possibility_pure_unary_QLN(1)[
        OF X r _ fundamental]
      pp_t_necessary_falsity_class_QLN(1)[
        OF X r _ fundamental]
      pp_t_possible_falsity_class_QLN(1)[
        OF X r _ fundamental]
    by blast
  show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
    using classes
      pp_t_possibility_pure_unary_QLN(2)[
        OF X r _ fundamental]
      pp_t_necessary_falsity_class_QLN(2)[
        OF X r _ fundamental]
      pp_t_possible_falsity_class_QLN(2)[
        OF X r _ fundamental]
    by blast
qed

lemma pp_t_quantified_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_quantified_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_quantified_fragment_pure
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

lemma pp_t_quantified_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_quantified_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_quantified_fragment_pure
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

theorem pp_t_quantified_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_quantified_unary_recombination_holds_iff
  using pp_t_quantified_pure_unary_QLN(1)
  by blast

theorem pp_t_quantified_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_quantified_unary_exhaustion_holds_iff
  using pp_t_quantified_pure_unary_QLN(2)
  by blast

theorem pp_t_quantified_unary_recombination_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_quantified_unary_recombination_holds by blast

theorem pp_t_quantified_unary_exhaustion_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_quantified_unary_exhaustion_holds by blast

lemma pp_t_quantified_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
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
          (pp_t_eval pp_t_quantified_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_quantified_fragment_pure Prop w P"
      using
        QuantifiedFragment.pp_t_moving_eval_pure_holds[
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
        (pp_t_eval pp_t_quantified_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
        pp_t_quantified_pure_Prop_iff
        pp_t_possibility_pure_Prop_iff
        pp_t_necessity_pure_Prop_iff
        pp_t_binary_truth_pure_Prop_iff
        pp_t_constant_builder_pure_Prop_iff
        pp_t_constants_fragment_pure_Prop_iff
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_quantified_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
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
          (pp_t_eval pp_t_quantified_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_quantified_fragment_pure Prop w P"
      using
        QuantifiedFragment.pp_t_moving_eval_pure_holds[
          of "[Prop]" "Var 0" Prop
            "extend_env P \<rho>" w]
        extended
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_quantified_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_binary_truth_pure_true_implies_necessary[OF P]
      unfolding pp_t_quantified_pure_Prop_iff
        pp_t_possibility_pure_Prop_iff
        pp_t_necessity_pure_Prop_iff
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_quantified_zeroary_recombination_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_quantified_zeroary_recombination_holds by blast

theorem pp_t_quantified_zeroary_exhaustion_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_quantified_zeroary_exhaustion_holds by blast

lemma pp_t_quantified_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_quantified_fragment_constants \<rho>
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

theorem pp_t_quantified_modalized_functionality_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (QuantifiedFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      QuantifiedFragment.MovingTreeConstants.pp_t_den_def
      pp_t_quantified_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

lemma pp_t_quantified_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_quantified_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_quantified_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_quantified_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_quantified_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_quantified_application_closure_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (QuantifiedFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      QuantifiedFragment.MovingTreeConstants.pp_t_den_def
      pp_t_quantified_application_closure_holds_iff
    using pp_t_quantified_fragment_application by blast
qed

theorem pp_t_quantified_unique_fundamental_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using QuantifiedFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_quantified_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows
    "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
      (pp_no_fundamentals \<sigma>)"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using QuantifiedFragment.pp_t_moving_no_fundamentals_holds[
    OF assms]
  by blast

lemma pp_t_quantified_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_quantified_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_quantified_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_quantified_stock_classifier"
    unfolding pp_t_quantified_stock_classifier_def
      pp_t_classifier_def
    by (simp add: pp_t_quantified_pure_unary_iff)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_quantified_stock_classifier_in_domain,
      of "pp_t_quantified_fragment_pure
        pp_t_constants_classifier_type" w]
      pp_t_quantified_classifier_is_pure
    by (simp add: unary_classifier)
qed

theorem pp_t_quantified_target_PP_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    QuantifiedFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_quantified_target_PP_holds by blast

lemma pp_t_quantified_inherits_possibility_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and not_classifier:
      "\<sigma> \<noteq> pp_t_constants_classifier_type"
    and old:
      "PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid []
        (pp_pure \<sigma> M)"
  shows
    "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
      (pp_pure \<sigma> M)"
proof -
  have old_holds:
      "\<And>w. pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants
          pp_t_closed_env (pp_pure \<sigma> M)) w"
  proof -
    fix w
    have empty_ok: "env_ok [] []"
      by simp
    have valid_empty:
        "\<forall>u. pp_t_holds
          (PossibilityFragment.MovingTreeConstants.pp_t_den
            (pp_pure \<sigma> M) []) u"
      using old empty_ok
      unfolding
        PossibilityFragment.MovingTreeConstants.TreeHenkin.gvalid_def
      by simp
    have at_empty:
        "pp_t_holds
          (PossibilityFragment.MovingTreeConstants.pp_t_den
            (pp_pure \<sigma> M) []) w"
      using valid_empty by blast
    have env_eq:
        "pp_t_list_env [] = pp_t_closed_env"
      by (rule ext)
        (simp add: pp_t_list_env_def pp_t_closed_env_def
          nth_default_def)
    show "pp_t_holds
        (pp_t_eval pp_t_possibility_fragment_constants
          pp_t_closed_env (pp_pure \<sigma> M)) w"
      using at_empty
      unfolding
        PossibilityFragment.MovingTreeConstants.pp_t_den_def
        env_eq .
  qed
  have old_pure:
      "\<And>w. pp_t_possibility_fragment_pure
        \<sigma> w (pp_t_closed_den M)"
  proof -
    fix w
    have env: "pp_t_env_typed [] pp_t_closed_env"
      by (rule pp_t_empty_env_typed)
    have evaluated_pure:
        "pp_t_possibility_fragment_pure \<sigma> w
          (pp_t_eval pp_t_possibility_fragment_constants
            pp_t_closed_env M)"
      using
        PossibilityFragment.pp_t_moving_eval_pure_holds[
          OF typed env, of w]
        old_holds[of w]
      by simp
    have const_free: "consts_of M = {}"
      using logical unfolding pp_logical_vocabulary_def .
    have evaluation:
        "pp_t_eval pp_t_possibility_fragment_constants
            pp_t_closed_env M
          = pp_t_closed_den M"
      unfolding pp_t_closed_den_def
      using pp_t_eval_const_free[OF const_free] by simp
    show "pp_t_possibility_fragment_pure
        \<sigma> w (pp_t_closed_den M)"
      using evaluated_pure unfolding evaluation .
  qed
  have quantified_pure:
      "\<And>w. pp_t_quantified_fragment_pure
        \<sigma> w (pp_t_closed_den M)"
    using old_pure
    by (rule pp_t_quantified_inherits_old_pure[
      OF _ not_classifier])
  show ?thesis
    unfolding
      QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_def
      QuantifiedFragment.MovingTreeConstants.pp_t_den_def
    using pp_t_quantified_logical_purity_holds[
      OF typed logical quantified_pure]
    by blast
qed

section \<open>The higher-order quantified fragment\<close>

definition pp_HO_quantified_purity_axioms :: "oterm set" where
  "pp_HO_quantified_purity_axioms = {
    pp_pure pp_unary_ty pp_t_HO_leibniz_truth_term,
    pp_pure pp_unary_ty pp_t_HO_leibniz_false_term,
    pp_pure pp_unary_ty pp_t_HO_not_leibniz_truth_term,
    pp_pure pp_unary_ty pp_t_HO_not_leibniz_false_term,
    pp_pure pp_unary_ty pp_t_HO_forall_application_term,
    pp_pure pp_unary_ty pp_t_HO_exists_application_term}"

lemma pp_HO_quantified_purity_axioms_in_schema:
  "pp_HO_quantified_purity_axioms \<subseteq> pp_purity_schema"
  unfolding pp_HO_quantified_purity_axioms_def
    pp_purity_schema_def
  using pp_t_HO_leibniz_terms_typed
    pp_t_HO_leibniz_terms_logical
    pp_t_HO_application_terms_typed
    pp_t_HO_application_terms_logical
  unfolding pp_unary_ty_def
  by auto

definition pp_quantified_fragment_PP_axioms :: "oterm set" where
  "pp_quantified_fragment_PP_axioms =
    pp_possibility_fragment_PP_axioms
      \<union> pp_HO_quantified_purity_axioms"

theorem pp_t_quantified_old_axioms_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_possibility_fragment_PP_axioms"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_possibility_fragment_PP_axioms"
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
    | (necessity_purity)
        "A = pp_necessity_purity_axiom"
    | (possibility_purity)
        "A = pp_possibility_purity_axiom"
    | (target) "A = pp_target_PP"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> pp_modalized_functionality_schema"
    unfolding pp_possibility_fragment_PP_axioms_def
      pp_necessity_fragment_PP_axioms_def
      pp_binary_truth_fragment_PP_axioms_def
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
      "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case truth_function
    have typed:
        "[] \<turnstile> pp_truth_function_builder F :
          Prop \<rightarrow>\<^sub>o pp_unary_ty"
      by (rule typed_pp_truth_function_builder)
    have logical:
        "pp_logical_vocabulary (pp_truth_function_builder F)"
      unfolding pp_logical_vocabulary_def
      by (rule pp_truth_function_builder_closed)
    show ?thesis
      unfolding truth_function
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed logical])
       apply simp
      using pp_t_possibility_truth_function_purity_gvalid[
        where \<Gamma>="[]" and F=F]
      unfolding pp_unary_ty_def
      by simp
  next
    case builder
    have logical:
        "pp_logical_vocabulary pp_conjunction_builder"
      by (simp add: pp_logical_vocabulary_def
          pp_conjunction_builder_def)
    show ?thesis
      unfolding builder
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed_pp_conjunction_builder logical])
       apply simp
      using pp_t_possibility_conjunction_purity_gvalid[
        where \<Gamma>="[]"]
      unfolding pp_unary_ty_def
      by simp
  next
    case constant_builder
    have logical:
        "pp_logical_vocabulary pp_constant_builder"
      by (simp add: pp_logical_vocabulary_def
          pp_constant_builder_def)
    show ?thesis
      unfolding constant_builder
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed_pp_constant_builder logical])
       apply simp
      using pp_t_possibility_constant_builder_purity_gvalid[
        where \<Gamma>="[]"]
      unfolding pp_unary_ty_def
      by simp
  next
    case constant_truth
    have typed:
        "[] \<turnstile> pp_constant_operator ObjTrue : pp_unary_ty"
      by (rule typed_pp_constant_operator[OF typed_ObjTrue])
    have logical:
        "pp_logical_vocabulary
          (pp_constant_operator ObjTrue)"
      by (simp add: pp_logical_vocabulary_def
          pp_constant_operator_def ObjTrue_def)
    show ?thesis
      unfolding constant_truth
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed logical])
       apply (simp add: pp_unary_ty_def)
      using pp_t_possibility_constant_truth_purity_gvalid[
        where \<Gamma>="[]"]
      unfolding pp_unary_ty_def
      by simp
  next
    case constant_falsity
    have typed:
        "[] \<turnstile> pp_constant_operator ObjFalse : pp_unary_ty"
      by (rule typed_pp_constant_operator[OF typed_ObjFalse])
    have logical:
        "pp_logical_vocabulary
          (pp_constant_operator ObjFalse)"
      by (simp add: pp_logical_vocabulary_def
          pp_constant_operator_def ObjFalse_def ObjTrue_def)
    show ?thesis
      unfolding constant_falsity
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed logical])
       apply (simp add: pp_unary_ty_def)
      using pp_t_possibility_constant_falsity_purity_gvalid[
        where \<Gamma>="[]"]
      unfolding pp_unary_ty_def
      by simp
  next
    case identity_purity
    have logical: "pp_logical_vocabulary prop_id"
      by (simp add: pp_logical_vocabulary_def prop_id_def)
    show ?thesis
      unfolding identity_purity
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed_prop_id logical])
       apply simp
      apply (rule pp_t_possibility_identity_purity_gvalid)
      done
  next
    case negation_purity
    have typed:
        "[] \<turnstile> pp_negation_operator :
          pp_t_constants_unary_type"
      by (rule infer_type_sound)
        (simp add: pp_negation_operator_def lookup_def)
    have logical:
        "pp_logical_vocabulary pp_negation_operator"
      by (simp add: pp_logical_vocabulary_def
          pp_negation_operator_def)
    show ?thesis
      unfolding negation_purity
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed logical])
       apply simp
      apply (rule pp_t_possibility_negation_purity_gvalid)
      done
  next
    case necessity_purity
    show ?thesis
      unfolding necessity_purity pp_necessity_purity_axiom_def
        pp_unary_ty_def
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF pp_zf_eq_truth_operator_typed
          pp_zf_eq_truth_operator_logical])
       apply (simp add: pp_unary_ty_def)
      using pp_t_possibility_necessity_purity_gvalid[
        where \<Gamma>="[]"]
      unfolding pp_unary_ty_def
      by simp
  next
    case possibility_purity
    have typed:
        "[] \<turnstile> pp_possibility_operator :
          pp_t_constants_unary_type"
      by (rule infer_type_sound)
        (simp add: pp_possibility_operator_def ObjDiamond_def
          ObjBox_def ObjTrue_def lookup_def)
    show ?thesis
      unfolding possibility_purity pp_possibility_purity_axiom_def
        pp_unary_ty_def
      apply (rule pp_t_quantified_inherits_possibility_purity_gvalid[
        OF typed
          pp_possibility_operator_logical])
       apply simp
      apply (rule pp_t_possibility_operator_purity_gvalid)
      done
  next
    case target
    then show ?thesis
      using pp_t_quantified_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_quantified_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_quantified_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_quantified_no_fundamentals_gvalid[
        OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_quantified_zeroary_recombination_gvalid
      by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_quantified_unary_recombination_gvalid
      by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_quantified_zeroary_exhaustion_gvalid
      by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_quantified_unary_exhaustion_gvalid
      by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_quantified_modalized_functionality_gvalid)
qed
qed

theorem pp_t_quantified_fragment_PP_gvalid:
  "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_quantified_fragment_PP_axioms"
  unfolding
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_quantified_fragment_PP_axioms"
  then consider
      (old) "A \<in> pp_possibility_fragment_PP_axioms"
    | (leibniz_truth)
        "A = pp_pure pp_unary_ty pp_t_HO_leibniz_truth_term"
    | (leibniz_false)
        "A = pp_pure pp_unary_ty pp_t_HO_leibniz_false_term"
    | (not_leibniz_truth)
        "A = pp_pure pp_unary_ty
          pp_t_HO_not_leibniz_truth_term"
    | (not_leibniz_false)
        "A = pp_pure pp_unary_ty
          pp_t_HO_not_leibniz_false_term"
    | (forall_application)
        "A = pp_pure pp_unary_ty
          pp_t_HO_forall_application_term"
    | (exists_application)
        "A = pp_pure pp_unary_ty
          pp_t_HO_exists_application_term"
    unfolding pp_quantified_fragment_PP_axioms_def
      pp_HO_quantified_purity_axioms_def
    by blast
  then show
      "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case old
    show ?thesis
      using pp_t_quantified_old_axioms_gvalid old
      unfolding
        QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
      by blast
  next
    case leibniz_truth
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(1) by simp
  next
    case leibniz_false
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(2) by simp
  next
    case not_leibniz_truth
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(3) by simp
  next
    case not_leibniz_false
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(4) by simp
  next
    case forall_application
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(5) by simp
  next
    case exists_application
    then show ?thesis
      using pp_t_HO_quantified_purity_gvalid(6) by simp
  qed
qed

theorem pp_quantified_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_quantified_fragment_PP_axioms"
  using
    QuantifiedFragment.MovingTreeConstants.pp_t_base_sound
    QuantifiedFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_quantified_fragment_PP_gvalid
  by (rule
    QuantifiedFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_quantified_fragment_consistent:
  assumes "U \<subseteq> pp_quantified_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_quantified_fragment_PP_gvalid
    unfolding
      QuantifiedFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      QuantifiedFragment.MovingTreeConstants.pp_t_base_sound
      QuantifiedFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      QuantifiedFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
