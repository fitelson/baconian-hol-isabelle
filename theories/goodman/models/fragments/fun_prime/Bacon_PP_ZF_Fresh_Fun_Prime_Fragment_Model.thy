theory Bacon_PP_ZF_Fresh_Fun_Prime_Fragment_Model
  imports
    "Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified.Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model"
begin

section \<open>The evaluation-injectivity operator\<close>

definition pp_fun_prime_operator :: oterm where
  "pp_fun_prime_operator =
    Lam Prop (pp_fun_prime (Var 0))"

lemma typed_pp_fun_prime_operator:
  "[] \<turnstile> pp_fun_prime_operator :
    pp_t_constants_unary_type"
  unfolding pp_fun_prime_operator_def
  by (rule has_type.Lam)
    (rule typed_pp_fun_prime, rule typed_var0)

definition pp_t_fun_prime_predicate ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_fun_prime_predicate U w p \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>Y.
        Elem Y (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
        (U w X \<and> U w Y) \<longrightarrow>
        (pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p) \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type w X Y)))"

lemma pp_t_fun_prime_predicate_admissible:
  "pp_t_predicate_admissible Prop
    (pp_t_fun_prime_predicate U)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w p q v
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_eqv Prop w p q"
    and future: "prefix w v"
  have pq_v: "pp_t_eqv Prop v p q"
    by (rule pp_t_eqv_persistent[OF pq future])
  show "pp_t_fun_prime_predicate U v p =
      pp_t_fun_prime_predicate U v q"
    unfolding pp_t_fun_prime_predicate_def
  proof (intro iffI allI impI)
    fix X Y
    assume injective:
        "\<forall>X.
          Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
          (\<forall>Y.
            Elem Y (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
            (U v X \<and> U v Y) \<longrightarrow>
            (pp_t_eqv Prop v (X \<acute> p) (Y \<acute> p) \<longrightarrow>
              pp_t_eqv pp_t_constants_unary_type v X Y))"
      and X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
      and pure: "U v X \<and> U v Y"
      and at_q: "pp_t_eqv Prop v (X \<acute> q) (Y \<acute> q)"
    have at_p_q_X:
        "pp_t_eqv Prop v (X \<acute> p) (X \<acute> q)"
      by (rule pp_t_app_respects[
        OF pp_t_eqv_reflexive[OF X] p q pq_v])
    have at_p_q_Y:
        "pp_t_eqv Prop v (Y \<acute> p) (Y \<acute> q)"
      by (rule pp_t_app_respects[
        OF pp_t_eqv_reflexive[OF Y] p q pq_v])
    have at_p:
        "pp_t_eqv Prop v (X \<acute> p) (Y \<acute> p)"
      using pp_t_app_closed[OF X p]
        pp_t_app_closed[OF X q]
        pp_t_app_closed[OF Y p]
        pp_t_app_closed[OF Y q]
        at_p_q_X at_q at_p_q_Y
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    show "pp_t_eqv pp_t_constants_unary_type v X Y"
      using injective X Y pure at_p by blast
  next
    fix X Y
    assume injective:
        "\<forall>X.
          Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
          (\<forall>Y.
            Elem Y (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
            (U v X \<and> U v Y) \<longrightarrow>
            (pp_t_eqv Prop v (X \<acute> q) (Y \<acute> q) \<longrightarrow>
              pp_t_eqv pp_t_constants_unary_type v X Y))"
      and X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
      and pure: "U v X \<and> U v Y"
      and at_p: "pp_t_eqv Prop v (X \<acute> p) (Y \<acute> p)"
    have qp_v: "pp_t_eqv Prop v q p"
      by (rule pp_t_eqv_symmetric[OF p q pq_v])
    have at_q_p_X:
        "pp_t_eqv Prop v (X \<acute> q) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF pp_t_eqv_reflexive[OF X] q p qp_v])
    have at_q_p_Y:
        "pp_t_eqv Prop v (Y \<acute> q) (Y \<acute> p)"
      by (rule pp_t_app_respects[
        OF pp_t_eqv_reflexive[OF Y] q p qp_v])
    have at_q:
        "pp_t_eqv Prop v (X \<acute> q) (Y \<acute> q)"
      using pp_t_app_closed[OF X p]
        pp_t_app_closed[OF X q]
        pp_t_app_closed[OF Y p]
        pp_t_app_closed[OF Y q]
        at_q_p_X at_p at_q_p_Y
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    show "pp_t_eqv pp_t_constants_unary_type v X Y"
      using injective X Y pure at_q by blast
  qed
qed

definition pp_t_fun_prime_operator_for ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF"
where
  "pp_t_fun_prime_operator_for U =
    pp_t_classifier Prop (pp_t_fun_prime_predicate U)"

lemma pp_t_fun_prime_operator_for_in_domain:
  "Elem (pp_t_fun_prime_operator_for U)
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_fun_prime_operator_for_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_fun_prime_predicate_admissible)

lemma pp_t_fun_prime_operator_for_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_fun_prime_operator_for U \<acute> p) w
    \<longleftrightarrow> pp_t_fun_prime_predicate U w p"
  unfolding pp_t_fun_prime_operator_for_def
  using pp_t_classifier_holds[OF p] .

definition pp_t_quantified_fun_prime_operator :: ZF where
  "pp_t_quantified_fun_prime_operator =
    pp_t_fun_prime_operator_for pp_t_quantified_unary_pure"

lemma pp_t_quantified_fun_prime_operator_in_domain:
  "Elem pp_t_quantified_fun_prime_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_quantified_fun_prime_operator_def
  by (rule pp_t_fun_prime_operator_for_in_domain)

lemma pp_t_quantified_fun_prime_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> p) w
    \<longleftrightarrow>
      pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
  unfolding pp_t_quantified_fun_prime_operator_def
  by (rule pp_t_fun_prime_operator_for_holds[OF p])

lemma pp_t_quantified_unary_pure_classes:
  "pp_t_quantified_unary_pure w X \<longleftrightarrow>
    pp_t_eqv pp_t_constants_unary_type
      w pp_t_identity_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_negation_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w (pp_t_constant_operator True) X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w (pp_t_constant_operator False) X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_necessity_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_possibility_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_necessary_falsity_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_possible_falsity_operator X"
  unfolding pp_t_quantified_unary_pure_def
    pp_t_possibility_fragment_pure_def
    pp_t_necessity_fragment_pure_def
    pp_t_binary_truth_fragment_pure_def
    pp_t_conjunction_fragment_pure_def
    pp_t_constant_builder_fragment_pure_def
    pp_t_constants_fragment_pure_def
    pp_t_constants_unary_pure_def
    pp_t_idneg_unary_pure_def
  by simp

definition pp_t_fun_prime_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_fun_prime_unary_pure w X \<longleftrightarrow>
    pp_t_quantified_unary_pure w X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_quantified_fun_prime_operator X"

lemma pp_t_fun_prime_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    pp_t_fun_prime_unary_pure"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        pp_t_quantified_unary_pure"
    by (rule pp_t_quantified_unary_pure_admissible)
  have added:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator X)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_quantified_fun_prime_operator_in_domain] .
  show ?thesis
    using old added
    unfolding pp_t_predicate_admissible_def
      pp_t_fun_prime_unary_pure_def
    by blast
qed

definition pp_t_fun_prime_stock_classifier :: ZF where
  "pp_t_fun_prime_stock_classifier =
    pp_t_classifier pp_t_constants_unary_type
      pp_t_fun_prime_unary_pure"

lemma pp_t_fun_prime_stock_classifier_in_domain:
  "Elem pp_t_fun_prime_stock_classifier
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_fun_prime_stock_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_fun_prime_unary_pure_admissible)

definition pp_t_fun_prime_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_fun_prime_fragment_pure \<sigma> w x \<longleftrightarrow>
    (pp_t_quantified_fragment_pure \<sigma> w x
      \<and> \<sigma> \<noteq> pp_t_constants_classifier_type)
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator x)
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type
        w pp_t_fun_prime_stock_classifier x)"

lemma pp_t_fun_prime_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_fun_prime_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_quantified_fragment_pure \<sigma>)"
    by (rule pp_t_quantified_fragment_pure_admissible)
  have added:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_quantified_fun_prime_operator_in_domain] .
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type
          w pp_t_fun_prime_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_fun_prime_stock_classifier_in_domain] .
  show ?thesis
    unfolding pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_eqv \<sigma> w x y"
      and future: "prefix w v"
    have old_iff:
        "pp_t_quantified_fragment_pure \<sigma> v x
          \<longleftrightarrow>
         pp_t_quantified_fragment_pure \<sigma> v y"
      using old x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have added_iff:
        "\<sigma> = pp_t_constants_unary_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_quantified_fun_prime_operator x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_quantified_fun_prime_operator y"
      using added x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have classifier_iff:
        "\<sigma> = pp_t_constants_classifier_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_classifier_type v
            pp_t_fun_prime_stock_classifier x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_classifier_type v
            pp_t_fun_prime_stock_classifier y"
      using classifier x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    show "pp_t_fun_prime_fragment_pure \<sigma> v x =
        pp_t_fun_prime_fragment_pure \<sigma> v y"
      unfolding pp_t_fun_prime_fragment_pure_def
      using old_iff added_iff classifier_iff by blast
  qed
qed

interpretation FunPrimeFragment:
  pp_t_moving_internal_parameters
    pp_t_fun_prime_fragment_pure
  by standard
    (rule pp_t_fun_prime_fragment_pure_admissible)

abbreviation pp_t_fun_prime_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_fun_prime_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_fun_prime_fragment_pure"

lemma pp_t_fun_prime_pure_unary_iff:
  "pp_t_fun_prime_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow> pp_t_fun_prime_unary_pure w X"
  unfolding pp_t_fun_prime_fragment_pure_def
    pp_t_fun_prime_unary_pure_def
    pp_t_quantified_pure_unary_iff
  by simp

lemma pp_t_fun_prime_pure_Prop_iff:
  "pp_t_fun_prime_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_quantified_fragment_pure Prop w P"
  unfolding pp_t_fun_prime_fragment_pure_def by simp

lemma pp_t_fun_prime_pure_classifier_iff:
  "pp_t_fun_prime_fragment_pure
      pp_t_constants_classifier_type w C
    \<longleftrightarrow>
    pp_t_eqv pp_t_constants_classifier_type
      w pp_t_fun_prime_stock_classifier C"
  unfolding pp_t_fun_prime_fragment_pure_def by simp

lemma pp_t_fun_prime_added_is_pure[simp]:
  "pp_t_fun_prime_fragment_pure
    pp_t_constants_unary_type w
    pp_t_quantified_fun_prime_operator"
  unfolding pp_t_fun_prime_pure_unary_iff
    pp_t_fun_prime_unary_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_quantified_fun_prime_operator_in_domain]
  by blast

lemma pp_t_fun_prime_classifier_is_pure[simp]:
  "pp_t_fun_prime_fragment_pure
    pp_t_constants_classifier_type w
    pp_t_fun_prime_stock_classifier"
  unfolding pp_t_fun_prime_pure_classifier_iff
  by (rule pp_t_eqv_reflexive[
    OF pp_t_fun_prime_stock_classifier_in_domain])

lemma pp_t_necessity_not_constant_false:
  "\<not> pp_t_eqv pp_t_constants_unary_type w
    pp_t_necessity_operator (pp_t_constant_operator False)"
proof
  assume operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_necessity_operator (pp_t_constant_operator False)"
  have truth: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have applications:
      "pp_t_eqv Prop w
        (pp_t_necessity_operator \<acute> pp_zf_truth True)
        (pp_t_constant_operator False \<acute> pp_zf_truth True)"
    by (rule pp_t_app_respects[
      OF operators truth truth pp_t_eqv_reflexive[OF truth]])
  have at_w:
      "pp_t_holds
          (pp_t_necessity_operator \<acute> pp_zf_truth True) w
        \<longleftrightarrow>
       pp_t_holds
          (pp_t_constant_operator False \<acute> pp_zf_truth True) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  show False
    using at_w
      pp_t_necessity_operator_holds[OF truth, of w]
      pp_t_constant_operator_holds[OF truth, of False w]
      pp_t_eqv_reflexive[OF truth, of w]
    by simp
qed

lemma pp_t_necessary_falsity_not_constant_false:
  "\<not> pp_t_eqv pp_t_constants_unary_type w
    pp_t_necessary_falsity_operator (pp_t_constant_operator False)"
proof
  assume operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_necessary_falsity_operator
        (pp_t_constant_operator False)"
  have falsity: "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have applications:
      "pp_t_eqv Prop w
        (pp_t_necessary_falsity_operator \<acute> pp_zf_truth False)
        (pp_t_constant_operator False \<acute> pp_zf_truth False)"
    by (rule pp_t_app_respects[
      OF operators falsity falsity pp_t_eqv_reflexive[OF falsity]])
  have at_w:
      "pp_t_holds
          (pp_t_necessary_falsity_operator \<acute> pp_zf_truth False) w
        \<longleftrightarrow>
       pp_t_holds
          (pp_t_constant_operator False \<acute> pp_zf_truth False) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  have false_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth False) (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF falsity])
  show False
    using at_w
      pp_t_necessary_falsity_operator_holds[OF falsity, of w]
      pp_t_constant_operator_holds[OF falsity, of False w]
      false_refl
    by simp
qed

lemma pp_t_base_injective_has_homogeneous_cones:
  assumes p: "Elem p (pp_t_domain Prop)"
    and injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
  obtains u v where
      "prefix w u"
      "pp_t_eqv Prop u p (pp_zf_truth True)"
      "prefix w v"
      "pp_t_eqv Prop v p (pp_zf_truth False)"
proof -
  have necessity_pure:
      "pp_t_quantified_unary_pure w pp_t_necessity_operator"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_necessity_operator_in_domain]
    by blast
  have necessary_falsity_pure:
      "pp_t_quantified_unary_pure
        w pp_t_necessary_falsity_operator"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_necessary_falsity_operator_in_domain]
    by blast
  have false_pure:
      "pp_t_quantified_unary_pure
        w (pp_t_constant_operator False)"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain]
    by blast
  have not_box_false:
      "\<not> pp_t_eqv Prop w
        (pp_t_necessity_operator \<acute> p)
        (pp_t_constant_operator False \<acute> p)"
  proof
    assume applications:
        "pp_t_eqv Prop w
          (pp_t_necessity_operator \<acute> p)
          (pp_t_constant_operator False \<acute> p)"
    have operators:
        "pp_t_eqv pp_t_constants_unary_type w
          pp_t_necessity_operator (pp_t_constant_operator False)"
      using injective
        pp_t_necessity_operator_in_domain
        pp_t_constant_operator_in_domain
        necessity_pure false_pure applications
      unfolding pp_t_fun_prime_predicate_def by blast
    show False
      using pp_t_necessity_not_constant_false[of w] operators
      by blast
  qed
  obtain u where wu: "prefix w u"
    and box_u:
      "pp_t_holds (pp_t_necessity_operator \<acute> p) u"
  proof -
    have "\<exists>u. prefix w u \<and>
        pp_t_holds (pp_t_necessity_operator \<acute> p) u"
      using not_box_false
      unfolding pp_t_eqv.simps
      using pp_t_constant_operator_holds[OF p, of False]
      by blast
    then show ?thesis using that by blast
  qed
  have p_true:
      "pp_t_eqv Prop u p (pp_zf_truth True)"
    using pp_t_necessity_operator_holds[OF p, of u] box_u
    by blast
  have not_box_neg_false:
      "\<not> pp_t_eqv Prop w
        (pp_t_necessary_falsity_operator \<acute> p)
        (pp_t_constant_operator False \<acute> p)"
  proof
    assume applications:
        "pp_t_eqv Prop w
          (pp_t_necessary_falsity_operator \<acute> p)
          (pp_t_constant_operator False \<acute> p)"
    have operators:
        "pp_t_eqv pp_t_constants_unary_type w
          pp_t_necessary_falsity_operator
          (pp_t_constant_operator False)"
      using injective
        pp_t_necessary_falsity_operator_in_domain
        pp_t_constant_operator_in_domain
        necessary_falsity_pure false_pure applications
      unfolding pp_t_fun_prime_predicate_def by blast
    show False
      using pp_t_necessary_falsity_not_constant_false[of w]
        operators
      by blast
  qed
  obtain v where wv: "prefix w v"
    and box_neg_v:
      "pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) v"
  proof -
    have "\<exists>v. prefix w v \<and>
        pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) v"
      using not_box_neg_false
      unfolding pp_t_eqv.simps
      using pp_t_constant_operator_holds[OF p, of False]
      by blast
    then show ?thesis using that by blast
  qed
  have p_false:
      "pp_t_eqv Prop v p (pp_zf_truth False)"
    using pp_t_necessary_falsity_operator_holds[OF p, of v]
      box_neg_v
    by blast
  show ?thesis
    using that[OF wu p_true wv p_false] .
qed

lemma pp_t_identity_not_constant:
  "\<not> pp_t_eqv pp_t_constants_unary_type w
    pp_t_identity_operator (pp_t_constant_operator b)"
proof
  assume operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_identity_operator (pp_t_constant_operator b)"
  let ?q = "pp_zf_truth (\<not> b)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have applications:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> ?q)
        (pp_t_constant_operator b \<acute> ?q)"
    by (rule pp_t_app_respects[
      OF operators q q pp_t_eqv_reflexive[OF q]])
  have at_w:
      "pp_t_holds (pp_t_identity_operator \<acute> ?q) w
        \<longleftrightarrow>
       pp_t_holds (pp_t_constant_operator b \<acute> ?q) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  show False
    using q at_w
    by (cases b)
      (simp_all add: pp_t_identity_operator_def Lambda_app
        pp_t_constant_operator_holds)
qed

lemma pp_t_fun_prime_fails_on_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "\<not> pp_t_fun_prime_predicate
    pp_t_quantified_unary_pure w p"
proof
  assume injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
  have identity_pure:
      "pp_t_quantified_unary_pure w pp_t_identity_operator"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_identity_operator_in_domain]
    by blast
  have constant_pure:
      "pp_t_quantified_unary_pure w (pp_t_constant_operator b)"
  proof (cases b)
    case False
    have refl:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_constant_operator False)
          (pp_t_constant_operator False)"
      by (rule pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain])
    show ?thesis
      apply (subst False)
      unfolding pp_t_quantified_unary_pure_classes
      using refl by blast
  next
    case True
    have refl:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_constant_operator True)
          (pp_t_constant_operator True)"
      by (rule pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain])
    show ?thesis
      apply (subst True)
      unfolding pp_t_quantified_unary_pure_classes
      using refl by blast
  qed
  have applications:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> p)
        (pp_t_constant_operator b \<acute> p)"
  proof -
    have identity_p:
        "pp_t_identity_operator \<acute> p = p"
      using p by (simp add: pp_t_identity_operator_def Lambda_app)
    have constant_p:
        "pp_t_constant_operator b \<acute> p = pp_zf_truth b"
      by (rule pp_t_constant_operator_apply[OF p])
    show ?thesis
      using settled unfolding identity_p constant_p .
  qed
  have operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_identity_operator (pp_t_constant_operator b)"
    using injective pp_t_identity_operator_in_domain
      pp_t_constant_operator_in_domain
      identity_pure constant_pure applications
    unfolding pp_t_fun_prime_predicate_def by blast
  show False
    using pp_t_identity_not_constant[of w b] operators by blast
qed

lemma pp_t_quantified_fun_prime_false_on_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "\<not> pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute> p) w"
  using pp_t_quantified_fun_prime_operator_holds[OF p, of w]
    pp_t_fun_prime_fails_on_settled[OF p settled]
  by blast

lemma pp_t_base_injective_added_noncollision:
  assumes p: "Elem p (pp_t_domain Prop)"
    and injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
    and X: "pp_t_quantified_unary_pure w X"
    and X_typed:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
  shows "\<not> pp_t_eqv Prop w
    (pp_t_quantified_fun_prime_operator \<acute> p) (X \<acute> p)"
proof -
  let ?Jp = "pp_t_quantified_fun_prime_operator \<acute> p"
  have J_now: "pp_t_holds ?Jp w"
    using pp_t_quantified_fun_prime_operator_holds[OF p, of w]
      injective by blast
  obtain u v where wu: "prefix w u"
    and p_true: "pp_t_eqv Prop u p (pp_zf_truth True)"
    and wv: "prefix w v"
    and p_false: "pp_t_eqv Prop v p (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF p injective] by blast
  have J_u: "\<not> pp_t_holds ?Jp u"
    using pp_t_quantified_fun_prime_false_on_settled[
      OF p p_true] .
  have J_v: "\<not> pp_t_holds ?Jp v"
    using pp_t_quantified_fun_prime_false_on_settled[
      OF p p_false] .
  have p_u: "pp_t_holds p u"
    using pp_t_prop_eqv_at[OF p_true, of u] by simp
  have not_p_v: "\<not> pp_t_holds p v"
    using pp_t_prop_eqv_at[OF p_false, of v] by simp
  from X consider
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
    | (necessity)
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessity_operator X"
    | (possibility)
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possibility_operator X"
    | (necessary_falsity)
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator X"
    | (possible_falsity)
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_possible_falsity_operator X"
    unfolding pp_t_quantified_unary_pure_classes by blast
  then show ?thesis
  proof cases
    case identity
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_identity_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF identity p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JI: "pp_t_eqv Prop w
          ?Jp (pp_t_identity_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_identity_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      show False
      proof (cases "pp_t_holds p w")
        case True
        have at_u:
            "pp_t_holds ?Jp u \<longleftrightarrow>
             pp_t_holds (pp_t_identity_operator \<acute> p) u"
          using pp_t_prop_eqv_at[OF JI wu] .
        show False
          using J_u p_u at_u p
          by (simp add: pp_t_identity_operator_def Lambda_app)
      next
        case False
        have at_w:
            "pp_t_holds ?Jp w \<longleftrightarrow>
             pp_t_holds (pp_t_identity_operator \<acute> p) w"
          using pp_t_prop_eqv_at[OF JI, of w] by simp
        show False
          using J_now False at_w p
          by (simp add: pp_t_identity_operator_def Lambda_app)
      qed
    qed
  next
    case negation
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_negation_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF negation p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JN: "pp_t_eqv Prop w
          ?Jp (pp_t_negation_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_negation_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      show False
      proof (cases "pp_t_holds p w")
        case True
        have at_w:
            "pp_t_holds ?Jp w \<longleftrightarrow>
             pp_t_holds (pp_t_negation_operator \<acute> p) w"
          using pp_t_prop_eqv_at[OF JN, of w] by simp
        show False
          using J_now True at_w
            pp_t_negation_operator_holds[OF p, of w]
          by blast
      next
        case False
        have at_v:
            "pp_t_holds ?Jp v \<longleftrightarrow>
             pp_t_holds (pp_t_negation_operator \<acute> p) v"
          using pp_t_prop_eqv_at[OF JN wv] .
        show False
          using J_v not_p_v at_v
            pp_t_negation_operator_holds[OF p, of v]
          by blast
      qed
    qed
  next
    case truth
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_constant_operator True \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF truth p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JT: "pp_t_eqv Prop w
          ?Jp (pp_t_constant_operator True \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_constant_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_u:
          "pp_t_holds ?Jp u \<longleftrightarrow>
           pp_t_holds (pp_t_constant_operator True \<acute> p) u"
        using pp_t_prop_eqv_at[OF JT wu] .
      show False
        using J_u at_u pp_t_constant_operator_holds[OF p, of True u]
        by blast
    qed
  next
    case falsity
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_constant_operator False \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF falsity p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JF: "pp_t_eqv Prop w
          ?Jp (pp_t_constant_operator False \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_constant_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_w:
          "pp_t_holds ?Jp w \<longleftrightarrow>
           pp_t_holds (pp_t_constant_operator False \<acute> p) w"
        using pp_t_prop_eqv_at[OF JF, of w] by simp
      show False
        using J_now at_w
          pp_t_constant_operator_holds[OF p, of False w]
        by blast
    qed
  next
    case necessity
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_necessity_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF necessity p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JB: "pp_t_eqv Prop w
          ?Jp (pp_t_necessity_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_necessity_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_u:
          "pp_t_holds ?Jp u \<longleftrightarrow>
           pp_t_holds (pp_t_necessity_operator \<acute> p) u"
        using pp_t_prop_eqv_at[OF JB wu] .
      show False
        using J_u at_u
          pp_t_necessity_operator_holds[OF p, of u] p_true
        by blast
    qed
  next
    case possibility
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_possibility_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF possibility p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JM: "pp_t_eqv Prop w
          ?Jp (pp_t_possibility_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[OF pp_t_possibility_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_u:
          "pp_t_holds ?Jp u \<longleftrightarrow>
           pp_t_holds (pp_t_possibility_operator \<acute> p) u"
        using pp_t_prop_eqv_at[OF JM wu] .
      have possible_u:
          "pp_t_holds (pp_t_possibility_operator \<acute> p) u"
        using pp_t_possibility_operator_holds[OF p, of u]
          p_u by blast
      show False using J_u at_u possible_u by blast
    qed
  next
    case necessary_falsity
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_necessary_falsity_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF necessary_falsity p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JBN: "pp_t_eqv Prop w
          ?Jp (pp_t_necessary_falsity_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[
            OF pp_t_necessary_falsity_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_v:
          "pp_t_holds ?Jp v \<longleftrightarrow>
           pp_t_holds (pp_t_necessary_falsity_operator \<acute> p) v"
        using pp_t_prop_eqv_at[OF JBN wv] .
      show False
        using J_v at_v
          pp_t_necessary_falsity_operator_holds[OF p, of v]
          p_false
        by blast
    qed
  next
    case possible_falsity
    have transfer:
        "pp_t_eqv Prop w
          (pp_t_possible_falsity_operator \<acute> p) (X \<acute> p)"
      by (rule pp_t_app_respects[
        OF possible_falsity p p pp_t_eqv_reflexive[OF p]])
    show ?thesis
    proof
      assume JX: "pp_t_eqv Prop w ?Jp (X \<acute> p)"
      have JMN: "pp_t_eqv Prop w
          ?Jp (pp_t_possible_falsity_operator \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X_typed p]
          pp_t_app_closed[
            OF pp_t_possible_falsity_operator_in_domain p]
          JX transfer
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have at_v:
          "pp_t_holds ?Jp v \<longleftrightarrow>
           pp_t_holds (pp_t_possible_falsity_operator \<acute> p) v"
        using pp_t_prop_eqv_at[OF JMN wv] .
      have not_true_v:
          "\<not> pp_t_eqv Prop v p (pp_zf_truth True)"
      proof
        assume p_true_v:
            "pp_t_eqv Prop v p (pp_zf_truth True)"
        have true_false:
            "pp_t_eqv Prop v
              (pp_zf_truth True) (pp_zf_truth False)"
          using p pp_t_truth_in_domain p_true_v p_false
          by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
        have at_v':
            "pp_t_holds (pp_zf_truth True) v
              \<longleftrightarrow> pp_t_holds (pp_zf_truth False) v"
          using pp_t_prop_eqv_at[OF true_false, of v] by simp
        show False using at_v' by simp
      qed
      show False
        using J_v at_v
          pp_t_possible_falsity_operator_holds[OF p, of v]
          not_true_v
        by blast
    qed
  qed
qed

theorem pp_t_fun_prime_stabilizes:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_fun_prime_predicate
      pp_t_fun_prime_unary_pure w p
    \<longleftrightarrow>
    pp_t_fun_prime_predicate
      pp_t_quantified_unary_pure w p"
proof
  assume enlarged:
      "pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p"
  show "pp_t_fun_prime_predicate
      pp_t_quantified_unary_pure w p"
    unfolding pp_t_fun_prime_predicate_def
  proof (intro allI impI)
    fix X Y
    assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
      and old: "pp_t_quantified_unary_pure w X
        \<and> pp_t_quantified_unary_pure w Y"
      and outputs: "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
    have old_X: "pp_t_quantified_unary_pure w X"
      using old by blast
    have old_Y: "pp_t_quantified_unary_pure w Y"
      using old by blast
    have new_X: "pp_t_fun_prime_unary_pure w X"
      using old_X unfolding pp_t_fun_prime_unary_pure_def by blast
    have new_Y: "pp_t_fun_prime_unary_pure w Y"
      using old_Y unfolding pp_t_fun_prime_unary_pure_def by blast
    show "pp_t_eqv pp_t_constants_unary_type w X Y"
      using enlarged X Y new_X new_Y outputs
      unfolding pp_t_fun_prime_predicate_def by blast
  qed
next
  assume base:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
  show "pp_t_fun_prime_predicate
      pp_t_fun_prime_unary_pure w p"
    unfolding pp_t_fun_prime_predicate_def
  proof (intro allI impI)
    fix X Y
    assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
      and new: "pp_t_fun_prime_unary_pure w X
        \<and> pp_t_fun_prime_unary_pure w Y"
      and outputs: "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
    have new_X: "pp_t_fun_prime_unary_pure w X"
      using new by blast
    have new_Y: "pp_t_fun_prime_unary_pure w Y"
      using new by blast
    have X_cases:
        "pp_t_quantified_unary_pure w X
          \<or> pp_t_eqv pp_t_constants_unary_type
            w pp_t_quantified_fun_prime_operator X"
      using new_X unfolding pp_t_fun_prime_unary_pure_def .
    have Y_cases:
        "pp_t_quantified_unary_pure w Y
          \<or> pp_t_eqv pp_t_constants_unary_type
            w pp_t_quantified_fun_prime_operator Y"
      using new_Y unfolding pp_t_fun_prime_unary_pure_def .
    have old_old:
        "pp_t_quantified_unary_pure w X \<Longrightarrow>
         pp_t_quantified_unary_pure w Y \<Longrightarrow>
         pp_t_eqv pp_t_constants_unary_type w X Y"
      using base X Y outputs
      unfolding pp_t_fun_prime_predicate_def by blast
    have old_J_impossible:
        "pp_t_quantified_unary_pure w X \<Longrightarrow>
         pp_t_eqv pp_t_constants_unary_type
           w pp_t_quantified_fun_prime_operator Y \<Longrightarrow>
         False"
    proof -
      assume old_X: "pp_t_quantified_unary_pure w X"
        and J_Y: "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator Y"
      have Jp_Yp:
          "pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (Y \<acute> p)"
        by (rule pp_t_app_respects[
          OF J_Y p p pp_t_eqv_reflexive[OF p]])
      have Xp_Jp:
          "pp_t_eqv Prop w
            (X \<acute> p)
            (pp_t_quantified_fun_prime_operator \<acute> p)"
        using pp_t_app_closed[OF X p]
          pp_t_app_closed[OF Y p]
          pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          outputs Jp_Yp
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have contradiction:
          "\<not> pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (X \<acute> p)"
        by (rule pp_t_base_injective_added_noncollision[
          OF p base old_X X])
      have Jp_Xp:
          "pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (X \<acute> p)"
        by (rule pp_t_eqv_symmetric[
            OF pp_t_app_closed[OF X p]
              pp_t_app_closed[
                OF pp_t_quantified_fun_prime_operator_in_domain p]
            Xp_Jp])
      show False using contradiction Jp_Xp by blast
    qed
    have J_old_impossible:
        "pp_t_eqv pp_t_constants_unary_type
           w pp_t_quantified_fun_prime_operator X \<Longrightarrow>
         pp_t_quantified_unary_pure w Y \<Longrightarrow>
         False"
    proof -
      assume J_X: "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator X"
        and old_Y: "pp_t_quantified_unary_pure w Y"
      have Jp_Xp:
          "pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (X \<acute> p)"
        by (rule pp_t_app_respects[
          OF J_X p p pp_t_eqv_reflexive[OF p]])
      have Jp_Yp:
          "pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (Y \<acute> p)"
        using pp_t_app_closed[
            OF pp_t_quantified_fun_prime_operator_in_domain p]
          pp_t_app_closed[OF X p]
          pp_t_app_closed[OF Y p]
          Jp_Xp outputs
        by (meson pp_t_eqv_transitive)
      have contradiction:
          "\<not> pp_t_eqv Prop w
            (pp_t_quantified_fun_prime_operator \<acute> p)
            (Y \<acute> p)"
        by (rule pp_t_base_injective_added_noncollision[
          OF p base old_Y Y])
      show False using contradiction Jp_Yp by blast
    qed
    have J_J:
        "pp_t_eqv pp_t_constants_unary_type
           w pp_t_quantified_fun_prime_operator X \<Longrightarrow>
         pp_t_eqv pp_t_constants_unary_type
           w pp_t_quantified_fun_prime_operator Y \<Longrightarrow>
         pp_t_eqv pp_t_constants_unary_type w X Y"
    proof -
      assume J_X: "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator X"
        and J_Y: "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator Y"
      have XJ:
          "pp_t_eqv pp_t_constants_unary_type
            w X pp_t_quantified_fun_prime_operator"
        by (rule pp_t_eqv_symmetric[
          OF pp_t_quantified_fun_prime_operator_in_domain X J_X])
      show ?thesis
        by (rule pp_t_eqv_transitive[
          OF X pp_t_quantified_fun_prime_operator_in_domain Y
            XJ J_Y])
    qed
    show "pp_t_eqv pp_t_constants_unary_type w X Y"
      using X_cases Y_cases old_old old_J_impossible
        J_old_impossible J_J
      by blast
  qed
qed

corollary pp_t_fun_prime_operator_is_fixed_point:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_fun_prime_operator_for
        pp_t_fun_prime_unary_pure \<acute> p) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> p) w"
  unfolding pp_t_quantified_fun_prime_operator_def
  using pp_t_fun_prime_operator_for_holds[OF p]
    pp_t_fun_prime_stabilizes[OF p]
  by blast

lemma pp_t_eval_fun_prime_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants
        pp_t_closed_env pp_fun_prime_operator \<acute> p) w
    \<longleftrightarrow>
      pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p"
proof -
  have beta:
      "pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_fun_prime_operator \<acute> p
        =
       pp_t_eval pp_t_fun_prime_fragment_constants
          (extend_env p pp_t_closed_env)
          (pp_fun_prime (Var 0))"
    unfolding pp_fun_prime_operator_def
    using p by (simp add: Lambda_app)
  show ?thesis
    unfolding beta pp_fun_prime_def
      pp_t_fun_prime_predicate_def pp_pure_def
    using p
    apply (simp only: pp_t_eval_Forall_holds
      pp_t_eval_Imp_holds pp_t_eval_Conj_holds
      pp_t_eval_Eq_holds)
    apply (simp del: pp_t_eqv.simps
      add: pp_t_classifier_holds extend_env.simps
      pp_t_three_extensions_index_two shift_by_def shift_ren_def
      pp_t_fun_prime_pure_unary_iff)
    apply (simp only: pp_t_fun_prime_pure_unary_iff
      pp_unary_ty_def)
    by simp
qed

theorem pp_t_eval_fun_prime_operator:
  "pp_t_eval pp_t_fun_prime_fragment_constants
      pp_t_closed_env pp_fun_prime_operator
    = pp_t_quantified_fun_prime_operator"
proof -
  let ?J =
    "pp_t_eval pp_t_fun_prime_fragment_constants
      pp_t_closed_env pp_fun_prime_operator"
  have J_domain:
      "Elem ?J (pp_t_domain pp_t_constants_unary_type)"
    using
      FunPrimeFragment.MovingTreeConstants.pp_t_eval_type[
        OF typed_pp_fun_prime_operator pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have root_eqv:
      "pp_t_eqv pp_t_constants_unary_type []
        ?J pp_t_quantified_fun_prime_operator"
  proof (rule pp_t_arrow_eqv_if_pointwise[
      OF J_domain pp_t_quantified_fun_prime_operator_in_domain])
    show "\<forall>v. prefix [] v \<longrightarrow>
        (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
          pp_t_eqv Prop v
            (?J \<acute> p)
            (pp_t_quantified_fun_prime_operator \<acute> p))"
      unfolding pp_t_eqv.simps
      using pp_t_eval_fun_prime_operator_holds
        pp_t_quantified_fun_prime_operator_holds
        pp_t_fun_prime_stabilizes
      by blast
  qed
  show ?thesis
    using pp_t_root_eqv_iff_eq[
      OF J_domain pp_t_quantified_fun_prime_operator_in_domain]
      root_eqv by blast
qed

theorem pp_t_fun_prime_operator_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_fun_prime_operator)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have evaluated:
      "pp_t_eval pp_t_fun_prime_fragment_constants
        \<rho> pp_fun_prime_operator
       = pp_t_quantified_fun_prime_operator"
  proof -
    have independent:
        "pp_t_eval pp_t_fun_prime_fragment_constants
            \<rho> pp_fun_prime_operator
          =
         pp_t_eval pp_t_fun_prime_fragment_constants
            pp_t_closed_env pp_fun_prime_operator"
    proof -
      have left:
          "Elem
            (pp_t_eval pp_t_fun_prime_fragment_constants
              \<rho> pp_fun_prime_operator)
            (pp_t_domain pp_t_constants_unary_type)"
        using
          FunPrimeFragment.MovingTreeConstants.pp_t_eval_type[
            OF typed_pp_fun_prime_operator env]
        by (simp add: pp_t_dom_def)
      have right:
          "Elem
            (pp_t_eval pp_t_fun_prime_fragment_constants
              pp_t_closed_env pp_fun_prime_operator)
            (pp_t_domain pp_t_constants_unary_type)"
        using
          FunPrimeFragment.MovingTreeConstants.pp_t_eval_type[
            OF typed_pp_fun_prime_operator pp_t_empty_env_typed]
        by (simp add: pp_t_dom_def)
      have related:
          "pp_t_eqv pp_t_constants_unary_type []
            (pp_t_eval pp_t_fun_prime_fragment_constants
              \<rho> pp_fun_prime_operator)
            (pp_t_eval pp_t_fun_prime_fragment_constants
              pp_t_closed_env pp_fun_prime_operator)"
        by (rule
          FunPrimeFragment.MovingTreeConstants.pp_t_eval_respects[
            OF typed_pp_fun_prime_operator pp_t_empty_env_eqv])
      show ?thesis
        using pp_t_root_eqv_iff_eq[OF left right] related by blast
    qed
    show ?thesis
      by (simp add: independent pp_t_eval_fun_prime_operator)
  qed
  have pure:
      "pp_t_fun_prime_fragment_pure
        pp_t_constants_unary_type w
        (pp_t_eval pp_t_fun_prime_fragment_constants
          \<rho> pp_fun_prime_operator)"
    unfolding evaluated by simp
  show ?thesis
    using FunPrimeFragment.pp_t_moving_eval_pure_holds[
      OF typed_pp_fun_prime_operator env, of w]
      pure by blast
qed

section \<open>Application closure of the enlarged stock\<close>

lemma pp_t_quantified_pure_function_from_unary:
  assumes pure:
      "pp_t_quantified_fragment_pure
        (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
  shows "\<tau> = Prop"
  using pure
    pp_t_possibility_pure_function_from_unary[
      of \<tau> w f]
  unfolding pp_t_quantified_fragment_pure_def
  by (cases \<tau>) auto

lemma pp_t_fun_prime_old_input:
  assumes pure_f:
      "pp_t_quantified_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and retained:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
        \<noteq> pp_t_constants_classifier_type"
    and pure_x:
      "pp_t_fun_prime_fragment_pure \<sigma> w x"
  shows "pp_t_quantified_fragment_pure \<sigma> w x"
proof -
  from pure_x consider
      (old)
        "pp_t_quantified_fragment_pure \<sigma> w x"
        "\<sigma> \<noteq> pp_t_constants_classifier_type"
    | (added)
        "\<sigma> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator x"
    | (classifier)
        "\<sigma> = pp_t_constants_classifier_type"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_fun_prime_stock_classifier x"
    unfolding pp_t_fun_prime_fragment_pure_def
    by blast
  then show ?thesis
  proof cases
    case old
    then show ?thesis by blast
  next
    case added
    have pure_from_unary:
        "pp_t_quantified_fragment_pure
          (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f"
      using pure_f added by simp
    have tau: "\<tau> = Prop"
      by (rule pp_t_quantified_pure_function_from_unary[
        OF pure_from_unary])
    have False
      using retained added tau by simp
    then show ?thesis by blast
  next
    case classifier
    have no_old:
        "\<not> pp_t_quantified_fragment_pure
          (pp_t_constants_classifier_type \<rightarrow>\<^sub>o \<tau>) w f"
      unfolding pp_t_quantified_fragment_pure_def
        pp_t_possibility_fragment_pure_def
        pp_t_necessity_fragment_pure_def
        pp_t_binary_truth_fragment_pure_def
        pp_t_conjunction_fragment_pure_def
        pp_t_constant_builder_fragment_pure_def
        pp_t_constants_fragment_pure_def
      by (cases \<tau>) auto
    show ?thesis
      using no_old pure_f classifier by simp
  qed
qed

lemma pp_t_fun_prime_added_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator f"
    and pure_p:
      "pp_t_fun_prime_fragment_pure Prop w p"
  shows "pp_t_fun_prime_fragment_pure Prop w (f \<acute> p)"
proof -
  have old_p:
      "pp_t_quantified_fragment_pure Prop w p"
    using pure_p unfolding pp_t_fun_prime_pure_Prop_iff .
  have classes:
      "pp_t_eqv Prop w (pp_zf_truth True) p
        \<or> pp_t_eqv Prop w (pp_zf_truth False) p"
    using old_p
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    by blast
  then obtain b where bp:
      "pp_t_eqv Prop w (pp_zf_truth b) p"
    by (metis (full_types) bool.exhaust)
  have pb:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
    by (rule pp_t_eqv_symmetric[
      OF pp_t_truth_in_domain p bp])
  have J_false:
      "\<not> pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> p) w"
    by (rule pp_t_quantified_fun_prime_false_on_settled[
      OF p pb])
  have pp: "pp_t_eqv Prop w p p"
    by (rule pp_t_eqv_reflexive[OF p])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_quantified_fun_prime_operator \<acute> p)
        (f \<acute> p)"
    by (rule pp_t_app_respects[
      OF representative p p pp])
  have f_false: "\<not> pp_t_holds (f \<acute> p) w"
  proof
    assume fp: "pp_t_holds (f \<acute> p) w"
    have at_w:
        "pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> p) w
          \<longleftrightarrow> pp_t_holds (f \<acute> p) w"
      using pp_t_prop_eqv_at[OF applications, of w] by simp
    show False using J_false fp at_w by blast
  qed
  have f_false_eqv:
      "pp_t_eqv Prop w
        (pp_zf_truth False) (f \<acute> p)"
  proof (unfold pp_t_eqv.simps, intro allI impI)
    fix v
    assume future: "prefix w v"
    have representative_v:
        "pp_t_eqv pp_t_constants_unary_type
          v pp_t_quantified_fun_prime_operator f"
      by (rule pp_t_eqv_persistent[OF representative future])
    have pb_v:
        "pp_t_eqv Prop v p (pp_zf_truth b)"
      by (rule pp_t_eqv_persistent[OF pb future])
    have J_false_v:
        "\<not> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> p) v"
      by (rule pp_t_quantified_fun_prime_false_on_settled[
        OF p pb_v])
    have pp_v: "pp_t_eqv Prop v p p"
      by (rule pp_t_eqv_reflexive[OF p])
    have applications_v:
        "pp_t_eqv Prop v
          (pp_t_quantified_fun_prime_operator \<acute> p)
          (f \<acute> p)"
      by (rule pp_t_app_respects[
        OF representative_v p p pp_v])
    have at_v:
        "pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> p) v
          \<longleftrightarrow> pp_t_holds (f \<acute> p) v"
      using pp_t_prop_eqv_at[OF applications_v, of v] by simp
    show "pp_t_holds (pp_zf_truth False) v =
        pp_t_holds (f \<acute> p) v"
      using J_false_v at_v by simp
  qed
  have old_result:
      "pp_t_quantified_fragment_pure Prop w (f \<acute> p)"
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using f_false_eqv by blast
  show ?thesis
    unfolding pp_t_fun_prime_pure_Prop_iff
    using old_result .
qed

lemma pp_t_fun_prime_unary_pure_persistent:
  assumes pure: "pp_t_fun_prime_unary_pure w X"
    and future: "prefix w v"
  shows "pp_t_fun_prime_unary_pure v X"
  using pure pp_t_eqv_persistent[OF _ future]
    pp_t_quantified_unary_pure_persistent[OF _ future]
  unfolding pp_t_fun_prime_unary_pure_def
  by blast

lemma pp_t_fun_prime_classifier_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_classifier_type)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_fun_prime_stock_classifier f"
    and pure_X: "pp_t_fun_prime_unary_pure w X"
  shows "pp_t_fun_prime_fragment_pure Prop w (f \<acute> X)"
proof -
  have classifier_true:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_stock_classifier \<acute> X)
        (pp_zf_truth True)"
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_fun_prime_stock_classifier_def
    using pp_t_classifier_holds[
        OF X, of pp_t_fun_prime_unary_pure]
      pp_t_fun_prime_unary_pure_persistent[
        OF pure_X]
    by blast
  have XX:
      "pp_t_eqv pp_t_constants_unary_type w X X"
    by (rule pp_t_eqv_reflexive[OF X])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_stock_classifier \<acute> X)
        (f \<acute> X)"
    by (rule pp_t_app_respects[
      OF representative X X XX])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth True) (f \<acute> X)"
    using pp_t_app_closed[
        OF pp_t_fun_prime_stock_classifier_in_domain X]
      pp_t_app_closed[OF f X]
      pp_t_truth_in_domain classifier_true applications
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have old_result:
      "pp_t_quantified_fragment_pure Prop w (f \<acute> X)"
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by blast
  show ?thesis
    unfolding pp_t_fun_prime_pure_Prop_iff
    using old_result .
qed

theorem pp_t_fun_prime_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_fun_prime_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_fun_prime_fragment_pure \<sigma> w x"
  shows "pp_t_fun_prime_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_quantified_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
        "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<noteq> pp_t_constants_classifier_type"
    | (added)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator f"
    | (classifier)
        "\<sigma> = pp_t_constants_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_fun_prime_stock_classifier f"
    unfolding pp_t_fun_prime_fragment_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_quantified_fragment_pure \<sigma> w x"
      by (rule pp_t_fun_prime_old_input[
        OF old pure_x])
    have old_result:
        "pp_t_quantified_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_quantified_fragment_application[
        OF f x old(1) old_x])
    have not_classifier:
        "\<tau> \<noteq> pp_t_constants_classifier_type"
    proof
      assume tau:
          "\<tau> = pp_t_constants_classifier_type"
      have no_old:
          "\<not> pp_t_quantified_fragment_pure
            (\<sigma> \<rightarrow>\<^sub>o
              pp_t_constants_classifier_type) w f"
        unfolding pp_t_quantified_fragment_pure_def
          pp_t_possibility_fragment_pure_def
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
      unfolding pp_t_fun_prime_fragment_pure_def
      using old_result not_classifier by blast
  next
    case added
    show ?thesis
      using pp_t_fun_prime_added_application[
        OF _ _ added(3)]
        f x pure_x added
      by simp
  next
    case classifier
    have pure_unary_fragment:
        "pp_t_fun_prime_fragment_pure
          pp_t_constants_unary_type w x"
      using pure_x classifier by simp
    have pure_unary:
        "pp_t_fun_prime_unary_pure w x"
      using pp_t_fun_prime_pure_unary_iff[
        of w x] pure_unary_fragment by blast
    show ?thesis
      using pp_t_fun_prime_classifier_application[
        OF _ _ classifier(3) pure_unary]
        f x classifier
      by simp
  qed
qed

section \<open>Recombination and Exhaustion for the added class\<close>

definition pp_t_now_only :: "bool list \<Rightarrow> ZF" where
  "pp_t_now_only w = pp_t_prop (\<lambda>v. v = w)"

lemma pp_t_now_only_in_domain:
  "Elem (pp_t_now_only w) (pp_t_domain Prop)"
  unfolding pp_t_now_only_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_identity_not_necessity:
  "\<not> pp_t_eqv pp_t_constants_unary_type w
    pp_t_identity_operator pp_t_necessity_operator"
proof
  assume operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_identity_operator pp_t_necessity_operator"
  let ?q = "pp_t_now_only w"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_now_only_in_domain)
  have applications:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> ?q)
        (pp_t_necessity_operator \<acute> ?q)"
    by (rule pp_t_app_respects[
      OF operators q q pp_t_eqv_reflexive[OF q]])
  have at_w:
      "pp_t_holds (pp_t_identity_operator \<acute> ?q) w
        \<longleftrightarrow>
       pp_t_holds (pp_t_necessity_operator \<acute> ?q) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  have identity_true:
      "pp_t_holds (pp_t_identity_operator \<acute> ?q) w"
    using q
    by (simp add: pp_t_identity_operator_def
        pp_t_now_only_def Lambda_app)
  have q_not_true:
      "\<not> pp_t_eqv Prop w ?q (pp_zf_truth True)"
  proof
    assume q_true: "pp_t_eqv Prop w ?q (pp_zf_truth True)"
    let ?v = "w @ [False]"
    have future: "prefix w ?v" by simp
    have at_v:
        "pp_t_holds ?q ?v
          \<longleftrightarrow> pp_t_holds (pp_zf_truth True) ?v"
      using pp_t_prop_eqv_at[OF q_true future] .
    show False
      using at_v
      by (simp add: pp_t_now_only_def)
  qed
  have necessity_false:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?q) w"
    using pp_t_necessity_operator_holds[OF q, of w]
      q_not_true by blast
  show False
    using at_w identity_true necessity_false by blast
qed

lemma pp_t_moving_seed_eqv_necessity:
  "pp_t_eqv Prop w
    (pp_t_identity_operator \<acute> pp_t_moving_seed w)
    (pp_t_necessity_operator \<acute> pp_t_moving_seed w)"
proof (unfold pp_t_eqv.simps, intro allI impI)
  fix v
  assume future: "prefix w v"
  have identity:
      "pp_t_holds
          (pp_t_identity_operator \<acute> pp_t_moving_seed w) v
        \<longleftrightarrow>
       pp_t_holds (pp_t_moving_seed w) v"
    using pp_t_moving_seed_in_domain
    by (simp add: pp_t_identity_operator_def Lambda_app)
  have box:
      "pp_t_holds
          (pp_t_necessity_operator \<acute> pp_t_moving_seed w) v
        \<longleftrightarrow>
       pp_t_eqv Prop v
          (pp_t_moving_seed w) (pp_zf_truth True)"
    by (rule pp_t_necessity_operator_holds[
      OF pp_t_moving_seed_in_domain])
  have settled_iff:
      "pp_t_eqv Prop v
          (pp_t_moving_seed w) (pp_zf_truth True)
        \<longleftrightarrow>
       pp_t_holds (pp_t_moving_seed w) v"
  proof
    assume settled:
        "pp_t_eqv Prop v
          (pp_t_moving_seed w) (pp_zf_truth True)"
    show "pp_t_holds (pp_t_moving_seed w) v"
      using pp_t_prop_eqv_at[OF settled, of v] by simp
  next
    assume at_v: "pp_t_holds (pp_t_moving_seed w) v"
    have left: "prefix (w @ [True]) v"
      using at_v by simp
    show "pp_t_eqv Prop v
        (pp_t_moving_seed w) (pp_zf_truth True)"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix u
      assume vu: "prefix v u"
      have left_u: "prefix (w @ [True]) u"
        using left vu prefix_order.trans by blast
      show "pp_t_holds (pp_t_moving_seed w) u =
          pp_t_holds (pp_zf_truth True) u"
        using left_u by simp
    qed
  qed
  show "pp_t_holds
      (pp_t_identity_operator \<acute> pp_t_moving_seed w) v =
    pp_t_holds
      (pp_t_necessity_operator \<acute> pp_t_moving_seed w) v"
    using identity box settled_iff by blast
qed

lemma pp_t_fun_prime_fails_on_fundamental:
  assumes r: "Elem r (pp_t_domain Prop)"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  shows "\<not> pp_t_fun_prime_predicate
    pp_t_quantified_unary_pure w r"
proof
  assume injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w r"
  have r_seed:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using fundamental by simp
  have identity_r_seed:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> r)
        (pp_t_identity_operator \<acute> pp_t_moving_seed w)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[OF pp_t_identity_operator_in_domain]
        r pp_t_moving_seed_in_domain r_seed])
  have necessity_r_seed:
      "pp_t_eqv Prop w
        (pp_t_necessity_operator \<acute> r)
        (pp_t_necessity_operator \<acute> pp_t_moving_seed w)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[OF pp_t_necessity_operator_in_domain]
        r pp_t_moving_seed_in_domain r_seed])
  have outputs:
      "pp_t_eqv Prop w
        (pp_t_identity_operator \<acute> r)
        (pp_t_necessity_operator \<acute> r)"
    using pp_t_app_closed[OF pp_t_identity_operator_in_domain r]
      pp_t_app_closed[
        OF pp_t_identity_operator_in_domain
          pp_t_moving_seed_in_domain]
      pp_t_app_closed[OF pp_t_necessity_operator_in_domain r]
      pp_t_app_closed[
        OF pp_t_necessity_operator_in_domain
          pp_t_moving_seed_in_domain]
      identity_r_seed necessity_r_seed
      pp_t_moving_seed_eqv_necessity[of w]
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have identity_pure:
      "pp_t_quantified_unary_pure w pp_t_identity_operator"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_identity_operator_in_domain]
    by blast
  have necessity_pure:
      "pp_t_quantified_unary_pure w pp_t_necessity_operator"
    unfolding pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_necessity_operator_in_domain]
    by blast
  have operators:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_identity_operator pp_t_necessity_operator"
    using injective pp_t_identity_operator_in_domain
      pp_t_necessity_operator_in_domain
      identity_pure necessity_pure outputs
    unfolding pp_t_fun_prime_predicate_def by blast
  show False
    using pp_t_identity_not_necessity[of w] operators by blast
qed

lemma pp_t_fun_prime_added_class_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator X"
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
  have J_r_false:
      "\<not> pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    using pp_t_quantified_fun_prime_operator_holds[OF r, of w]
      pp_t_fun_prime_fails_on_fundamental[OF r fundamental]
    by blast
  have rr: "pp_t_eqv Prop w r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have applications_r:
      "pp_t_eqv Prop w
        (pp_t_quantified_fun_prime_operator \<acute> r)
        (X \<acute> r)"
    by (rule pp_t_app_respects[
      OF representative r r rr])
  have X_r_false: "\<not> pp_t_holds (X \<acute> r) w"
    using J_r_false
      pp_t_prop_eqv_at[OF applications_r, of w]
    by blast
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)"
    using X_r_false by blast
  have truth: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have truth_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF truth])
  have J_truth_false:
      "\<not> pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> pp_zf_truth True) w"
    by (rule pp_t_quantified_fun_prime_false_on_settled[
      OF truth truth_refl])
  have applications_truth:
      "pp_t_eqv Prop w
        (pp_t_quantified_fun_prime_operator \<acute> pp_zf_truth True)
        (X \<acute> pp_zf_truth True)"
    by (rule pp_t_app_respects[
      OF representative truth truth truth_refl])
  have X_truth_false:
      "\<not> pp_t_holds (X \<acute> pp_zf_truth True) w"
    using J_truth_false
      pp_t_prop_eqv_at[OF applications_truth, of w]
    by blast
  have not_universal:
      "\<not> (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)"
    using truth X_truth_false by blast
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

lemma pp_t_fun_prime_pure_unary_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_fun_prime_fragment_pure
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
  have enlarged:
      "pp_t_fun_prime_unary_pure w X"
    using pp_t_fun_prime_pure_unary_iff[of w X] pure
    by blast
  have classes:
      "pp_t_quantified_unary_pure w X
        \<or> pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator X"
    using enlarged
    unfolding pp_t_fun_prime_unary_pure_def .
  from classes show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
  proof
    assume old: "pp_t_quantified_unary_pure w X"
    have old_pure:
        "pp_t_quantified_fragment_pure
          pp_t_constants_unary_type w X"
      using pp_t_quantified_pure_unary_iff[of w X] old
      by blast
    show ?thesis
      by (rule pp_t_quantified_pure_unary_QLN(1)[
        OF X r old_pure fundamental])
  next
    assume added:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator X"
    show ?thesis
      by (rule pp_t_fun_prime_added_class_QLN(1)[
        OF X r added fundamental])
  qed
  from classes show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
  proof
    assume old: "pp_t_quantified_unary_pure w X"
    have old_pure:
        "pp_t_quantified_fragment_pure
          pp_t_constants_unary_type w X"
      using pp_t_quantified_pure_unary_iff[of w X] old
      by blast
    show ?thesis
      by (rule pp_t_quantified_pure_unary_QLN(2)[
        OF X r old_pure fundamental])
  next
    assume added:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator X"
    show ?thesis
      by (rule pp_t_fun_prime_added_class_QLN(2)[
        OF X r added fundamental])
  qed
qed

lemma pp_t_fun_prime_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_fun_prime_fragment_pure
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

lemma pp_t_fun_prime_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_fun_prime_fragment_pure
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

theorem pp_t_fun_prime_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_fun_prime_unary_recombination_holds_iff
  using pp_t_fun_prime_pure_unary_QLN(1)
  by blast

theorem pp_t_fun_prime_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_fun_prime_unary_exhaustion_holds_iff
  using pp_t_fun_prime_pure_unary_QLN(2)
  by blast

theorem pp_t_fun_prime_unary_recombination_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    FunPrimeFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_fun_prime_unary_recombination_holds by blast

theorem pp_t_fun_prime_unary_exhaustion_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    FunPrimeFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_fun_prime_unary_exhaustion_holds by blast

lemma pp_t_fun_prime_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
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

theorem pp_t_fun_prime_modalized_functionality_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FunPrimeFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      FunPrimeFragment.MovingTreeConstants.pp_t_den_def
      pp_t_fun_prime_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

lemma pp_t_fun_prime_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_fun_prime_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_fun_prime_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_fun_prime_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_fun_prime_application_closure_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FunPrimeFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      FunPrimeFragment.MovingTreeConstants.pp_t_den_def
      pp_t_fun_prime_application_closure_holds_iff
    using pp_t_fun_prime_fragment_application by blast
qed

theorem pp_t_fun_prime_unique_fundamental_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    FunPrimeFragment.MovingTreeConstants.pp_t_den_def
  using FunPrimeFragment.pp_t_moving_unique_fundamental_holds
  by blast

lemma pp_t_fun_prime_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fun_prime_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_fun_prime_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_fun_prime_stock_classifier"
    unfolding pp_t_fun_prime_stock_classifier_def
      pp_t_classifier_def
    by (simp add: pp_t_fun_prime_pure_unary_iff)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_fun_prime_stock_classifier_in_domain,
      of "pp_t_fun_prime_fragment_pure
        pp_t_constants_classifier_type" w]
      pp_t_fun_prime_classifier_is_pure
    by (simp add: unary_classifier)
qed

theorem pp_t_fun_prime_target_PP_gvalid:
  "FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    FunPrimeFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    FunPrimeFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_fun_prime_target_PP_holds by blast

end
