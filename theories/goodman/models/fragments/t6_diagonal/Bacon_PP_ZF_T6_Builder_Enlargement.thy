theory Bacon_PP_ZF_T6_Builder_Enlargement
  imports Bacon_PP_ZF_Fresh_T6_Collisions
begin

section \<open>The next finite central-stock enlargement\<close>

text \<open>
  The T6 diagonal itself is not a logical term: it contains the name
  \<open>Pure\<close>.  The logical item supplied by the Purity schema is instead the
  constant-free builder obtained by abstracting that name.  PP makes the
  unary-stock classifier pure, and application closure therefore requires
  the value of this builder at that classifier to be pure.

  This theory isolates that exact new obligation over the already verified
  T6-diagonal fragment.  It does not assume that the old one-step stock is a
  fixed point.
\<close>

abbreviation pp_t_T6_builder_type :: otype where
  "pp_t_T6_builder_type \<equiv>
    pp_t_constants_classifier_type
      \<rightarrow>\<^sub>o pp_t_constants_unary_type"

definition pp_t_T6_purity_builder_den :: ZF where
  "pp_t_T6_purity_builder_den =
    pp_t_eval pp_t_T6_diagonal_fragment_constants
      pp_t_closed_env pp_T6_purity_builder"

lemma pp_t_T6_purity_builder_den_in_domain:
  "Elem pp_t_T6_purity_builder_den
    (pp_t_domain pp_t_T6_builder_type)"
  unfolding pp_t_T6_purity_builder_den_def
  using
    T6DiagonalFragment.MovingTreeConstants.pp_t_eval_type[
      OF typed_pp_T6_purity_builder pp_t_empty_env_typed]
  by (simp add: pp_t_dom_def pp_unary_ty_def)

lemma pp_t_T6_purity_builder_applied_to_classifier:
  "pp_t_T6_purity_builder_den
      \<acute> pp_t_T6_diagonal_stock_classifier
    = pp_t_T6_diagonal_T6_operator"
proof -
  have classifier:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env (pp_Pure pp_unary_ty)
        = pp_t_T6_diagonal_stock_classifier"
    unfolding pp_Pure_def pp_unary_ty_def
      pp_t_T6_diagonal_stock_classifier_def
    by (simp add: pp_t_classifier_def
        pp_t_T6_diagonal_pure_unary_iff)
  have beta:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_purity_builder
        \<acute> pp_t_T6_diagonal_stock_classifier
      =
      pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_purity_instance"
    using classifier by simp
  have raw_classifier_in_domain:
      "Elem
        (pp_t_classifier pp_unary_ty
          (pp_t_T6_diagonal_fragment_pure pp_unary_ty))
        (pp_t_domain (pp_unary_ty \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain)
      (rule pp_t_T6_diagonal_fragment_pure_admissible)
  have classifier_raw:
      "pp_t_T6_diagonal_fragment_constants
          pp_pure_name (pp_unary_ty \<rightarrow>\<^sub>o Prop)
        =
       pp_t_classifier pp_unary_ty
          (pp_t_T6_diagonal_fragment_pure pp_unary_ty)"
    using classifier
    unfolding pp_Pure_def pp_t_T6_diagonal_stock_classifier_def
    by (simp add: pp_t_classifier_def
        pp_t_T6_diagonal_pure_unary_iff)
  have application_beta:
      "Lambda
          (pp_t_domain (pp_unary_ty \<rightarrow>\<^sub>o Prop))
          (\<lambda>x.
            pp_t_eval pp_t_T6_diagonal_fragment_constants
              (extend_env x pp_t_closed_env)
              pp_T6_abstract_body)
        \<acute>
        (pp_t_classifier pp_unary_ty
          (pp_t_T6_diagonal_fragment_pure pp_unary_ty))
      =
      pp_t_eval pp_t_T6_diagonal_fragment_constants
        (extend_env
          (pp_t_classifier pp_unary_ty
            (pp_t_T6_diagonal_fragment_pure pp_unary_ty))
          pp_t_closed_env)
        pp_T6_abstract_body"
    by (rule Lambda_app[OF raw_classifier_in_domain])
  have instance_application:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_purity_instance
      =
      pp_t_eval pp_t_T6_diagonal_fragment_constants
        (extend_env
          (pp_t_classifier pp_unary_ty
            (pp_t_T6_diagonal_fragment_pure pp_unary_ty))
          pp_t_closed_env)
        pp_T6_abstract_body"
    unfolding pp_T6_purity_builder_def pp_Pure_def
    using application_beta classifier_raw
    by (simp only: pp_t_eval.simps)
  have substitution:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_liar
      =
      pp_t_eval pp_t_T6_diagonal_fragment_constants
        (extend_env
          (pp_t_classifier pp_unary_ty
            (pp_t_T6_diagonal_fragment_pure pp_unary_ty))
          pp_t_closed_env)
        pp_T6_abstract_body"
  proof -
    have eval_substitution:
        "pp_t_eval pp_t_T6_diagonal_fragment_constants
            pp_t_closed_env
            (subst0 (pp_Pure pp_unary_ty)
              pp_T6_abstract_body)
        =
        pp_t_eval pp_t_T6_diagonal_fragment_constants
          (extend_env
            (pp_t_eval pp_t_T6_diagonal_fragment_constants
              pp_t_closed_env (pp_Pure pp_unary_ty))
            pp_t_closed_env)
          pp_T6_abstract_body"
      by (rule pp_t_eval_subst0)
    show ?thesis
      using eval_substitution classifier
      unfolding pp_T6_builder_substitution
      by simp
  qed
  have instance_eval:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_purity_instance
      =
      pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_liar"
    using instance_application substitution by simp
  show ?thesis
    unfolding pp_t_T6_purity_builder_den_def
      pp_t_T6_diagonal_T6_operator_def
    using beta instance_eval by simp
qed

definition pp_t_T6_builder_application_closed :: bool where
  "pp_t_T6_builder_application_closed \<longleftrightarrow>
    (\<forall>w f C.
      Elem f (pp_t_domain pp_t_T6_builder_type)
      \<longrightarrow>
      Elem C (pp_t_domain pp_t_constants_classifier_type)
      \<longrightarrow>
      pp_t_eqv pp_t_T6_builder_type
        w pp_t_T6_purity_builder_den f
      \<longrightarrow>
      pp_t_T6_diagonal_fragment_pure
        pp_t_constants_classifier_type w C
      \<longrightarrow>
      pp_t_T6_diagonal_fragment_pure
        pp_t_constants_unary_type w (f \<acute> C))"

definition pp_t_T6_recomputed_diagonal_absorbed :: bool where
  "pp_t_T6_recomputed_diagonal_absorbed \<longleftrightarrow>
    (\<forall>w.
      pp_t_T6_diagonal_fragment_pure
        pp_t_constants_unary_type w
        pp_t_T6_diagonal_T6_operator)"

lemma pp_t_T6_builder_application_closed_if_absorbed:
  assumes absorbed: "pp_t_T6_recomputed_diagonal_absorbed"
  shows "pp_t_T6_builder_application_closed"
  unfolding pp_t_T6_builder_application_closed_def
proof (intro allI impI)
  fix w f C
  assume f:
      "Elem f (pp_t_domain pp_t_T6_builder_type)"
    and C:
      "Elem C (pp_t_domain pp_t_constants_classifier_type)"
    and representative:
      "pp_t_eqv pp_t_T6_builder_type
        w pp_t_T6_purity_builder_den f"
    and pure_C:
      "pp_t_T6_diagonal_fragment_pure
        pp_t_constants_classifier_type w C"
  have classifier_rep:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_T6_diagonal_stock_classifier C"
    using pure_C
    unfolding pp_t_T6_diagonal_pure_classifier_iff .
  have applications:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_T6_diagonal_stock_classifier)
        (f \<acute> C)"
    by (rule pp_t_app_respects[
      OF representative
        pp_t_T6_diagonal_stock_classifier_in_domain C
        classifier_rep])
  have recomputed:
      "pp_t_T6_diagonal_fragment_pure
        pp_t_constants_unary_type w
        pp_t_T6_diagonal_T6_operator"
    using absorbed
    unfolding pp_t_T6_recomputed_diagonal_absorbed_def
    by blast
  have result:
      "pp_t_eqv pp_t_constants_unary_type w
        pp_t_T6_diagonal_T6_operator (f \<acute> C)"
    using applications
    unfolding pp_t_T6_purity_builder_applied_to_classifier .
  show "pp_t_T6_diagonal_fragment_pure
      pp_t_constants_unary_type w (f \<acute> C)"
    using pp_t_T6_diagonal_fragment_pure_admissible
      pp_t_T6_diagonal_T6_operator_in_domain
      pp_t_app_closed[OF f C] result recomputed
    unfolding pp_t_predicate_admissible_def
    by (metis prefix_order.refl)
qed

lemma pp_t_T6_recomputed_diagonal_absorbed_if_builder_closed:
  assumes closed: "pp_t_T6_builder_application_closed"
  shows "pp_t_T6_recomputed_diagonal_absorbed"
  unfolding pp_t_T6_recomputed_diagonal_absorbed_def
proof
  fix w
  have builder_refl:
      "pp_t_eqv pp_t_T6_builder_type w
        pp_t_T6_purity_builder_den
        pp_t_T6_purity_builder_den"
    by (rule pp_t_eqv_reflexive[
      OF pp_t_T6_purity_builder_den_in_domain])
  have application:
      "pp_t_T6_diagonal_fragment_pure
        pp_t_constants_unary_type w
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_T6_diagonal_stock_classifier)"
    using closed
      pp_t_T6_purity_builder_den_in_domain
      pp_t_T6_diagonal_stock_classifier_in_domain
      builder_refl
      pp_t_T6_diagonal_classifier_is_pure
    unfolding pp_t_T6_builder_application_closed_def
    by blast
  show "pp_t_T6_diagonal_fragment_pure
      pp_t_constants_unary_type w
      pp_t_T6_diagonal_T6_operator"
    using application
    unfolding pp_t_T6_purity_builder_applied_to_classifier .
qed

theorem pp_t_T6_builder_application_closed_iff:
  "pp_t_T6_builder_application_closed
    \<longleftrightarrow>
   pp_t_T6_recomputed_diagonal_absorbed"
  using pp_t_T6_builder_application_closed_if_absorbed
    pp_t_T6_recomputed_diagonal_absorbed_if_builder_closed
  by blast

lemma pp_t_T6_diagonal_unary_pure_classes:
  "pp_t_T6_diagonal_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
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
      w pp_t_possible_falsity_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_quantified_fun_prime_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_fun_prime_T6_operator X"
  unfolding pp_t_T6_diagonal_pure_unary_iff
    pp_t_T6_diagonal_unary_pure_def
    pp_t_fun_prime_unary_pure_def
    pp_t_quantified_unary_pure_classes
  by blast

theorem pp_t_T6_recomputed_diagonal_absorbed_iff_ten_classes:
  "pp_t_T6_recomputed_diagonal_absorbed
    \<longleftrightarrow>
    (\<forall>w.
      pp_t_eqv pp_t_constants_unary_type
        w pp_t_identity_operator pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_negation_operator pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator True)
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator False)
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessity_operator pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_possibility_operator pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_possible_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator
          pp_t_T6_diagonal_T6_operator)"
  unfolding pp_t_T6_recomputed_diagonal_absorbed_def
    pp_t_T6_diagonal_unary_pure_classes
  by blast

section \<open>The recomputed diagonal on settled propositions\<close>

lemma pp_t_T6_diagonal_constant_operator_is_pure:
  "pp_t_T6_diagonal_unary_pure w (pp_t_constant_operator b)"
  unfolding pp_t_T6_diagonal_unary_pure_def
  using pp_t_fun_prime_constant_operator_is_pure
  by blast

lemma pp_t_T6_diagonal_representation_at_J:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and pure_X: "pp_t_T6_diagonal_unary_pure w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_eqv pp_t_constants_unary_type
    w X (pp_t_constant_operator b)"
proof -
  have J_predicate:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w q"
    using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
      OF q, of w] Jq
    by blast
  have Kq:
      "pp_t_constant_operator b \<acute> q = pp_zf_truth b"
    by (rule pp_t_constant_operator_apply[OF q])
  have Xq:
      "Elem (X \<acute> q) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF X q])
  have agreement:
      "pp_t_eqv Prop w
        (X \<acute> q) (pp_t_constant_operator b \<acute> q)"
    unfolding Kq
    using Xq p pp_t_truth_in_domain p_as_Xq p_as_b
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  show ?thesis
    using J_predicate X pp_t_constant_operator_in_domain
      pure_X pp_t_T6_diagonal_constant_operator_is_pure
      agreement
    unfolding pp_t_fun_prime_predicate_def
    by blast
qed

lemma pp_t_T6_diagonal_representation_value:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and pure_X: "pp_t_T6_diagonal_unary_pure w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_holds (X \<acute> p) w = b"
proof -
  have operators:
      "pp_t_eqv pp_t_constants_unary_type
        w X (pp_t_constant_operator b)"
    by (rule pp_t_T6_diagonal_representation_at_J[
      OF p q X Jq pure_X p_as_Xq p_as_b])
  have applications:
      "pp_t_eqv Prop w
        (X \<acute> p) (pp_t_constant_operator b \<acute> p)"
    by (rule pp_t_app_respects[
      OF operators p p pp_t_eqv_reflexive[OF p]])
  have at_w:
      "pp_t_holds (X \<acute> p) w =
       pp_t_holds (pp_t_constant_operator b \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  show ?thesis
    using at_w pp_t_constant_operator_holds[OF p, of b w]
    by simp
qed

lemma pp_t_T6_recomputed_diagonal_false_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and false_p:
      "pp_t_eqv Prop w p (pp_zf_truth False)"
  shows "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute> p) w"
proof -
  show ?thesis
    unfolding pp_t_eval_T6_diagonal_T6_operator_holds[OF p]
  proof (intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_T6_diagonal_unary_pure w X
          \<and> pp_t_holds
            (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
          \<and> pp_t_eqv Prop w p (X \<acute> q)"
    show "\<not> pp_t_holds (X \<acute> p) w"
      using pp_t_T6_diagonal_representation_value[
        OF p q X _ _ _ false_p]
        antecedent
      by simp
  qed
qed

lemma pp_t_T6_recomputed_diagonal_true_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and true_p:
      "pp_t_eqv Prop w p (pp_zf_truth True)"
    and witness:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
  shows "\<not> pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute> p) w"
proof
  assume Dp:
      "pp_t_holds (pp_t_T6_diagonal_T6_operator \<acute> p) w"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    using witness by blast
  let ?K = "pp_t_constant_operator True"
  have Kq: "?K \<acute> q = pp_zf_truth True"
    by (rule pp_t_constant_operator_apply[OF q])
  have antecedent:
      "pp_t_T6_diagonal_unary_pure w ?K
        \<and> pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
        \<and> pp_t_eqv Prop w p (?K \<acute> q)"
    using pp_t_T6_diagonal_constant_operator_is_pure
      Jq true_p
    unfolding Kq by blast
  have not_Kp: "\<not> pp_t_holds (?K \<acute> p) w"
    using pp_t_eval_T6_diagonal_T6_operator_holds[
        OF p, of w]
      Dp pp_t_constant_operator_in_domain q antecedent
    by blast
  show False
    using not_Kp
      pp_t_constant_operator_holds[OF p, of True w]
    by simp
qed

definition pp_t_T6_diagonal_has_witness_everywhere :: bool where
  "pp_t_T6_diagonal_has_witness_everywhere \<longleftrightarrow>
    (\<forall>w.
      \<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w)"

theorem pp_t_T6_recomputed_diagonal_on_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
    and witnesses: "pp_t_T6_diagonal_has_witness_everywhere"
  shows "pp_t_eqv Prop w
    (pp_t_T6_diagonal_T6_operator \<acute> p)
    (pp_zf_truth (\<not> b))"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume future: "prefix w v"
  have settled_v:
      "pp_t_eqv Prop v p (pp_zf_truth b)"
    by (rule pp_t_eqv_persistent[OF settled future])
  have witness_v:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) v"
    using witnesses
    unfolding pp_t_T6_diagonal_has_witness_everywhere_def
    by blast
  show "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> p) v
    =
    pp_t_holds (pp_zf_truth (\<not> b)) v"
  proof (cases b)
    case False
    have Dp:
        "pp_t_holds
          (pp_t_T6_diagonal_T6_operator \<acute> p) v"
      by (rule pp_t_T6_recomputed_diagonal_false_input[
        OF p])
        (use settled_v False in simp)
    show ?thesis using Dp False by simp
  next
    case True
    have not_Dp:
        "\<not> pp_t_holds
          (pp_t_T6_diagonal_T6_operator \<acute> p) v"
      by (rule pp_t_T6_recomputed_diagonal_true_input[
        OF p _ witness_v])
        (use settled_v True in simp)
    show ?thesis using not_Dp True by simp
  qed
qed

section \<open>A generic separator for the ten-class stock\<close>

definition pp_t_T6_ten_representatives :: "ZF set" where
  "pp_t_T6_ten_representatives = {
    pp_t_identity_operator,
    pp_t_negation_operator,
    pp_t_constant_operator True,
    pp_t_constant_operator False,
    pp_t_necessity_operator,
    pp_t_possibility_operator,
    pp_t_necessary_falsity_operator,
    pp_t_possible_falsity_operator,
    pp_t_quantified_fun_prime_operator,
    pp_t_fun_prime_T6_operator}"

lemma pp_t_T6_ten_representatives_finite:
  "finite pp_t_T6_ten_representatives"
  unfolding pp_t_T6_ten_representatives_def by simp

lemma pp_t_T6_ten_representative_in_domain:
  assumes "A \<in> pp_t_T6_ten_representatives"
  shows "Elem A (pp_t_domain pp_t_constants_unary_type)"
  using assms
  unfolding pp_t_T6_ten_representatives_def
  using pp_t_identity_operator_in_domain
    pp_t_negation_operator_in_domain
    pp_t_constant_operator_in_domain
    pp_t_necessity_operator_in_domain
    pp_t_possibility_operator_in_domain
    pp_t_necessary_falsity_operator_in_domain
    pp_t_possible_falsity_operator_in_domain
    pp_t_quantified_fun_prime_operator_in_domain
    pp_t_fun_prime_T6_operator_in_domain
  by blast

lemma pp_t_T6_ten_representative:
  assumes pure: "pp_t_T6_diagonal_unary_pure w X"
  shows "\<exists>A \<in> pp_t_T6_ten_representatives.
    pp_t_eqv pp_t_constants_unary_type w A X"
  using pure
  unfolding pp_t_T6_diagonal_unary_pure_def
    pp_t_fun_prime_unary_pure_def
    pp_t_quantified_unary_pure_classes
    pp_t_T6_ten_representatives_def
  by blast

lemma pp_b_operator_of_injective_on_unary_domain:
  assumes A:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    and B:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    and operators:
      "pp_b_operator_of A = pp_b_operator_of B"
  shows "A = B"
proof -
  have root_eqv:
      "pp_t_eqv pp_t_constants_unary_type [] A B"
  proof (rule pp_t_arrow_eqv_if_pointwise[OF A B])
    show "\<forall>v. prefix [] v \<longrightarrow>
        (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
          pp_t_eqv Prop v (A \<acute> p) (B \<acute> p))"
    proof (intro allI impI)
      fix v :: "bool list"
        and p
      assume "prefix [] v"
        and p: "Elem p (pp_t_domain Prop)"
      have at_p:
          "pp_b_operator_of A (pp_b_of_zf p) =
           pp_b_operator_of B (pp_b_of_zf p)"
        using operators by simp
      have output_sets:
          "pp_b_of_zf (A \<acute> p) =
           pp_b_of_zf (B \<acute> p)"
        using at_p pp_zf_of_b_of_zf[OF p]
        unfolding pp_b_operator_of_def by simp
      have output_values:
          "\<forall>z.
            pp_t_holds (A \<acute> p) z =
            pp_t_holds (B \<acute> p) z"
        using output_sets
        unfolding pp_b_of_zf_def
        by auto
      show "pp_t_eqv Prop v (A \<acute> p) (B \<acute> p)"
        using output_values
        unfolding pp_t_eqv.simps
        by blast
    qed
  qed
  show ?thesis
    using pp_t_root_eqv_iff_eq[OF A B] root_eqv
    by blast
qed

lemma pp_t_closed_logical_unary_den_equivariant:
  assumes typed: "[] \<turnstile> M : pp_t_constants_unary_type"
    and logical: "pp_logical_vocabulary M"
  shows "pp_b_equivariant
    (pp_b_operator_of (pp_t_closed_den M))"
proof -
  have membership:
      "pp_t_closed_den M
        \<in> pp_t_exact_closed_logical_operators"
    using typed logical
    unfolding pp_t_exact_closed_logical_operators_def
    by blast
  show ?thesis
    by (rule UnconditionalCone.pp_t_exact_closed_operator_equivariant[
      OF membership])
qed

lemma pp_t_identity_operator_equivariant:
  "pp_b_equivariant (pp_b_operator_of pp_t_identity_operator)"
proof -
  have logical: "pp_logical_vocabulary prop_id"
    by (simp add: pp_logical_vocabulary_def prop_id_def)
  have den:
      "pp_t_closed_den prop_id = pp_t_identity_operator"
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF typed_prop_id logical]
    unfolding den .
qed

lemma pp_t_negation_operator_equivariant:
  "pp_b_equivariant (pp_b_operator_of pp_t_negation_operator)"
proof -
  have logical:
      "pp_logical_vocabulary pp_negation_operator"
    by (simp add: pp_logical_vocabulary_def
        pp_negation_operator_def)
  have den:
      "pp_t_closed_den pp_negation_operator =
        pp_t_negation_operator"
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF typed_pp_negation_operator[
          where \<Gamma>="[]", unfolded pp_unary_ty_def]
        logical]
    unfolding den .
qed

lemma pp_t_constant_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of (pp_t_constant_operator b))"
proof (cases b)
  case False
  let ?M = "pp_constant_operator ObjFalse"
  have typed: "[] \<turnstile> ?M : pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjFalse]
    by (simp add: pp_unary_ty_def)
  have logical: "pp_logical_vocabulary ?M"
    by (simp add: pp_logical_vocabulary_def
        pp_constant_operator_def pp_constant_builder_def
        ObjFalse_def ObjTrue_def)
  have den:
      "pp_t_closed_den ?M = pp_t_constant_operator False"
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    apply (subst False)
    using pp_t_closed_logical_unary_den_equivariant[
      OF typed logical]
    unfolding den .
next
  case True
  let ?M = "pp_constant_operator ObjTrue"
  have typed: "[] \<turnstile> ?M : pp_t_constants_unary_type"
    using typed_pp_constant_operator[OF typed_ObjTrue]
    by (simp add: pp_unary_ty_def)
  have logical: "pp_logical_vocabulary ?M"
    by (simp add: pp_logical_vocabulary_def
        pp_constant_operator_def pp_constant_builder_def
        ObjTrue_def)
  have den:
      "pp_t_closed_den ?M = pp_t_constant_operator True"
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    apply (subst True)
    using pp_t_closed_logical_unary_den_equivariant[
      OF typed logical]
    unfolding den .
qed

lemma pp_t_necessity_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_necessity_operator)"
proof -
  have den:
      "pp_t_closed_den pp_zf_eq_truth_operator =
        pp_t_necessity_operator"
    unfolding pp_t_closed_den_def
    by (rule pp_t_eval_eq_truth_logical_operator)
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF pp_zf_eq_truth_operator_typed
        pp_zf_eq_truth_operator_logical]
    unfolding den pp_unary_ty_def .
qed

lemma pp_t_possibility_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_possibility_operator)"
proof -
  have den:
      "pp_t_closed_den pp_possibility_operator =
        pp_t_possibility_operator"
    unfolding pp_t_closed_den_def
    by (rule pp_t_eval_possibility_operator)
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF pp_possibility_operator_typed[
          unfolded pp_unary_ty_def]
        pp_possibility_operator_logical]
    unfolding den pp_unary_ty_def .
qed

lemma pp_t_necessary_falsity_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_necessary_falsity_operator)"
proof -
  have den_domain:
      "Elem (pp_t_closed_den pp_t_HO_leibniz_false_term)
        (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(2)]
    by simp
  have root_eqv:
      "pp_t_eqv pp_t_constants_unary_type []
        (pp_t_closed_den pp_t_HO_leibniz_false_term)
        pp_t_necessary_falsity_operator"
    by (rule pp_t_HO_leibniz_false_eqv_necessary_falsity)
  have den:
      "pp_t_closed_den pp_t_HO_leibniz_false_term =
        pp_t_necessary_falsity_operator"
    using pp_t_root_eqv_iff_eq[
      OF den_domain pp_t_necessary_falsity_operator_in_domain]
      root_eqv
    by blast
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF pp_t_HO_leibniz_terms_typed(2)
        pp_t_HO_leibniz_terms_logical(2)]
    unfolding den .
qed

lemma pp_t_possible_falsity_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_possible_falsity_operator)"
proof -
  have den_domain:
      "Elem
        (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
        (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF pp_t_HO_leibniz_terms_typed(3)]
    by simp
  have root_eqv:
      "pp_t_eqv pp_t_constants_unary_type []
        (pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
        pp_t_possible_falsity_operator"
    by (rule pp_t_HO_not_leibniz_truth_eqv_possible_falsity)
  have den:
      "pp_t_closed_den pp_t_HO_not_leibniz_truth_term =
        pp_t_possible_falsity_operator"
    using pp_t_root_eqv_iff_eq[
      OF den_domain pp_t_possible_falsity_operator_in_domain]
      root_eqv
    by blast
  show ?thesis
    using pp_t_closed_logical_unary_den_equivariant[
      OF pp_t_HO_leibniz_terms_typed(3)
        pp_t_HO_leibniz_terms_logical(3)]
    unfolding den .
qed

definition pp_t_T6_ten_representatives_equivariant :: bool where
  "pp_t_T6_ten_representatives_equivariant \<longleftrightarrow>
    (\<forall>A \<in> pp_t_T6_ten_representatives.
      pp_b_equivariant (pp_b_operator_of A))"

theorem pp_t_T6_ten_representatives_equivariant_iff_last_two:
  "pp_t_T6_ten_representatives_equivariant
    \<longleftrightarrow>
    pp_b_equivariant
      (pp_b_operator_of pp_t_quantified_fun_prime_operator)
    \<and>
    pp_b_equivariant
      (pp_b_operator_of pp_t_fun_prime_T6_operator)"
  unfolding pp_t_T6_ten_representatives_equivariant_def
    pp_t_T6_ten_representatives_def
  using pp_t_identity_operator_equivariant
    pp_t_negation_operator_equivariant
    pp_t_constant_operator_equivariant[of True]
    pp_t_constant_operator_equivariant[of False]
    pp_t_necessity_operator_equivariant
    pp_t_possibility_operator_equivariant
    pp_t_necessary_falsity_operator_equivariant
    pp_t_possible_falsity_operator_equivariant
  by blast

subsection \<open>Equivariance of the old fun-prime denotation\<close>

lemma pp_t_fun_prime_probe_representative_equivariant:
  assumes "A \<in> pp_t_fun_prime_probe_representatives"
  shows "pp_b_equivariant (pp_b_operator_of A)"
  using assms
  unfolding pp_t_fun_prime_probe_representatives_def
  using pp_t_identity_operator_equivariant
    pp_t_negation_operator_equivariant
    pp_t_constant_operator_equivariant[of True]
    pp_t_constant_operator_equivariant[of False]
    pp_t_necessity_operator_equivariant
    pp_t_possibility_operator_equivariant
    pp_t_necessary_falsity_operator_equivariant
    pp_t_possible_falsity_operator_equivariant
  by blast

definition pp_b_T6_base_fun_prime :: pp_b_operator where
  "pp_b_T6_base_fun_prime P = {
    w. \<forall>A \<in> pp_t_fun_prime_probe_representatives.
       \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        pp_b_view w (pp_b_operator_of A P) =
        pp_b_view w (pp_b_operator_of B P)
        \<longrightarrow> A = B}"

lemma pp_b_T6_base_fun_prime_membership:
  "w \<in> pp_b_T6_base_fun_prime P
  \<longleftrightarrow>
  (\<forall>A \<in> pp_t_fun_prime_probe_representatives.
   \<forall>B \<in> pp_t_fun_prime_probe_representatives.
    pp_b_view w (pp_b_operator_of A P) =
      pp_b_view w (pp_b_operator_of B P)
    \<longrightarrow> A = B)"
  unfolding pp_b_T6_base_fun_prime_def
  by simp

lemma pp_t_fun_prime_probe_representative_view_shift:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
  shows "pp_b_view (s @ u) (pp_b_operator_of A P) =
      pp_b_view u
        (pp_b_operator_of A (pp_b_view s P))"
proof -
  have first:
      "pp_b_view s (pp_b_operator_of A P) =
       pp_b_operator_of A (pp_b_view s P)"
    using pp_t_fun_prime_probe_representative_equivariant[
      OF A]
    unfolding pp_b_equivariant_def by blast
  show ?thesis
    using first
    unfolding pp_b_view_compose[symmetric]
    by simp
qed

lemma pp_t_fun_prime_probe_representative_view_shift_raw:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
  shows "{v. s @ u @ v \<in> pp_b_operator_of A P} =
      {v. u @ v \<in>
        pp_b_operator_of A {v. s @ v \<in> P}}"
  using pp_t_fun_prime_probe_representative_view_shift[
    OF A, of s u P]
  unfolding pp_b_view_def
  by (simp add: append_assoc)

lemma pp_b_T6_base_fun_prime_equivariant:
  "pp_b_equivariant pp_b_T6_base_fun_prime"
  unfolding pp_b_equivariant_def
  unfolding pp_b_view_def pp_b_T6_base_fun_prime_def
  by (intro allI set_eqI;
      simp add:
        pp_t_fun_prime_probe_representative_view_shift_raw)

lemma pp_t_eqv_Prop_iff_boolean_views:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_eqv Prop w p q
    \<longleftrightarrow>
    pp_b_view w (pp_b_of_zf p) =
      pp_b_view w (pp_b_of_zf q)"
  unfolding pp_t_eqv.simps pp_b_view_def pp_b_of_zf_def
  by (auto simp: prefix_def append_eq_append_conv2)

lemma pp_t_base_representatives_operator_eqv_implies_equal:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and operators:
      "pp_t_eqv pp_t_constants_unary_type w A B"
  shows "A = B"
proof -
  let ?p = "pp_t_fun_prime_probe w"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_fun_prime_probe_in_domain)
  have outputs:
      "pp_t_eqv Prop w (A \<acute> ?p) (B \<acute> ?p)"
    by (rule pp_t_app_respects[
      OF operators p p pp_t_eqv_reflexive[OF p]])
  show ?thesis
    by (rule pp_t_fun_prime_probe_representatives_separated[
      OF A B outputs])
qed

lemma pp_t_fun_prime_probe_representative_is_pure:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
  shows "pp_t_quantified_unary_pure w A"
proof -
  from A consider
      (identity) "A = pp_t_identity_operator"
    | (negation) "A = pp_t_negation_operator"
    | (truth) "A = pp_t_constant_operator True"
    | (falsity) "A = pp_t_constant_operator False"
    | (necessity) "A = pp_t_necessity_operator"
    | (possibility) "A = pp_t_possibility_operator"
    | (necessary_falsity)
        "A = pp_t_necessary_falsity_operator"
    | (possible_falsity)
        "A = pp_t_possible_falsity_operator"
    unfolding pp_t_fun_prime_probe_representatives_def
    by auto
  then show ?thesis
  proof cases
    case identity
    show ?thesis
      unfolding identity pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_identity_operator_in_domain]
      by blast
  next
    case negation
    show ?thesis
      unfolding negation pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_negation_operator_in_domain]
      by blast
  next
    case truth
    show ?thesis
      unfolding truth pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain]
      by blast
  next
    case falsity
    show ?thesis
      unfolding falsity pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_constant_operator_in_domain]
      by blast
  next
    case necessity
    show ?thesis
      unfolding necessity pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_necessity_operator_in_domain]
      by blast
  next
    case possibility
    show ?thesis
      unfolding possibility pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_possibility_operator_in_domain]
      by blast
  next
    case necessary_falsity
    show ?thesis
      unfolding necessary_falsity
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_necessary_falsity_operator_in_domain]
      by blast
  next
    case possible_falsity
    show ?thesis
      unfolding possible_falsity
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_possible_falsity_operator_in_domain]
      by blast
  qed
qed

lemma pp_t_quantified_fun_prime_separates_base_representatives:
  assumes injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w (pp_zf_of_b P)"
    and A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and views:
      "pp_b_view w (pp_b_operator_of A P) =
       pp_b_view w (pp_b_operator_of B P)"
  shows "A = B"
proof -
  have p:
      "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF A])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF B])
  have pure_A: "pp_t_quantified_unary_pure w A"
    by (rule pp_t_fun_prime_probe_representative_is_pure[OF A])
  have pure_B: "pp_t_quantified_unary_pure w B"
    by (rule pp_t_fun_prime_probe_representative_is_pure[OF B])
  have outputs:
      "pp_t_eqv Prop w
        (A \<acute> pp_zf_of_b P) (B \<acute> pp_zf_of_b P)"
  proof -
    have boolean_outputs:
        "pp_b_view w (pp_b_of_zf (A \<acute> pp_zf_of_b P)) =
         pp_b_view w (pp_b_of_zf (B \<acute> pp_zf_of_b P))"
      using views
      unfolding pp_b_operator_of_def
      by simp
    show ?thesis
      using pp_t_eqv_Prop_iff_boolean_views[
        OF pp_t_app_closed[OF A_domain p]
          pp_t_app_closed[OF B_domain p]]
        boolean_outputs
      by blast
  qed
  have operator_eqv:
      "pp_t_eqv pp_t_constants_unary_type w A B"
    using injective A_domain B_domain pure_A pure_B outputs
    unfolding pp_t_fun_prime_predicate_def
    by blast
  show "A = B"
    by (rule
      pp_t_base_representatives_operator_eqv_implies_equal[
        OF A B operator_eqv])
qed

lemma pp_t_base_representative_separation_implies_fun_prime:
  assumes separated:
      "\<forall>A \<in> pp_t_fun_prime_probe_representatives.
       \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        pp_b_view w (pp_b_operator_of A P) =
          pp_b_view w (pp_b_operator_of B P)
        \<longrightarrow> A = B"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and pure:
      "pp_t_quantified_unary_pure w X
        \<and> pp_t_quantified_unary_pure w Y"
    and agreement:
      "pp_t_eqv Prop w
        (X \<acute> pp_zf_of_b P) (Y \<acute> pp_zf_of_b P)"
  shows "pp_t_eqv pp_t_constants_unary_type w X Y"
proof -
  have p:
      "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  obtain A where A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct1]] by blast
  obtain B where B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and BY:
      "pp_t_eqv pp_t_constants_unary_type w B Y"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct2]] by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF A])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF B])
  have A_X:
      "pp_t_eqv Prop w
        (A \<acute> pp_zf_of_b P) (X \<acute> pp_zf_of_b P)"
    by (rule pp_t_app_respects[
      OF AX p p pp_t_eqv_reflexive[OF p]])
  have B_Y:
      "pp_t_eqv Prop w
        (B \<acute> pp_zf_of_b P) (Y \<acute> pp_zf_of_b P)"
    by (rule pp_t_app_respects[
      OF BY p p pp_t_eqv_reflexive[OF p]])
  have AB_outputs:
      "pp_t_eqv Prop w
        (A \<acute> pp_zf_of_b P) (B \<acute> pp_zf_of_b P)"
    using pp_t_app_closed[OF A_domain p]
      pp_t_app_closed[OF X p]
      pp_t_app_closed[OF Y p]
      pp_t_app_closed[OF B_domain p]
      A_X agreement B_Y
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have views:
      "pp_b_view w (pp_b_operator_of A P) =
       pp_b_view w (pp_b_operator_of B P)"
    unfolding pp_b_operator_of_def
    using pp_t_eqv_Prop_iff_boolean_views[
      OF pp_t_app_closed[OF A_domain p]
        pp_t_app_closed[OF B_domain p]]
      AB_outputs
    by simp
  have AB: "A = B"
    using separated A B views by blast
  have XB:
      "pp_t_eqv pp_t_constants_unary_type w X B"
    by (rule pp_t_eqv_symmetric[
      OF A_domain X AX, unfolded AB])
  show ?thesis
    using pp_t_eqv_transitive[
      OF X B_domain Y XB BY] .
qed

lemma pp_t_quantified_fun_prime_base_separation:
  assumes injective:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w (pp_zf_of_b P)"
  shows "\<forall>A \<in> pp_t_fun_prime_probe_representatives.
    \<forall>B \<in> pp_t_fun_prime_probe_representatives.
      pp_b_view w (pp_b_operator_of A P) =
        pp_b_view w (pp_b_operator_of B P)
      \<longrightarrow> A = B"
  using pp_t_quantified_fun_prime_separates_base_representatives[
    OF injective]
  by blast

lemma pp_t_base_separation_is_quantified_fun_prime:
  assumes separated:
      "\<forall>A \<in> pp_t_fun_prime_probe_representatives.
       \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        pp_b_view w (pp_b_operator_of A P) =
          pp_b_view w (pp_b_operator_of B P)
        \<longrightarrow> A = B"
  shows "pp_t_fun_prime_predicate
    pp_t_quantified_unary_pure w (pp_zf_of_b P)"
  unfolding pp_t_fun_prime_predicate_def
  using pp_t_base_representative_separation_implies_fun_prime[
    OF separated]
  by blast

theorem pp_b_operator_of_quantified_fun_prime:
  "pp_b_operator_of pp_t_quantified_fun_prime_operator =
    pp_b_T6_base_fun_prime"
proof (rule ext)
  fix P
  show "pp_b_operator_of pp_t_quantified_fun_prime_operator P =
      pp_b_T6_base_fun_prime P"
  proof (rule set_eqI)
    fix w
    have p:
        "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have semantic:
        "w \<in>
          pp_b_operator_of pp_t_quantified_fun_prime_operator P
        \<longleftrightarrow>
        pp_t_fun_prime_predicate
          pp_t_quantified_unary_pure w (pp_zf_of_b P)"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
      using pp_t_quantified_fun_prime_operator_holds[
        OF p, of w]
      by simp
    show "w \<in>
        pp_b_operator_of pp_t_quantified_fun_prime_operator P
      \<longleftrightarrow>
      w \<in> pp_b_T6_base_fun_prime P"
      using semantic pp_b_T6_base_fun_prime_membership
        pp_t_quantified_fun_prime_base_separation
        pp_t_base_separation_is_quantified_fun_prime
      by blast
  qed
qed

theorem pp_t_quantified_fun_prime_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_quantified_fun_prime_operator)"
  unfolding pp_b_operator_of_quantified_fun_prime
  by (rule pp_b_T6_base_fun_prime_equivariant)

subsection \<open>Cone naturality of the old fun-prime stock\<close>

lemma pp_t_unary_operator_equivariant_implies_cone_related:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and equivariant:
      "pp_b_equivariant (pp_b_operator_of X)"
  shows "pp_t_cone_rel pp_t_constants_unary_type s X X"
  unfolding pp_t_cone_rel.simps(3)
proof (intro allI impI)
  fix p q
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_cone_rel Prop s p q"
  have input_views:
      "pp_b_view s (pp_b_of_zf p) = pp_b_of_zf q"
    using pq
    unfolding pp_t_cone_rel.simps pp_b_view_def pp_b_of_zf_def
    by auto
  have equivariant_at:
      "pp_b_view s
          (pp_b_operator_of X (pp_b_of_zf p))
       =
       pp_b_operator_of X
          (pp_b_view s (pp_b_of_zf p))"
    using equivariant
    unfolding pp_b_equivariant_def by blast
  have output_views:
      "pp_b_view s (pp_b_of_zf (X \<acute> p)) =
       pp_b_of_zf (X \<acute> q)"
  proof -
    have left:
        "pp_b_operator_of X (pp_b_of_zf p) =
         pp_b_of_zf (X \<acute> p)"
      unfolding pp_b_operator_of_def
      using pp_zf_of_b_of_zf[OF p]
      by simp
    have right:
        "pp_b_operator_of X (pp_b_of_zf q) =
         pp_b_of_zf (X \<acute> q)"
      unfolding pp_b_operator_of_def
      using pp_zf_of_b_of_zf[OF q]
      by simp
    show ?thesis
      using equivariant_at input_views
      unfolding left[symmetric] right[symmetric]
      by simp
  qed
  have reconstructed:
      "pp_zf_of_b
        (pp_b_view s (pp_b_of_zf (X \<acute> p))) =
       X \<acute> q"
  proof -
    have right_output:
        "Elem (X \<acute> q) (pp_t_domain Prop)"
      by (rule pp_t_app_closed[OF X q])
    show ?thesis
      using output_views pp_zf_of_b_of_zf[OF right_output]
      by simp
  qed
  have view_rel:
      "pp_t_cone_rel Prop s (X \<acute> p)
        (pp_zf_of_b
          (pp_b_view s (pp_b_of_zf (X \<acute> p))))"
    by (rule pp_t_cone_rel_prop_view)
  show "pp_t_cone_rel Prop s (X \<acute> p) (X \<acute> q)"
    using view_rel reconstructed by simp
qed

definition pp_t_fun_prime_nine_representatives :: "ZF set" where
  "pp_t_fun_prime_nine_representatives =
    insert pp_t_quantified_fun_prime_operator
      pp_t_fun_prime_probe_representatives"

lemma pp_t_fun_prime_nine_representative_in_domain:
  assumes A:
      "A \<in> pp_t_fun_prime_nine_representatives"
  shows "Elem A (pp_t_domain pp_t_constants_unary_type)"
  using A pp_t_quantified_fun_prime_operator_in_domain
    pp_t_fun_prime_probe_representative_in_domain
  unfolding pp_t_fun_prime_nine_representatives_def
  by blast

lemma pp_t_fun_prime_nine_representative_equivariant:
  assumes A:
      "A \<in> pp_t_fun_prime_nine_representatives"
  shows "pp_b_equivariant (pp_b_operator_of A)"
  using A pp_t_quantified_fun_prime_operator_equivariant
    pp_t_fun_prime_probe_representative_equivariant
  unfolding pp_t_fun_prime_nine_representatives_def
  by blast

lemma pp_t_fun_prime_nine_representative_cone_related:
  assumes A:
      "A \<in> pp_t_fun_prime_nine_representatives"
  shows "pp_t_cone_rel pp_t_constants_unary_type s A A"
  by (rule pp_t_unary_operator_equivariant_implies_cone_related[
    OF pp_t_fun_prime_nine_representative_in_domain[OF A]
      pp_t_fun_prime_nine_representative_equivariant[OF A]])

lemma pp_t_fun_prime_unary_pure_represented:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
  shows "pp_t_fun_prime_unary_pure w X
  \<longleftrightarrow>
  (\<exists>A \<in> pp_t_fun_prime_nine_representatives.
    pp_t_eqv pp_t_constants_unary_type w A X)"
proof
  assume pure: "pp_t_fun_prime_unary_pure w X"
  show "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
      pp_t_eqv pp_t_constants_unary_type w A X"
  proof (cases
      "pp_t_quantified_unary_pure w X")
    case True
    obtain A where A:
        "A \<in> pp_t_fun_prime_probe_representatives"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type w A X"
      using pp_t_fun_prime_probe_representative[OF True]
      by blast
    show ?thesis
      using A AX
      unfolding pp_t_fun_prime_nine_representatives_def
      by blast
  next
    case False
    have JX:
        "pp_t_eqv pp_t_constants_unary_type w
          pp_t_quantified_fun_prime_operator X"
      using pure False
      unfolding pp_t_fun_prime_unary_pure_def
      by blast
    show ?thesis
      using JX
      unfolding pp_t_fun_prime_nine_representatives_def
      by blast
  qed
next
  assume represented:
      "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
        pp_t_eqv pp_t_constants_unary_type w A X"
  then obtain A where A:
      "A \<in> pp_t_fun_prime_nine_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    by blast
  show "pp_t_fun_prime_unary_pure w X"
  proof (cases "A = pp_t_quantified_fun_prime_operator")
    case True
    show ?thesis
      using AX
      unfolding True pp_t_fun_prime_unary_pure_def
      by blast
  next
    case False
    have A_base:
        "A \<in> pp_t_fun_prime_probe_representatives"
      using A False
      unfolding pp_t_fun_prime_nine_representatives_def
      by blast
    have pure_A:
        "pp_t_quantified_unary_pure w A"
      by (rule pp_t_fun_prime_probe_representative_is_pure[
        OF A_base])
    have pure_X:
        "pp_t_quantified_unary_pure w X"
      using pp_t_quantified_unary_pure_admissible
        pp_t_fun_prime_probe_representative_in_domain[OF A_base]
        X AX pure_A
      unfolding pp_t_predicate_admissible_def
      by blast
    show ?thesis
      using pure_X
      unfolding pp_t_fun_prime_unary_pure_def
      by blast
  qed
qed

lemma pp_t_fun_prime_unary_pure_cone_iff:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows "pp_t_fun_prime_unary_pure (s @ u) X
    \<longleftrightarrow> pp_t_fun_prime_unary_pure u Y"
  unfolding pp_t_fun_prime_unary_pure_represented[OF X]
    pp_t_fun_prime_unary_pure_represented[OF Y]
proof
  assume left:
      "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
        pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
  then obtain A where A:
      "A \<in> pp_t_fun_prime_nine_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_nine_representative_in_domain[OF A])
  have AY:
      "pp_t_eqv pp_t_constants_unary_type u A Y"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF A_domain A_domain X Y
        pp_t_fun_prime_nine_representative_cone_related[OF A] XY,
      of u]
      AX by blast
  show "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
      pp_t_eqv pp_t_constants_unary_type u A Y"
    using A AY by blast
next
  assume right:
      "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
        pp_t_eqv pp_t_constants_unary_type u A Y"
  then obtain A where A:
      "A \<in> pp_t_fun_prime_nine_representatives"
    and AY:
      "pp_t_eqv pp_t_constants_unary_type u A Y"
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_nine_representative_in_domain[OF A])
  have AX:
      "pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    using UnconditionalCone.pp_t_cone_rel_eqv_iff[
      OF A_domain A_domain X Y
        pp_t_fun_prime_nine_representative_cone_related[OF A] XY,
      of u]
      AY by blast
  show "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
      pp_t_eqv pp_t_constants_unary_type (s @ u) A X"
    using A AX by blast
qed

lemma pp_t_fun_prime_stock_classifier_pointwise_cone:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows "pp_t_holds
      (pp_t_fun_prime_stock_classifier \<acute> X) (s @ u)
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_fun_prime_stock_classifier \<acute> Y) u"
proof -
  have left:
      "pp_t_holds
        (pp_t_fun_prime_stock_classifier \<acute> X) (s @ u)
      \<longleftrightarrow>
      pp_t_fun_prime_unary_pure (s @ u) X"
    unfolding pp_t_fun_prime_stock_classifier_def
    by (rule pp_t_classifier_holds[OF X])
  have right:
      "pp_t_holds
        (pp_t_fun_prime_stock_classifier \<acute> Y) u
      \<longleftrightarrow>
      pp_t_fun_prime_unary_pure u Y"
    unfolding pp_t_fun_prime_stock_classifier_def
    by (rule pp_t_classifier_holds[OF Y])
  show ?thesis
    using left right
      pp_t_fun_prime_unary_pure_cone_iff[
        OF X Y XY, of u]
    by blast
qed

lemma pp_t_fun_prime_stock_classifier_outputs_cone:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_constants_unary_type s X Y"
  shows "pp_t_cone_rel Prop s
    (pp_t_fun_prime_stock_classifier \<acute> X)
    (pp_t_fun_prime_stock_classifier \<acute> Y)"
  unfolding pp_t_cone_rel.simps(2)
  using pp_t_fun_prime_stock_classifier_pointwise_cone[
    OF X Y XY]
  by blast

lemma pp_t_fun_prime_stock_classifier_cone_related:
  "pp_t_cone_rel pp_t_constants_classifier_type s
    pp_t_fun_prime_stock_classifier
    pp_t_fun_prime_stock_classifier"
  apply (subst pp_t_cone_rel.simps(3))
  using pp_t_fun_prime_stock_classifier_outputs_cone
  by blast

lemma pp_t_T6_purity_builder_den_is_closed_den:
  "pp_t_T6_purity_builder_den =
    pp_t_closed_den pp_T6_purity_builder"
  unfolding pp_t_T6_purity_builder_den_def
    pp_t_closed_den_def
  using pp_t_eval_const_free[
    OF pp_T6_purity_builder_constant_free,
    where C=pp_t_T6_diagonal_fragment_constants
      and D=pp_t_default_constants
      and \<rho>=pp_t_closed_env]
  by simp

lemma pp_t_T6_purity_builder_den_cone_related:
  "pp_t_cone_rel pp_t_T6_builder_type s
    pp_t_T6_purity_builder_den
    pp_t_T6_purity_builder_den"
proof -
  have logical:
      "pp_logical_vocabulary pp_T6_purity_builder"
    unfolding pp_logical_vocabulary_def
    by (rule pp_T6_purity_builder_constant_free)
  have cone:
      "pp_t_cone_rel
        ((pp_unary_ty \<rightarrow>\<^sub>o Prop)
          \<rightarrow>\<^sub>o pp_unary_ty) s
        (pp_t_closed_den pp_T6_purity_builder)
        (pp_t_closed_den pp_T6_purity_builder)"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF typed_pp_T6_purity_builder[
          where \<Gamma>="[]"] logical])
  show ?thesis
    using cone
    unfolding pp_t_T6_purity_builder_den_is_closed_den
    by (simp add: pp_unary_ty_def)
qed

lemma pp_t_fun_prime_classifier_eval:
  "pp_t_eval pp_t_fun_prime_fragment_constants
      pp_t_closed_env (pp_Pure pp_unary_ty)
    = pp_t_fun_prime_stock_classifier"
  unfolding pp_Pure_def pp_unary_ty_def
    pp_t_fun_prime_stock_classifier_def
  by (simp add: pp_t_classifier_def
      pp_t_fun_prime_pure_unary_iff)

lemma pp_t_T6_purity_builder_den_at_fun_prime_classifier:
  "pp_t_T6_purity_builder_den
      \<acute> pp_t_fun_prime_stock_classifier
    = pp_t_fun_prime_T6_operator"
proof -
  have builder_change_constants:
      "pp_t_T6_purity_builder_den =
       pp_t_eval pp_t_fun_prime_fragment_constants
         pp_t_closed_env pp_T6_purity_builder"
    unfolding pp_t_T6_purity_builder_den_def
    using pp_t_eval_const_free[
      OF pp_T6_purity_builder_constant_free,
      where C=pp_t_T6_diagonal_fragment_constants
        and D=pp_t_fun_prime_fragment_constants
        and \<rho>=pp_t_closed_env]
    by simp
  have beta:
      "pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_T6_purity_builder
        \<acute> pp_t_fun_prime_stock_classifier
      =
       pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_T6_purity_instance"
    using pp_t_fun_prime_classifier_eval
    by simp
  have instance_liar:
      "pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_T6_purity_instance
       =
       pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_T6_liar"
    by (rule
      FunPrimeFragment.MovingTreeConstants.pp_t_beta_contract_eval_preserving[
        unfolded
          FunPrimeFragment.MovingTreeConstants.pp_t_eval_preserving_step_def,
        rule_format,
        OF pp_T6_purity_instance_beta
          typed_pp_T6_purity_instance typed_pp_T6_liar
          pp_t_empty_env_typed])
  show ?thesis
    unfolding builder_change_constants
      pp_t_fun_prime_T6_operator_def
    using beta instance_liar by simp
qed

lemma pp_t_fun_prime_T6_operator_cone_related:
  "pp_t_cone_rel pp_t_constants_unary_type s
    pp_t_fun_prime_T6_operator
    pp_t_fun_prime_T6_operator"
proof -
  have builder:
      "pp_t_cone_rel pp_t_T6_builder_type s
        pp_t_T6_purity_builder_den
        pp_t_T6_purity_builder_den"
    by (rule pp_t_T6_purity_builder_den_cone_related)
  have classifier:
      "pp_t_cone_rel pp_t_constants_classifier_type s
        pp_t_fun_prime_stock_classifier
        pp_t_fun_prime_stock_classifier"
    by (rule pp_t_fun_prime_stock_classifier_cone_related)
  have classifier_domain:
      "Elem pp_t_fun_prime_stock_classifier
        (pp_t_domain pp_t_constants_classifier_type)"
    by (rule pp_t_fun_prime_stock_classifier_in_domain)
  have applied:
      "pp_t_cone_rel pp_t_constants_unary_type s
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_fun_prime_stock_classifier)
        (pp_t_T6_purity_builder_den
          \<acute> pp_t_fun_prime_stock_classifier)"
    using builder classifier_domain classifier_domain classifier
    by simp
  show ?thesis
    using applied
    unfolding pp_t_T6_purity_builder_den_at_fun_prime_classifier .
qed

theorem pp_t_fun_prime_T6_operator_equivariant:
  "pp_b_equivariant
    (pp_b_operator_of pp_t_fun_prime_T6_operator)"
  by (rule pp_t_cone_rel_operator_implies_equivariant)
    (rule pp_t_fun_prime_T6_operator_cone_related)

theorem pp_t_T6_ten_representatives_equivariant:
  "pp_t_T6_ten_representatives_equivariant"
  using pp_t_T6_ten_representatives_equivariant_iff_last_two
    pp_t_quantified_fun_prime_operator_equivariant
    pp_t_fun_prime_T6_operator_equivariant
  by blast

lemma pp_t_T6_ten_generic_boolean_separator:
  assumes equivariant:
      "pp_t_T6_ten_representatives_equivariant"
  shows "\<exists>R.
    \<forall>A \<in> pp_t_T6_ten_representatives.
    \<forall>B \<in> pp_t_T6_ten_representatives.
      (pp_b_operator_of A R = pp_b_operator_of B R
        \<longleftrightarrow> A = B)"
proof -
  let ?Stock =
    "pp_b_operator_of ` pp_t_T6_ten_representatives"
  have countable: "countable ?Stock"
    unfolding pp_t_T6_ten_representatives_def
    by simp
  have stock_equivariant:
      "\<And>F. F \<in> ?Stock \<Longrightarrow> pp_b_equivariant F"
    using equivariant
    unfolding pp_t_T6_ten_representatives_equivariant_def
    by blast
  obtain R where separator:
      "\<forall>F \<in> ?Stock. \<forall>G \<in> ?Stock.
        (F R = G R \<longleftrightarrow> F = G)"
    using pp_b_generic_separator_for_countable_stock[
      OF countable stock_equivariant]
    by blast
  show ?thesis
  proof (intro exI[of _ R] ballI allI impI iffI)
    fix A B
    assume A_rep: "A \<in> pp_t_T6_ten_representatives"
      and B_rep: "B \<in> pp_t_T6_ten_representatives"
      and outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
    have operators:
        "pp_b_operator_of A = pp_b_operator_of B"
      using separator A_rep B_rep outputs by blast
    show "A = B"
      by (rule pp_b_operator_of_injective_on_unary_domain[
        OF pp_t_T6_ten_representative_in_domain[OF A_rep]
          pp_t_T6_ten_representative_in_domain[OF B_rep]
          operators])
  next
    fix A B
    assume "A \<in> pp_t_T6_ten_representatives"
      and "B \<in> pp_t_T6_ten_representatives"
      and "A = B"
    then show
        "pp_b_operator_of A R = pp_b_operator_of B R"
      by simp
  qed
qed

lemma pp_t_T6_ten_separator_at_world:
  assumes equivariant:
      "pp_t_T6_ten_representatives_equivariant"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and>
    (\<forall>A \<in> pp_t_T6_ten_representatives.
      \<forall>B \<in> pp_t_T6_ten_representatives.
        pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)
        \<longrightarrow> A = B)"
proof -
  obtain R where separator:
      "\<forall>A \<in> pp_t_T6_ten_representatives.
       \<forall>B \<in> pp_t_T6_ten_representatives.
        (pp_b_operator_of A R = pp_b_operator_of B R
          \<longleftrightarrow> A = B)"
    using pp_t_T6_ten_generic_boolean_separator[
      OF equivariant] by blast
  let ?q = "pp_zf_of_b (pp_b_lift w R)"
  show ?thesis
  proof (intro exI[of _ ?q] conjI ballI allI impI)
    show "Elem ?q (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
  next
    fix A B
    assume A_rep: "A \<in> pp_t_T6_ten_representatives"
      and B_rep: "B \<in> pp_t_T6_ten_representatives"
      and agreement:
        "pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)"
    have view_outputs:
        "pp_b_view w
            (pp_b_operator_of A (pp_b_lift w R))
        =
         pp_b_view w
            (pp_b_operator_of B (pp_b_lift w R))"
      using agreement
      unfolding pp_t_eqv.simps pp_b_view_def
        pp_b_operator_of_def pp_b_of_zf_def
      by auto
    have A_equivariant:
        "pp_b_equivariant (pp_b_operator_of A)"
      using equivariant A_rep
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have B_equivariant:
        "pp_b_equivariant (pp_b_operator_of B)"
      using equivariant B_rep
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
      using view_outputs A_equivariant B_equivariant
      unfolding pp_b_equivariant_def
      by simp
    show "A = B"
      using separator A_rep B_rep outputs by blast
  qed
qed

lemma pp_t_T6_ten_separator_at_world_with_value:
  assumes equivariant:
      "pp_t_T6_ten_representatives_equivariant"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds q w = b
    \<and>
    (\<forall>A \<in> pp_t_T6_ten_representatives.
      \<forall>B \<in> pp_t_T6_ten_representatives.
        pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)
        \<longrightarrow> A = B)"
proof -
  let ?Stock =
    "pp_b_operator_of ` pp_t_T6_ten_representatives"
  have countable: "countable ?Stock"
    unfolding pp_t_T6_ten_representatives_def
    by simp
  have stock_equivariant:
      "\<And>F. F \<in> ?Stock \<Longrightarrow> pp_b_equivariant F"
    using equivariant
    unfolding pp_t_T6_ten_representatives_equivariant_def
    by blast
  obtain R where root: "[] \<in> R \<longleftrightarrow> b"
    and separator:
      "\<forall>F \<in> ?Stock. \<forall>G \<in> ?Stock.
        (F R = G R \<longleftrightarrow> F = G)"
    using pp_b_generic_separator_for_countable_stock_with_root[
      OF countable stock_equivariant, where b=b]
    by blast
  let ?q = "pp_zf_of_b (pp_b_lift w R)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have lift_root:
      "w \<in> pp_b_lift w R \<longleftrightarrow> [] \<in> R"
    using pp_b_view_membership_root[
      of w "pp_b_lift w R"]
    by simp
  have q_value: "pp_t_holds ?q w = b"
    using root lift_root
    by simp
  have separated:
      "A \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       B \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)
       \<Longrightarrow> A = B"
    for A B
  proof -
    assume A_rep: "A \<in> pp_t_T6_ten_representatives"
      and B_rep: "B \<in> pp_t_T6_ten_representatives"
      and agreement:
        "pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)"
    have view_outputs:
        "pp_b_view w
            (pp_b_operator_of A (pp_b_lift w R))
        =
         pp_b_view w
            (pp_b_operator_of B (pp_b_lift w R))"
      using agreement
      unfolding pp_t_eqv.simps pp_b_view_def
        pp_b_operator_of_def pp_b_of_zf_def
      by auto
    have A_equivariant:
        "pp_b_equivariant (pp_b_operator_of A)"
      using equivariant A_rep
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have B_equivariant:
        "pp_b_equivariant (pp_b_operator_of B)"
      using equivariant B_rep
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
      using view_outputs A_equivariant B_equivariant
      unfolding pp_b_equivariant_def
      by simp
    have operators:
        "pp_b_operator_of A = pp_b_operator_of B"
      using separator A_rep B_rep outputs by blast
    show "A = B"
      by (rule pp_b_operator_of_injective_on_unary_domain[
        OF pp_t_T6_ten_representative_in_domain[OF A_rep]
          pp_t_T6_ten_representative_in_domain[OF B_rep]
          operators])
  qed
  show ?thesis
    using q q_value separated by blast
qed

lemma pp_t_T6_ten_separated_implies_fun_prime:
  assumes q: "Elem q (pp_t_domain Prop)"
    and separated:
      "\<And>A B.
        A \<in> pp_t_T6_ten_representatives \<Longrightarrow>
        B \<in> pp_t_T6_ten_representatives \<Longrightarrow>
        pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)
        \<Longrightarrow> A = B"
  shows "pp_t_fun_prime_predicate
    pp_t_T6_diagonal_unary_pure w q"
proof (unfold pp_t_fun_prime_predicate_def, intro allI impI)
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and pure:
      "pp_t_T6_diagonal_unary_pure w X
        \<and> pp_t_T6_diagonal_unary_pure w Y"
    and agreement:
      "pp_t_eqv Prop w (X \<acute> q) (Y \<acute> q)"
  obtain A where A_rep:
      "A \<in> pp_t_T6_ten_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    using pp_t_T6_ten_representative[
      OF pure[THEN conjunct1]] by blast
  obtain B where B_rep:
      "B \<in> pp_t_T6_ten_representatives"
    and BY:
      "pp_t_eqv pp_t_constants_unary_type w B Y"
    using pp_t_T6_ten_representative[
      OF pure[THEN conjunct2]] by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_ten_representative_in_domain[
      OF A_rep])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_T6_ten_representative_in_domain[
      OF B_rep])
  have A_X:
      "pp_t_eqv Prop w (A \<acute> q) (X \<acute> q)"
    by (rule pp_t_app_respects[
      OF AX q q pp_t_eqv_reflexive[OF q]])
  have B_Y:
      "pp_t_eqv Prop w (B \<acute> q) (Y \<acute> q)"
    by (rule pp_t_app_respects[
      OF BY q q pp_t_eqv_reflexive[OF q]])
  have AB_outputs:
      "pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)"
    using pp_t_app_closed[OF A_domain q]
      pp_t_app_closed[OF X q]
      pp_t_app_closed[OF Y q]
      pp_t_app_closed[OF B_domain q]
      A_X agreement B_Y
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have AB: "A = B"
    by (rule separated[OF A_rep B_rep AB_outputs])
  have XB:
      "pp_t_eqv pp_t_constants_unary_type w X B"
    by (rule pp_t_eqv_symmetric[
      OF A_domain X AX, unfolded AB])
  show "pp_t_eqv pp_t_constants_unary_type w X Y"
    using pp_t_eqv_transitive[
      OF X B_domain Y XB BY] .
qed

theorem pp_t_T6_diagonal_witnesses_from_equivariance:
  assumes equivariant:
      "pp_t_T6_ten_representatives_equivariant"
  shows "pp_t_T6_diagonal_has_witness_everywhere"
  unfolding pp_t_T6_diagonal_has_witness_everywhere_def
proof
  fix w
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and separated:
      "\<forall>A \<in> pp_t_T6_ten_representatives.
       \<forall>B \<in> pp_t_T6_ten_representatives.
        pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)
        \<longrightarrow> A = B"
    using pp_t_T6_ten_separator_at_world[
      OF equivariant, of w] by blast
  have predicate:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w q"
    by (rule pp_t_T6_ten_separated_implies_fun_prime[
      OF q])
      (use separated in blast)
  show "\<exists>q.
      Elem q (pp_t_domain Prop)
      \<and> pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    using q predicate
      pp_t_eval_T6_diagonal_fun_prime_operator_holds[
        OF q, of w]
    by blast
qed

corollary pp_t_T6_diagonal_has_witness_everywhere:
  "pp_t_T6_diagonal_has_witness_everywhere"
  by (rule pp_t_T6_diagonal_witnesses_from_equivariance)
    (rule pp_t_T6_ten_representatives_equivariant)

lemma pp_t_T6_diagonal_has_true_witness:
  "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds q w"
proof -
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and q_true: "pp_t_holds q w"
    and separated:
      "\<forall>A \<in> pp_t_T6_ten_representatives.
       \<forall>B \<in> pp_t_T6_ten_representatives.
        pp_t_eqv Prop w (A \<acute> q) (B \<acute> q)
        \<longrightarrow> A = B"
    using pp_t_T6_ten_separator_at_world_with_value[
      OF pp_t_T6_ten_representatives_equivariant,
      of w True]
    by auto
  have predicate:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w q"
    by (rule pp_t_T6_ten_separated_implies_fun_prime[
      OF q])
      (use separated in blast)
  have Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
      OF q, of w]
      predicate by blast
  show ?thesis using q Jq q_true by blast
qed

corollary pp_t_T6_recomputed_diagonal_on_settled_unconditional:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_eqv Prop w
    (pp_t_T6_diagonal_T6_operator \<acute> p)
    (pp_zf_truth (\<not> b))"
  by (rule pp_t_T6_recomputed_diagonal_on_settled[
    OF p settled pp_t_T6_diagonal_has_witness_everywhere])

lemma pp_t_T6_absorption_candidate_settled_value:
  assumes A:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    and candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w A pp_t_T6_diagonal_T6_operator"
    and p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_holds (A \<acute> p) w = (\<not> b)"
proof -
  have applications:
      "pp_t_eqv Prop w
        (A \<acute> p) (pp_t_T6_diagonal_T6_operator \<acute> p)"
    by (rule pp_t_app_respects[
      OF candidate p p pp_t_eqv_reflexive[OF p]])
  have A_D:
      "pp_t_holds (A \<acute> p) w =
       pp_t_holds (pp_t_T6_diagonal_T6_operator \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  have D:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute> p) w =
       (\<not> b)"
    using pp_t_prop_eqv_at[
      OF pp_t_T6_recomputed_diagonal_on_settled_unconditional[
        OF p settled],
      of w]
    by simp
  show ?thesis using A_D D by simp
qed

lemma pp_t_T6_recomputed_diagonal_not_identity:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_identity_operator pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_identity_operator pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth False"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF p])
  have identity_value:
      "pp_t_holds (pp_t_identity_operator \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_identity_operator_in_domain candidate p settled]
    by simp
  have identity_p: "pp_t_identity_operator \<acute> ?p = ?p"
    using p
    by (simp add: pp_t_identity_operator_def Lambda_app)
  show False
    using identity_value unfolding identity_p by simp
qed

lemma pp_t_T6_recomputed_diagonal_not_constant_truth:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w (pp_t_constant_operator True)
      pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator True)
          pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth True"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF p])
  have constant_truth_value:
      "\<not> pp_t_holds (pp_t_constant_operator True \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_constant_operator_in_domain candidate p settled]
    by simp
  show False
    using constant_truth_value
      pp_t_constant_operator_holds[OF p, of True w]
    by simp
qed

lemma pp_t_T6_recomputed_diagonal_not_constant_falsity:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w (pp_t_constant_operator False)
      pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w (pp_t_constant_operator False)
          pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth False"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF p])
  have constant_falsity_value:
      "pp_t_holds (pp_t_constant_operator False \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_constant_operator_in_domain candidate p settled]
    by simp
  show False
    using constant_falsity_value
      pp_t_constant_operator_holds[OF p, of False w]
    by simp
qed

lemma pp_t_T6_recomputed_diagonal_not_necessity:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_necessity_operator pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessity_operator pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth False"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF p])
  have necessity_value:
      "pp_t_holds (pp_t_necessity_operator \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_necessity_operator_in_domain candidate p settled]
    by simp
  have not_necessity:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) w"
    using pp_t_settled_operator_values(1)[OF p settled]
    by simp
  show False using necessity_value not_necessity by blast
qed

lemma pp_t_T6_recomputed_diagonal_not_possibility:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_possibility_operator pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possibility_operator pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth True"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF p])
  have not_possibility:
      "\<not> pp_t_holds (pp_t_possibility_operator \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_possibility_operator_in_domain candidate p settled]
    by simp
  have possibility_value:
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) w"
    using pp_t_settled_operator_values(2)[OF p settled]
    by simp
  show False using not_possibility possibility_value by blast
qed

lemma pp_t_T6_recomputed_diagonal_not_old_fun_prime:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_quantified_fun_prime_operator
      pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_quantified_fun_prime_operator
          pp_t_T6_diagonal_T6_operator"
  let ?p = "pp_zf_truth False"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled: "pp_t_eqv Prop w ?p (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF p])
  have old_fun_prime_value:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> ?p) w"
    using pp_t_T6_absorption_candidate_settled_value[
      OF pp_t_quantified_fun_prime_operator_in_domain
        candidate p settled]
    by simp
  have not_old_fun_prime:
      "\<not> pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> ?p) w"
    by (rule pp_t_quantified_fun_prime_false_on_settled[
      OF p settled])
  show False using old_fun_prime_value not_old_fun_prime by blast
qed

lemma pp_t_T6_recomputed_diagonal_false_on_negated_true_witness:
  assumes q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
  shows "\<not> pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      (pp_t_negation_operator \<acute> q)) w"
proof
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have pure_negation:
      "pp_t_T6_diagonal_unary_pure w pp_t_negation_operator"
    unfolding pp_t_T6_diagonal_unary_pure_def
      pp_t_fun_prime_unary_pure_def
      pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_negation_operator_in_domain, of w]
    by blast
  have representation:
      "pp_t_eqv Prop w ?p
        (pp_t_negation_operator \<acute> q)"
    by (rule pp_t_eqv_reflexive[OF p])
  assume Dp:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
  have semantic:
      "\<forall>X.
        Elem X (pp_t_domain pp_t_constants_unary_type)
        \<longrightarrow>
        (\<forall>r.
          Elem r (pp_t_domain Prop)
          \<longrightarrow>
          (pp_t_T6_diagonal_unary_pure w X
            \<and> pp_t_holds
              (pp_t_T6_diagonal_fun_prime_operator \<acute> r) w
            \<and> pp_t_eqv Prop w ?p (X \<acute> r))
          \<longrightarrow> \<not> pp_t_holds (X \<acute> ?p) w)"
    using pp_t_eval_T6_diagonal_T6_operator_holds[
      OF p, of w]
      Dp by blast
  have not_double_negation:
      "\<not> pp_t_holds
        (pp_t_negation_operator \<acute> ?p) w"
    using semantic pp_t_negation_operator_in_domain q
      pure_negation Jq representation
    by blast
  have double_negation:
      "pp_t_holds
        (pp_t_negation_operator \<acute> ?p) w"
    using pp_t_negation_operator_holds[OF p, of w]
      pp_t_negation_operator_holds[OF q, of w]
      q_true
    by simp
  show False using not_double_negation double_negation by blast
qed

lemma pp_t_T6_recomputed_diagonal_not_negation:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_negation_operator pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_negation_operator pp_t_T6_diagonal_T6_operator"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
    using pp_t_T6_diagonal_has_true_witness[of w]
    by blast
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have pure_negation:
      "pp_t_T6_diagonal_unary_pure w pp_t_negation_operator"
    unfolding pp_t_T6_diagonal_unary_pure_def
      pp_t_fun_prime_unary_pure_def
      pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_negation_operator_in_domain, of w]
    by blast
  have representation:
      "pp_t_eqv Prop w ?p
        (pp_t_negation_operator \<acute> q)"
    by (rule pp_t_eqv_reflexive[OF p])
  have not_Dp:
      "\<not> pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
    by (rule
      pp_t_T6_recomputed_diagonal_false_on_negated_true_witness[
        OF q Jq q_true])
  have negation_p:
      "pp_t_holds (pp_t_negation_operator \<acute> ?p) w"
    using pp_t_negation_operator_holds[OF p, of w]
      pp_t_negation_operator_holds[OF q, of w]
      q_true
    by simp
  have applications:
      "pp_t_eqv Prop w
        (pp_t_negation_operator \<acute> ?p)
        (pp_t_T6_diagonal_T6_operator \<acute> ?p)"
    by (rule pp_t_app_respects[
      OF candidate p p pp_t_eqv_reflexive[OF p]])
  have at_w:
      "pp_t_holds (pp_t_negation_operator \<acute> ?p) w =
       pp_t_holds (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  show False using negation_p not_Dp at_w by blast
qed

lemma pp_t_T6_recomputed_diagonal_not_possible_falsity:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_possible_falsity_operator pp_t_T6_diagonal_T6_operator"
proof
  assume candidate:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_possible_falsity_operator
          pp_t_T6_diagonal_T6_operator"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
    using pp_t_T6_diagonal_has_true_witness[of w]
    by blast
  let ?p = "pp_t_negation_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain q])
  have not_p: "\<not> pp_t_holds ?p w"
    using pp_t_negation_operator_holds[OF q, of w]
      q_true by simp
  have not_settled_true:
      "\<not> pp_t_eqv Prop w ?p (pp_zf_truth True)"
  proof
    assume settled:
        "pp_t_eqv Prop w ?p (pp_zf_truth True)"
    have "pp_t_holds ?p w"
      using pp_t_prop_eqv_at[OF settled, of w] by simp
    then show False using not_p by blast
  qed
  have possible_falsity_p:
      "pp_t_holds (pp_t_possible_falsity_operator \<acute> ?p) w"
    using pp_t_possible_falsity_operator_holds[OF p, of w]
      not_settled_true by blast
  have not_Dp:
      "\<not> pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
    by (rule
      pp_t_T6_recomputed_diagonal_false_on_negated_true_witness[
        OF q Jq q_true])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_possible_falsity_operator \<acute> ?p)
        (pp_t_T6_diagonal_T6_operator \<acute> ?p)"
    by (rule pp_t_app_respects[
      OF candidate p p pp_t_eqv_reflexive[OF p]])
  have at_w:
      "pp_t_holds
          (pp_t_possible_falsity_operator \<acute> ?p) w
       =
       pp_t_holds (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
    using pp_t_prop_eqv_at[OF applications, of w] by simp
  show False using possible_falsity_p not_Dp at_w by blast
qed

theorem pp_t_T6_recomputed_diagonal_absorbed_iff_four_classes:
  "pp_t_T6_recomputed_diagonal_absorbed
    \<longleftrightarrow>
    (\<forall>w.
      pp_t_eqv pp_t_constants_unary_type
        w pp_t_negation_operator pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_possible_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator
          pp_t_T6_diagonal_T6_operator)"
  using pp_t_T6_recomputed_diagonal_absorbed_iff_ten_classes
    pp_t_T6_recomputed_diagonal_not_identity
    pp_t_T6_recomputed_diagonal_not_constant_truth
    pp_t_T6_recomputed_diagonal_not_constant_falsity
    pp_t_T6_recomputed_diagonal_not_necessity
    pp_t_T6_recomputed_diagonal_not_possibility
    pp_t_T6_recomputed_diagonal_not_old_fun_prime
  by blast

theorem pp_t_T6_recomputed_diagonal_absorbed_iff_two_classes:
  "pp_t_T6_recomputed_diagonal_absorbed
    \<longleftrightarrow>
    (\<forall>w.
      pp_t_eqv pp_t_constants_unary_type
        w pp_t_necessary_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator
          pp_t_T6_diagonal_T6_operator)"
  using pp_t_T6_recomputed_diagonal_absorbed_iff_four_classes
    pp_t_T6_recomputed_diagonal_not_negation
    pp_t_T6_recomputed_diagonal_not_possible_falsity
  by blast

theorem pp_t_T6_recomputed_diagonal_absorbed_iff_global_collision:
  "pp_t_T6_recomputed_diagonal_absorbed
    \<longleftrightarrow>
    pp_t_T6_diagonal_T6_operator =
      pp_t_necessary_falsity_operator
    \<or>
    pp_t_T6_diagonal_T6_operator =
      pp_t_fun_prime_T6_operator"
proof
  assume absorbed: "pp_t_T6_recomputed_diagonal_absorbed"
  have root:
      "pp_t_eqv pp_t_constants_unary_type
        [] pp_t_necessary_falsity_operator
          pp_t_T6_diagonal_T6_operator
      \<or> pp_t_eqv pp_t_constants_unary_type
        [] pp_t_fun_prime_T6_operator
          pp_t_T6_diagonal_T6_operator"
    using absorbed
    unfolding pp_t_T6_recomputed_diagonal_absorbed_iff_two_classes
    by blast
  have NF:
      "pp_t_eqv pp_t_constants_unary_type
          [] pp_t_necessary_falsity_operator
            pp_t_T6_diagonal_T6_operator
       \<Longrightarrow>
       pp_t_T6_diagonal_T6_operator =
         pp_t_necessary_falsity_operator"
  proof -
    assume eqv:
        "pp_t_eqv pp_t_constants_unary_type
          [] pp_t_necessary_falsity_operator
            pp_t_T6_diagonal_T6_operator"
    have "pp_t_necessary_falsity_operator =
        pp_t_T6_diagonal_T6_operator"
      using pp_t_root_eqv_iff_eq[
        OF pp_t_necessary_falsity_operator_in_domain
          pp_t_T6_diagonal_T6_operator_in_domain]
        eqv by blast
    then show ?thesis by simp
  qed
  have old_D:
      "pp_t_eqv pp_t_constants_unary_type
          [] pp_t_fun_prime_T6_operator
            pp_t_T6_diagonal_T6_operator
       \<Longrightarrow>
       pp_t_T6_diagonal_T6_operator =
         pp_t_fun_prime_T6_operator"
  proof -
    assume eqv:
        "pp_t_eqv pp_t_constants_unary_type
          [] pp_t_fun_prime_T6_operator
            pp_t_T6_diagonal_T6_operator"
    have "pp_t_fun_prime_T6_operator =
        pp_t_T6_diagonal_T6_operator"
      using pp_t_root_eqv_iff_eq[
        OF pp_t_fun_prime_T6_operator_in_domain
          pp_t_T6_diagonal_T6_operator_in_domain]
        eqv by blast
    then show ?thesis by simp
  qed
  show "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator
      \<or>
      pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    using root NF old_D by blast
next
  assume collision:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator
      \<or>
      pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  show "pp_t_T6_recomputed_diagonal_absorbed"
    unfolding pp_t_T6_recomputed_diagonal_absorbed_iff_two_classes
  proof
    fix w
    show "pp_t_eqv pp_t_constants_unary_type
          w pp_t_necessary_falsity_operator
            pp_t_T6_diagonal_T6_operator
        \<or>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_T6_diagonal_T6_operator"
    proof -
      from collision consider
          (NF) "pp_t_T6_diagonal_T6_operator =
            pp_t_necessary_falsity_operator"
        | (old_D) "pp_t_T6_diagonal_T6_operator =
            pp_t_fun_prime_T6_operator"
        by blast
      then show ?thesis
      proof cases
        case NF
        show ?thesis
          apply (rule disjI1)
          unfolding NF
          by (rule pp_t_eqv_reflexive[
            OF pp_t_necessary_falsity_operator_in_domain])
      next
        case old_D
        show ?thesis
          apply (rule disjI2)
          unfolding old_D
          by (rule pp_t_eqv_reflexive[
            OF pp_t_fun_prime_T6_operator_in_domain])
      qed
    qed
  qed
qed

lemma pp_t_T6_diagonal_new_fun_prime_implies_old:
  assumes q: "Elem q (pp_t_domain Prop)"
    and new_J:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
  shows "pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute> q) w"
proof -
  have new_predicate:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w q"
    using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
      OF q, of w]
      new_J by blast
  have old_predicate:
      "pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w q"
    by (rule pp_t_T6_diagonal_fun_prime_predicate_shrinks[
      OF q new_predicate])
  show ?thesis
    using pp_t_fun_prime_stock_J_holds_iff[OF q, of w]
      old_predicate by blast
qed

lemma pp_t_right_tip_old_fun_prime_fails:
  "\<not> pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute>
      pp_t_right_tip) [True]"
proof
  assume Jp:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute>
          pp_t_right_tip) [True]"
  have p: "Elem pp_t_right_tip (pp_t_domain Prop)"
    by (rule pp_t_right_tip_in_domain)
  have base:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] pp_t_right_tip"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF p, of "[True]"]
      pp_t_fun_prime_stabilizes[OF p, of "[True]"]
      Jp by blast
  obtain u v where future_u: "prefix [True] u"
    and true_u:
      "pp_t_eqv Prop u pp_t_right_tip
        (pp_zf_truth True)"
    and "prefix [True] v"
    and "pp_t_eqv Prop v pp_t_right_tip
      (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF p base] by blast
  have tip_child:
      "\<not> pp_t_holds pp_t_right_tip (u @ [False])"
    by (rule pp_t_right_tip_false_below[OF future_u])
  have tip_child_true:
      "pp_t_holds pp_t_right_tip (u @ [False])"
    using pp_t_prop_eqv_at[
      OF true_u, of "u @ [False]"] by simp
  show False using tip_child tip_child_true by blast
qed

definition pp_t_T6_right_tip_old_diagonal_reachable :: bool where
  "pp_t_T6_right_tip_old_diagonal_reachable \<longleftrightarrow>
    (\<exists>q.
      Elem q (pp_t_domain Prop)
      \<and> pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]
      \<and> pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_fun_prime_T6_operator \<acute> q))"

theorem pp_t_T6_right_tip_old_diagonal_unreachable:
  "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
proof
  assume reachable:
      "pp_t_T6_right_tip_old_diagonal_reachable"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]"
    and image:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_fun_prime_T6_operator \<acute> q)"
    using reachable
    unfolding pp_t_T6_right_tip_old_diagonal_reachable_def
    by blast
  have old_Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
    by (rule pp_t_T6_diagonal_new_fun_prime_implies_old[
      OF q new_Jq])
  have old_fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] q"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF q, of "[True]"]
      pp_t_fun_prime_stabilizes[OF q, of "[True]"]
      old_Jq by blast
  obtain u v where "prefix [True] u"
    and "pp_t_eqv Prop u q (pp_zf_truth True)"
    and future_v: "prefix [True] v"
    and false_v:
      "pp_t_eqv Prop v q (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF q old_fun_prime]
    by blast
  let ?r = "v @ [False]"
  have future_r: "prefix [True] ?r"
    using future_v
    by (auto simp: prefix_def append_assoc)
  have false_r:
      "pp_t_eqv Prop ?r q (pp_zf_truth False)"
    by (rule pp_t_eqv_persistent[OF false_v])
      simp
  have old_D_true:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> q) ?r"
  proof -
    have settled:
        "pp_t_eqv Prop ?r
          (pp_t_fun_prime_T6_operator \<acute> q)
          (pp_zf_truth True)"
      using pp_t_fun_prime_T6_on_settled[
        OF q false_r pp_t_fun_prime_has_witness_everywhere]
      by simp
    show ?thesis
      using pp_t_prop_eqv_at[OF settled, of ?r] by simp
  qed
  have image_r:
      "pp_t_holds pp_t_right_tip ?r =
       pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[OF image, of ?r] future_r .
  have not_tip:
      "\<not> pp_t_holds pp_t_right_tip ?r"
    by (rule pp_t_right_tip_false_below[OF future_v])
  show False using old_D_true image_r not_tip by blast
qed

lemma pp_t_T6_right_tip_reachable_implies_recomputed_fails:
  assumes reachable:
      "pp_t_T6_right_tip_old_diagonal_reachable"
  shows "\<not> pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      pp_t_right_tip) [True]"
proof
  assume recomputed:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute>
          pp_t_right_tip) [True]"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]"
    and representation:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_fun_prime_T6_operator \<acute> q)"
    using reachable
    unfolding pp_t_T6_right_tip_old_diagonal_reachable_def
    by blast
  have pure_old_D:
      "pp_t_T6_diagonal_unary_pure
        [True] pp_t_fun_prime_T6_operator"
    unfolding pp_t_T6_diagonal_unary_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_fun_prime_T6_operator_in_domain, of "[True]"]
    by blast
  have not_old_D_tip:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_right_tip) [True]"
    using pp_t_eval_T6_diagonal_T6_operator_holds[
        OF pp_t_right_tip_in_domain, of "[True]"]
      recomputed pp_t_fun_prime_T6_operator_in_domain q
      pure_old_D Jq representation
    by blast
  show False
    using not_old_D_tip pp_t_right_tip_T6_holds by blast
qed

lemma pp_t_T6_right_tip_unreachable_implies_recomputed_holds:
  assumes unreachable:
      "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
  shows "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      pp_t_right_tip) [True]"
proof -
  have p: "Elem pp_t_right_tip (pp_t_domain Prop)"
    by (rule pp_t_right_tip_in_domain)
  show ?thesis
    unfolding pp_t_eval_T6_diagonal_T6_operator_holds[OF p]
  proof (intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_T6_diagonal_unary_pure [True] X
          \<and> pp_t_holds
            (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]
          \<and> pp_t_eqv Prop [True] pp_t_right_tip (X \<acute> q)"
    have pure_X: "pp_t_T6_diagonal_unary_pure [True] X"
      using antecedent by blast
    have new_Jq:
        "pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]"
      using antecedent by blast
    have old_Jq:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
      by (rule pp_t_T6_diagonal_new_fun_prime_implies_old[
        OF q new_Jq])
    have p_Xq:
        "pp_t_eqv Prop [True] pp_t_right_tip (X \<acute> q)"
      using antecedent by blast
    obtain A where A_rep:
        "A \<in> pp_t_T6_ten_representatives"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type [True] A X"
      using pp_t_T6_ten_representative[OF pure_X]
      by blast
    have A_domain:
        "Elem A (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_T6_ten_representative_in_domain[OF A_rep])
    have Aq_Xq:
        "pp_t_eqv Prop [True] (A \<acute> q) (X \<acute> q)"
      by (rule pp_t_app_respects[
        OF AX q q pp_t_eqv_reflexive[OF q]])
    have p_Aq:
        "pp_t_eqv Prop [True] pp_t_right_tip (A \<acute> q)"
      using p q A_domain X
        pp_t_app_closed[OF A_domain q]
        pp_t_app_closed[OF X q]
        p_Xq Aq_Xq
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    have Ap_Xp:
        "pp_t_eqv Prop [True]
          (A \<acute> pp_t_right_tip)
          (X \<acute> pp_t_right_tip)"
      by (rule pp_t_app_respects[
        OF AX p p pp_t_eqv_reflexive[OF p]])
    have output_transfer:
        "pp_t_holds (A \<acute> pp_t_right_tip) [True] =
         pp_t_holds (X \<acute> pp_t_right_tip) [True]"
      using pp_t_prop_eqv_at[
        OF Ap_Xp, of "[True]"] by simp
    from A_rep consider
        (identity) "A = pp_t_identity_operator"
      | (negation) "A = pp_t_negation_operator"
      | (truth) "A = pp_t_constant_operator True"
      | (falsity) "A = pp_t_constant_operator False"
      | (necessity) "A = pp_t_necessity_operator"
      | (possibility) "A = pp_t_possibility_operator"
      | (necessary_falsity)
          "A = pp_t_necessary_falsity_operator"
      | (possible_falsity)
          "A = pp_t_possible_falsity_operator"
      | (old_fun_prime)
          "A = pp_t_quantified_fun_prime_operator"
      | (old_diagonal)
          "A = pp_t_fun_prime_T6_operator"
      unfolding pp_t_T6_ten_representatives_def
      by auto
    then show "\<not> pp_t_holds
        (X \<acute> pp_t_right_tip) [True]"
    proof cases
      case identity
      show ?thesis
        using pp_t_right_tip_not_identity_image_of_J[
          OF q old_Jq, unfolded identity[symmetric],
          OF p_Aq]
        by blast
    next
      case truth
      show ?thesis
        using pp_t_right_tip_not_truth_image[
          OF q, unfolded truth[symmetric], OF p_Aq]
        by blast
    next
      case possibility
      show ?thesis
        using pp_t_right_tip_not_possibility_image_of_J[
          OF q old_Jq, unfolded possibility[symmetric],
          OF p_Aq]
        by blast
    next
      case possible_falsity
      show ?thesis
        using pp_t_right_tip_not_possible_falsity_image_of_J[
          OF q old_Jq,
          unfolded possible_falsity[symmetric], OF p_Aq]
        by blast
    next
      case negation
      have not_Ap:
          "\<not> pp_t_holds
            (A \<acute> pp_t_right_tip) [True]"
        using pp_t_fun_prime_probe_signatures(2)[of "[]"]
        unfolding pp_t_fun_prime_probe_signature_def
          pp_t_right_tip_def negation by simp
      show ?thesis using not_Ap output_transfer by blast
    next
      case falsity
      have not_Ap:
          "\<not> pp_t_holds
            (A \<acute> pp_t_right_tip) [True]"
        using pp_t_fun_prime_probe_signatures(4)[of "[]"]
        unfolding pp_t_fun_prime_probe_signature_def
          pp_t_right_tip_def falsity by simp
      show ?thesis using not_Ap output_transfer by blast
    next
      case necessity
      have not_Ap:
          "\<not> pp_t_holds
            (A \<acute> pp_t_right_tip) [True]"
        using pp_t_fun_prime_probe_signatures(5)[of "[]"]
        unfolding pp_t_fun_prime_probe_signature_def
          pp_t_right_tip_def necessity by simp
      show ?thesis using not_Ap output_transfer by blast
    next
      case necessary_falsity
      have not_Ap:
          "\<not> pp_t_holds
            (A \<acute> pp_t_right_tip) [True]"
        using pp_t_fun_prime_probe_signatures(7)[of "[]"]
        unfolding pp_t_fun_prime_probe_signature_def
          pp_t_right_tip_def necessary_falsity by simp
      show ?thesis using not_Ap output_transfer by blast
    next
      case old_fun_prime
      have not_Ap:
          "\<not> pp_t_holds
            (A \<acute> pp_t_right_tip) [True]"
        using pp_t_right_tip_old_fun_prime_fails
        unfolding old_fun_prime .
      show ?thesis using not_Ap output_transfer by blast
    next
      case old_diagonal
      have reachable:
          "pp_t_T6_right_tip_old_diagonal_reachable"
        unfolding pp_t_T6_right_tip_old_diagonal_reachable_def
        using q new_Jq p_Aq
        unfolding old_diagonal
        by blast
      show ?thesis using unreachable reachable by blast
    qed
  qed
qed

theorem pp_t_T6_recomputed_right_tip_iff_unreachable:
  "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute>
        pp_t_right_tip) [True]
    \<longleftrightarrow>
    \<not> pp_t_T6_right_tip_old_diagonal_reachable"
  using pp_t_T6_right_tip_reachable_implies_recomputed_fails
    pp_t_T6_right_tip_unreachable_implies_recomputed_holds
  by blast

corollary pp_t_T6_recomputed_right_tip_holds:
  "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      pp_t_right_tip) [True]"
  by (rule
    pp_t_T6_right_tip_unreachable_implies_recomputed_holds[
      OF pp_t_T6_right_tip_old_diagonal_unreachable])

corollary pp_t_T6_recomputed_diagonal_not_necessary_falsity:
  "pp_t_T6_diagonal_T6_operator \<noteq>
    pp_t_necessary_falsity_operator"
proof
  assume equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator"
  show False
    using pp_t_T6_recomputed_right_tip_holds
      pp_t_right_tip_necessary_falsity_fails equality
    by simp
qed

theorem pp_t_T6_recomputed_diagonal_absorbed_iff_old_diagonal:
  "pp_t_T6_recomputed_diagonal_absorbed
    \<longleftrightarrow>
    pp_t_T6_diagonal_T6_operator =
      pp_t_fun_prime_T6_operator"
  using
    pp_t_T6_recomputed_diagonal_absorbed_iff_global_collision
    pp_t_T6_recomputed_diagonal_not_necessary_falsity
  by blast

corollary pp_t_T6_builder_application_closed_iff_old_diagonal:
  "pp_t_T6_builder_application_closed
    \<longleftrightarrow>
    pp_t_T6_diagonal_T6_operator =
      pp_t_fun_prime_T6_operator"
  using pp_t_T6_builder_application_closed_iff
    pp_t_T6_recomputed_diagonal_absorbed_iff_old_diagonal
  by blast

lemma pp_t_T6_old_diagonal_square_fails_if_builder_stabilizes:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    and q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
  shows "\<not> pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute>
      (pp_t_fun_prime_T6_operator \<acute> q)) w"
proof
  let ?p = "pp_t_fun_prime_T6_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  assume old_square:
      "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> ?p) w"
  have recomputed_square:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute> ?p) w"
    using old_square equality by simp
  have pure_old_D:
      "pp_t_T6_diagonal_unary_pure
        w pp_t_fun_prime_T6_operator"
    unfolding pp_t_T6_diagonal_unary_pure_def
    using pp_t_eqv_reflexive[
      OF pp_t_fun_prime_T6_operator_in_domain, of w]
    by blast
  have representation:
      "pp_t_eqv Prop w ?p
        (pp_t_fun_prime_T6_operator \<acute> q)"
    by (rule pp_t_eqv_reflexive[OF p])
  have not_old_square:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> ?p) w"
    using pp_t_eval_T6_diagonal_T6_operator_holds[
        OF p, of w]
      recomputed_square pp_t_fun_prime_T6_operator_in_domain
      q pure_old_D new_Jq representation
    by blast
  show False using old_square not_old_square by blast
qed

theorem pp_t_T6_builder_stability_forces_cross_input_witness:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    and q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
  shows "\<exists>X r.
    Elem X (pp_t_domain pp_t_constants_unary_type)
    \<and> Elem r (pp_t_domain Prop)
    \<and> pp_t_fun_prime_unary_pure w X
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> r) w
    \<and> pp_t_eqv Prop w
      (pp_t_fun_prime_T6_operator \<acute> q) (X \<acute> r)
    \<and> pp_t_holds
      (X \<acute> (pp_t_fun_prime_T6_operator \<acute> q)) w"
proof -
  let ?p = "pp_t_fun_prime_T6_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  have not_square:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> ?p) w"
    by (rule
      pp_t_T6_old_diagonal_square_fails_if_builder_stabilizes[
        OF equality q new_Jq])
  have not_universal:
      "\<not> (\<forall>X.
        Elem X (pp_t_domain pp_t_constants_unary_type)
        \<longrightarrow>
        (\<forall>r.
          Elem r (pp_t_domain Prop)
          \<longrightarrow>
          (pp_t_fun_prime_unary_pure w X
            \<and> pp_t_holds
              (pp_t_quantified_fun_prime_operator \<acute> r) w
            \<and> pp_t_eqv Prop w ?p (X \<acute> r))
          \<longrightarrow> \<not> pp_t_holds (X \<acute> ?p) w))"
    using pp_t_fun_prime_T6_operator_holds[OF p, of w]
      not_square by blast
  show ?thesis
    using not_universal by blast
qed

corollary pp_t_T6_builder_stability_forces_nine_class_orbit:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    and q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
  shows "\<exists>A \<in> pp_t_fun_prime_nine_representatives.
    \<exists>r.
      Elem r (pp_t_domain Prop)
      \<and> pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w
      \<and> pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> q) (A \<acute> r)
      \<and> pp_t_holds
        (A \<acute> (pp_t_fun_prime_T6_operator \<acute> q)) w"
proof -
  let ?p = "pp_t_fun_prime_T6_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  obtain X r where X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure_X: "pp_t_fun_prime_unary_pure w X"
    and old_Jr:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    and p_Xr: "pp_t_eqv Prop w ?p (X \<acute> r)"
    and Xp: "pp_t_holds (X \<acute> ?p) w"
    using pp_t_T6_builder_stability_forces_cross_input_witness[
      OF equality q new_Jq]
    by blast
  obtain A where A:
      "A \<in> pp_t_fun_prime_nine_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    using pp_t_fun_prime_unary_pure_represented[OF X]
      pure_X by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_nine_representative_in_domain[OF A])
  have Ar_Xr:
      "pp_t_eqv Prop w (A \<acute> r) (X \<acute> r)"
    by (rule pp_t_app_respects[
      OF AX r r pp_t_eqv_reflexive[OF r]])
  have p_Ar: "pp_t_eqv Prop w ?p (A \<acute> r)"
    using p r A_domain X
      pp_t_app_closed[OF A_domain r]
      pp_t_app_closed[OF X r]
      p_Xr Ar_Xr
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have Ap_Xp:
      "pp_t_eqv Prop w (A \<acute> ?p) (X \<acute> ?p)"
    by (rule pp_t_app_respects[
      OF AX p p pp_t_eqv_reflexive[OF p]])
  have Ap: "pp_t_holds (A \<acute> ?p) w"
    using pp_t_prop_eqv_at[OF Ap_Xp, of w] Xp
    by blast
  show ?thesis using A r old_Jr p_Ar Ap by blast
qed

lemma pp_t_fun_prime_T6_false_on_true_new_fun_prime:
  assumes q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
  shows "\<not> pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> q) w"
proof
  assume Dq:
      "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w"
  have old_Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) w"
    by (rule pp_t_T6_diagonal_new_fun_prime_implies_old[
      OF q new_Jq])
  have identity_q:
      "pp_t_identity_operator \<acute> q = q"
    using q by (simp add: pp_t_identity_operator_def Lambda_app)
  have representation:
      "pp_t_eqv Prop w q (pp_t_identity_operator \<acute> q)"
    unfolding identity_q
    by (rule pp_t_eqv_reflexive[OF q])
  have not_identity_q:
      "\<not> pp_t_holds (pp_t_identity_operator \<acute> q) w"
    using pp_t_fun_prime_T6_operator_holds[OF q, of w]
      Dq pp_t_identity_operator_in_domain q
      pp_t_fun_prime_identity_is_pure old_Jq representation
    by blast
  show False
    using not_identity_q q_true unfolding identity_q by blast
qed

definition pp_t_T6_remaining_orbit_representatives :: "ZF set" where
  "pp_t_T6_remaining_orbit_representatives = {
    pp_t_negation_operator}"

theorem pp_t_T6_builder_stability_forces_negation_orbit:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  shows "\<exists>q A r.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds q w
    \<and> A \<in> pp_t_T6_remaining_orbit_representatives
    \<and> Elem r (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> r) w
    \<and> pp_t_eqv Prop w
      (pp_t_fun_prime_T6_operator \<acute> q) (A \<acute> r)
    \<and> pp_t_holds
      (A \<acute> (pp_t_fun_prime_T6_operator \<acute> q)) w"
proof -
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
    using pp_t_T6_diagonal_has_true_witness[of w]
    by blast
  let ?p = "pp_t_fun_prime_T6_operator \<acute> q"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  have not_p: "\<not> pp_t_holds ?p w"
    by (rule pp_t_fun_prime_T6_false_on_true_new_fun_prime[
      OF q new_Jq q_true])
  have not_square:
      "\<not> pp_t_holds (pp_t_fun_prime_T6_operator \<acute> ?p) w"
    by (rule
      pp_t_T6_old_diagonal_square_fails_if_builder_stabilizes[
        OF equality q new_Jq])
  obtain A r where A:
      "A \<in> pp_t_fun_prime_nine_representatives"
    and r: "Elem r (pp_t_domain Prop)"
    and old_Jr:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    and p_Ar: "pp_t_eqv Prop w ?p (A \<acute> r)"
    and Ap: "pp_t_holds (A \<acute> ?p) w"
    using pp_t_T6_builder_stability_forces_nine_class_orbit[
      OF equality q new_Jq]
    by blast
  have not_Ar: "\<not> pp_t_holds (A \<acute> r) w"
  proof
    assume Ar: "pp_t_holds (A \<acute> r) w"
    have p_true: "pp_t_holds ?p w"
      using pp_t_prop_eqv_at[OF p_Ar, of w] Ar
      by blast
    show False using not_p p_true by blast
  qed
  have A_remaining:
      "A \<in> pp_t_T6_remaining_orbit_representatives"
  proof -
    from A consider
        (identity) "A = pp_t_identity_operator"
      | (negation) "A = pp_t_negation_operator"
      | (truth) "A = pp_t_constant_operator True"
      | (falsity) "A = pp_t_constant_operator False"
      | (necessity) "A = pp_t_necessity_operator"
      | (possibility) "A = pp_t_possibility_operator"
      | (necessary_falsity)
          "A = pp_t_necessary_falsity_operator"
      | (possible_falsity)
          "A = pp_t_possible_falsity_operator"
      | (old_fun_prime)
          "A = pp_t_quantified_fun_prime_operator"
      unfolding pp_t_fun_prime_nine_representatives_def
        pp_t_fun_prime_probe_representatives_def
      by auto
    then show ?thesis
    proof cases
      case identity
      have identity_p:
          "A \<acute> ?p = ?p"
        using p unfolding identity
        by (simp add: pp_t_identity_operator_def Lambda_app)
      show ?thesis using Ap not_p unfolding identity_p by blast
    next
      case truth
      have A_r_true: "pp_t_holds (A \<acute> r) w"
        using pp_t_constant_operator_holds[OF r, of True w]
        unfolding truth by simp
      have p_true: "pp_t_holds ?p w"
        using pp_t_prop_eqv_at[OF p_Ar, of w] A_r_true
        by blast
      show ?thesis using not_p p_true by blast
    next
      case falsity
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) w"
        using pp_t_constant_operator_holds[OF p, of False w]
        unfolding falsity by simp
      show ?thesis using Ap not_Ap by blast
    next
      case necessity
      have settled_true:
          "pp_t_eqv Prop w ?p (pp_zf_truth True)"
        using pp_t_necessity_operator_holds[OF p, of w]
          Ap unfolding necessity by blast
      have p_true: "pp_t_holds ?p w"
        using pp_t_prop_eqv_at[OF settled_true, of w]
        by simp
      show ?thesis using not_p p_true by blast
    next
      case negation
      show ?thesis
        unfolding pp_t_T6_remaining_orbit_representatives_def
          negation by simp
    next
      case possibility
      have no_true_future:
          "\<not> (\<exists>v. prefix w v \<and> pp_t_holds r v)"
        using pp_t_possibility_operator_holds[OF r, of w]
          not_Ar unfolding possibility by blast
      have settled_false:
          "pp_t_eqv Prop w r (pp_zf_truth False)"
        unfolding pp_t_eqv.simps
        using no_true_future by auto
      have not_old_Jr:
          "\<not> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> r) w"
        by (rule pp_t_quantified_fun_prime_false_on_settled[
          OF r settled_false])
      show ?thesis using old_Jr not_old_Jr by blast
    next
      case necessary_falsity
      have settled_false:
          "pp_t_eqv Prop w ?p (pp_zf_truth False)"
        using pp_t_necessary_falsity_operator_holds[
            OF p, of w]
          Ap unfolding necessary_falsity by blast
      have square:
          "pp_t_holds
            (pp_t_fun_prime_T6_operator \<acute> ?p) w"
      proof -
        have square_settled:
            "pp_t_eqv Prop w
              (pp_t_fun_prime_T6_operator \<acute> ?p)
              (pp_zf_truth True)"
          using pp_t_fun_prime_T6_on_settled[
            OF p settled_false
              pp_t_fun_prime_has_witness_everywhere]
          by simp
        show ?thesis
          using pp_t_prop_eqv_at[OF square_settled, of w]
          by simp
      qed
      show ?thesis using not_square square by blast
    next
      case possible_falsity
      have settled_true:
          "pp_t_eqv Prop w r (pp_zf_truth True)"
        using pp_t_possible_falsity_operator_holds[
            OF r, of w]
          not_Ar unfolding possible_falsity by blast
      have not_old_Jr:
          "\<not> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> r) w"
        by (rule pp_t_quantified_fun_prime_false_on_settled[
          OF r settled_true])
      show ?thesis using old_Jr not_old_Jr by blast
    next
      case old_fun_prime
      show ?thesis
        using old_Jr not_Ar unfolding old_fun_prime by blast
    qed
  qed
  show ?thesis
    using q new_Jq q_true A_remaining r old_Jr p_Ar Ap
    by blast
qed

lemma pp_t_fun_prime_T6_not_negation_at_any_world:
  "\<not> pp_t_eqv pp_t_constants_unary_type
    w pp_t_fun_prime_T6_operator pp_t_negation_operator"
proof
  assume local:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator pp_t_negation_operator"
  have negation_cone:
      "\<And>s. pp_t_cone_rel pp_t_constants_unary_type s
        pp_t_negation_operator pp_t_negation_operator"
    by (rule
      pp_t_unary_operator_equivariant_implies_cone_related[
        OF pp_t_negation_operator_in_domain
          pp_t_negation_operator_equivariant])
  have root:
      "pp_t_eqv pp_t_constants_unary_type
        [] pp_t_fun_prime_T6_operator pp_t_negation_operator"
    using
      pp_t_cone_invariant_eqv_root_iff[
        OF pp_t_fun_prime_T6_operator_in_domain
          pp_t_negation_operator_in_domain
          pp_t_fun_prime_T6_operator_cone_related
          negation_cone,
        of w]
      local by blast
  have applications:
      "pp_t_eqv Prop []
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime)
        (pp_t_negation_operator \<acute>
          pp_t_recurrent_fun_prime)"
    by (rule pp_t_app_respects[
      OF root pp_t_recurrent_fun_prime_in_domain
        pp_t_recurrent_fun_prime_in_domain
        pp_t_eqv_reflexive[
          OF pp_t_recurrent_fun_prime_in_domain]])
  show False
    using applications pp_t_recurrent_no_negation_collision
    by blast
qed

corollary pp_t_T6_builder_stability_forces_distinct_fun_prime_negation_representation:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  shows "\<exists>q r.
    Elem q (pp_t_domain Prop)
    \<and> Elem r (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds q w
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> r) w
    \<and> pp_t_holds r w
    \<and> \<not> pp_t_eqv Prop w q r
    \<and> pp_t_eqv Prop w
      (pp_t_fun_prime_T6_operator \<acute> q)
      (pp_t_negation_operator \<acute> r)"
proof -
  obtain q A r where q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
    and A:
      "A \<in> pp_t_T6_remaining_orbit_representatives"
    and r: "Elem r (pp_t_domain Prop)"
    and old_Jr:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    and image:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> q) (A \<acute> r)"
    and "pp_t_holds
      (A \<acute> (pp_t_fun_prime_T6_operator \<acute> q)) w"
    using pp_t_T6_builder_stability_forces_negation_orbit[
      OF equality, of w]
    by blast
  have A_negation: "A = pp_t_negation_operator"
    using A
    unfolding pp_t_T6_remaining_orbit_representatives_def
    by simp
  have image_negation:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> q)
        (pp_t_negation_operator \<acute> r)"
    using image unfolding A_negation .
  have old_D_q_false:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> q) w"
    by (rule pp_t_fun_prime_T6_false_on_true_new_fun_prime[
      OF q new_Jq q_true])
  have negation_r_false:
      "\<not> pp_t_holds (pp_t_negation_operator \<acute> r) w"
    using pp_t_prop_eqv_at[OF image_negation, of w]
      old_D_q_false by blast
  have r_true: "pp_t_holds r w"
    using pp_t_negation_operator_holds[OF r, of w]
      negation_r_false by simp
  have not_qr: "\<not> pp_t_eqv Prop w q r"
  proof
    assume qr: "pp_t_eqv Prop w q r"
    have negation_qr:
        "pp_t_eqv Prop w
          (pp_t_negation_operator \<acute> q)
          (pp_t_negation_operator \<acute> r)"
      by (rule pp_t_app_respects[
        OF pp_t_eqv_reflexive[
            OF pp_t_negation_operator_in_domain, of w]
          q r qr])
    have outputs:
        "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> q)
          (pp_t_negation_operator \<acute> q)"
      using pp_t_app_closed[
          OF pp_t_fun_prime_T6_operator_in_domain q]
        pp_t_app_closed[OF pp_t_negation_operator_in_domain q]
        pp_t_app_closed[OF pp_t_negation_operator_in_domain r]
        image_negation negation_qr
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    have new_predicate:
        "pp_t_fun_prime_predicate
          pp_t_T6_diagonal_unary_pure w q"
      using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
        OF q, of w]
        new_Jq by blast
    have pure_old_D:
        "pp_t_T6_diagonal_unary_pure
          w pp_t_fun_prime_T6_operator"
      unfolding pp_t_T6_diagonal_unary_pure_def
      using pp_t_eqv_reflexive[
        OF pp_t_fun_prime_T6_operator_in_domain, of w]
      by blast
    have pure_negation:
        "pp_t_T6_diagonal_unary_pure w pp_t_negation_operator"
      unfolding pp_t_T6_diagonal_unary_pure_def
        pp_t_fun_prime_unary_pure_def
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_negation_operator_in_domain, of w]
      by blast
    have operators:
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator pp_t_negation_operator"
      using new_predicate
        pp_t_fun_prime_T6_operator_in_domain
        pp_t_negation_operator_in_domain
        pure_old_D pure_negation outputs
      unfolding pp_t_fun_prime_predicate_def
      by blast
    show False
      using operators pp_t_fun_prime_T6_not_negation_at_any_world
      by blast
  qed
  show ?thesis
    using q r new_Jq q_true old_Jr r_true not_qr image_negation
    by blast
qed

lemma pp_t_negation_settled_iff:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "pp_t_eqv Prop w
      (pp_t_negation_operator \<acute> r)
      (pp_zf_truth (\<not> b))
    \<longleftrightarrow>
    pp_t_eqv Prop w r (pp_zf_truth b)"
  unfolding pp_t_eqv.simps
  using pp_t_negation_operator_holds[OF r]
  by (cases b) auto

definition pp_t_settled_cones_preserved ::
    "bool list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_t_settled_cones_preserved w q r \<longleftrightarrow>
    (\<forall>u b.
      prefix w u
      \<longrightarrow>
      pp_t_eqv Prop u q (pp_zf_truth b)
      \<longrightarrow>
      pp_t_eqv Prop u r (pp_zf_truth b))"

theorem pp_t_T6_builder_stability_forces_distinct_settled_cone_preservation:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  shows "\<exists>q r.
    Elem q (pp_t_domain Prop)
    \<and> Elem r (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> r) w
    \<and> \<not> pp_t_eqv Prop w q r
    \<and> pp_t_settled_cones_preserved w q r"
proof -
  obtain q r where q: "Elem q (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and "pp_t_holds q w"
    and old_Jr:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    and "pp_t_holds r w"
    and not_qr: "\<not> pp_t_eqv Prop w q r"
    and image:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> q)
        (pp_t_negation_operator \<acute> r)"
    using
      pp_t_T6_builder_stability_forces_distinct_fun_prime_negation_representation[
      OF equality, of w]
    by blast
  have preserves:
      "pp_t_settled_cones_preserved w q r"
    unfolding pp_t_settled_cones_preserved_def
  proof (intro allI impI)
    fix u b
    assume future: "prefix w u"
      and q_settled:
        "pp_t_eqv Prop u q (pp_zf_truth b)"
    have image_u:
        "pp_t_eqv Prop u
          (pp_t_fun_prime_T6_operator \<acute> q)
          (pp_t_negation_operator \<acute> r)"
      by (rule pp_t_eqv_persistent[OF image future])
    have D_settled:
        "pp_t_eqv Prop u
          (pp_t_fun_prime_T6_operator \<acute> q)
          (pp_zf_truth (\<not> b))"
      by (rule pp_t_fun_prime_T6_on_settled[
        OF q q_settled pp_t_fun_prime_has_witness_everywhere])
    have negation_settled:
        "pp_t_eqv Prop u
          (pp_t_negation_operator \<acute> r)
          (pp_zf_truth (\<not> b))"
      using pp_t_app_closed[
          OF pp_t_fun_prime_T6_operator_in_domain q]
        pp_t_app_closed[OF pp_t_negation_operator_in_domain r]
        pp_t_truth_in_domain image_u D_settled
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    show "pp_t_eqv Prop u r (pp_zf_truth b)"
      using pp_t_negation_settled_iff[OF r, of u b]
        negation_settled by blast
  qed
  show ?thesis
    using q r new_Jq old_Jr not_qr preserves by blast
qed

theorem pp_t_T6_builder_stability_forces_fun_prime_after_negated_diagonal:
  assumes equality:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds q w
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute>
        (pp_t_negation_operator \<acute>
          (pp_t_fun_prime_T6_operator \<acute> q))) w"
proof -
  obtain q r where q: "Elem q (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
    and q_true: "pp_t_holds q w"
    and old_Jr:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> r) w"
    and "pp_t_holds r w"
    and "\<not> pp_t_eqv Prop w q r"
    and image:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> q)
        (pp_t_negation_operator \<acute> r)"
    using
      pp_t_T6_builder_stability_forces_distinct_fun_prime_negation_representation[
        OF equality, of w]
    by blast
  let ?p = "pp_t_fun_prime_T6_operator \<acute> q"
  let ?s = "pp_t_negation_operator \<acute> ?p"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  have s: "Elem ?s (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain p])
  have neg_r:
      "Elem (pp_t_negation_operator \<acute> r)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain r])
  have double_neg_r:
      "Elem
        (pp_t_negation_operator \<acute>
          (pp_t_negation_operator \<acute> r))
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain neg_r])
  have negated_image:
      "pp_t_eqv Prop w ?s
        (pp_t_negation_operator \<acute>
          (pp_t_negation_operator \<acute> r))"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_negation_operator_in_domain, of w]
        p neg_r image])
  have double_negation:
      "pp_t_eqv Prop w
        (pp_t_negation_operator \<acute>
          (pp_t_negation_operator \<acute> r)) r"
    unfolding pp_t_eqv.simps
    using pp_t_negation_operator_holds[OF r]
      pp_t_negation_operator_holds[OF neg_r]
    by simp
  have s_r: "pp_t_eqv Prop w ?s r"
    by (rule pp_t_eqv_transitive[
      OF s double_neg_r r negated_image double_negation])
  have J_applications:
      "pp_t_eqv Prop w
        (pp_t_quantified_fun_prime_operator \<acute> ?s)
        (pp_t_quantified_fun_prime_operator \<acute> r)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_quantified_fun_prime_operator_in_domain, of w]
        s r s_r])
  have old_Js:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> ?s) w"
    using pp_t_prop_eqv_at[OF J_applications, of w]
      old_Jr by blast
  show ?thesis using q new_Jq q_true old_Js by blast
qed

subsection \<open>Joint separation after the old T6 operator\<close>

lemma pp_b_equivariant_compose:
  assumes F: "pp_b_equivariant F"
    and G: "pp_b_equivariant G"
  shows "pp_b_equivariant (\<lambda>P. F (G P))"
  using F G
  unfolding pp_b_equivariant_def
  by simp

definition pp_b_T6_negated_diagonal_then ::
    "ZF \<Rightarrow> pp_b_operator" where
  "pp_b_T6_negated_diagonal_then A P =
    pp_b_operator_of A
      (pp_b_operator_of pp_t_negation_operator
        (pp_b_operator_of pp_t_fun_prime_T6_operator P))"

lemma pp_b_T6_negated_diagonal_then_equivariant:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
  shows "pp_b_equivariant
    (pp_b_T6_negated_diagonal_then A)"
  unfolding pp_b_T6_negated_diagonal_then_def
  by (rule pp_b_equivariant_compose[
      OF pp_t_fun_prime_probe_representative_equivariant[OF A]])
    (rule pp_b_equivariant_compose[
      OF pp_t_negation_operator_equivariant
        pp_t_fun_prime_T6_operator_equivariant])

definition pp_t_T6_negated_diagonal_transforms_injective :: bool where
  "pp_t_T6_negated_diagonal_transforms_injective \<longleftrightarrow>
    (\<forall>A \<in> pp_t_fun_prime_probe_representatives.
      \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        pp_b_T6_negated_diagonal_then A =
          pp_b_T6_negated_diagonal_then B
        \<longrightarrow> A = B)"

lemma pp_b_T6_negated_diagonal_then_application:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_b_T6_negated_diagonal_then A (pp_b_of_zf p) =
    pp_b_of_zf
      (A \<acute>
        (pp_t_negation_operator \<acute>
          (pp_t_fun_prime_T6_operator \<acute> p)))"
proof -
  have Dp:
      "Elem (pp_t_fun_prime_T6_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain p])
  have not_Dp:
      "Elem
        (pp_t_negation_operator \<acute>
          (pp_t_fun_prime_T6_operator \<acute> p))
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain Dp])
  show ?thesis
    unfolding pp_b_T6_negated_diagonal_then_def
      pp_b_operator_of_def
    using pp_zf_of_b_of_zf[OF p]
      pp_zf_of_b_of_zf[OF Dp]
      pp_zf_of_b_of_zf[OF not_Dp]
    by simp
qed

definition pp_t_T6_punctured_right_tip :: ZF where
  "pp_t_T6_punctured_right_tip =
    pp_t_negation_operator \<acute> pp_t_right_tip"

lemma pp_t_T6_punctured_right_tip_in_domain:
  "Elem pp_t_T6_punctured_right_tip (pp_t_domain Prop)"
  unfolding pp_t_T6_punctured_right_tip_def
  by (rule pp_t_app_closed[
    OF pp_t_negation_operator_in_domain
      pp_t_right_tip_in_domain])

lemma pp_t_T6_punctured_right_tip_on_right_cone:
  assumes future: "prefix [True] v"
  shows "pp_t_holds pp_t_T6_punctured_right_tip v
    \<longleftrightarrow> v \<noteq> [True]"
  unfolding pp_t_T6_punctured_right_tip_def
  using pp_t_negation_operator_holds[
      OF pp_t_right_tip_in_domain, of v]
    pp_t_right_tip_on_right_cone[OF future]
  by simp

lemma pp_t_T6_punctured_right_tip_false_at_tip:
  "\<not> pp_t_holds pp_t_T6_punctured_right_tip [True]"
  using pp_t_T6_punctured_right_tip_on_right_cone[
    of "[True]"]
  by simp

lemma pp_t_T6_punctured_right_tip_true_below:
  assumes future: "prefix [True] v"
  shows "pp_t_holds pp_t_T6_punctured_right_tip
    (v @ [False])"
proof -
  have child_future: "prefix [True] (v @ [False])"
    using future by (auto simp: prefix_def append_assoc)
  have different: "v @ [False] \<noteq> [True]"
    by auto
  show ?thesis
    using pp_t_T6_punctured_right_tip_on_right_cone[
      OF child_future]
      different by blast
qed

lemma pp_t_T6_punctured_right_tip_settled_below:
  "pp_t_eqv Prop [True, False]
    pp_t_T6_punctured_right_tip (pp_zf_truth True)"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume future: "prefix [True, False] v"
  have right_future: "prefix [True] v"
    using future by (auto simp: prefix_def)
  have different: "v \<noteq> [True]"
    using future by (auto simp: prefix_def)
  show "pp_t_holds pp_t_T6_punctured_right_tip v =
      pp_t_holds (pp_zf_truth True) v"
    using pp_t_T6_punctured_right_tip_on_right_cone[
      OF right_future]
      different by simp
qed

lemma pp_t_T6_punctured_right_tip_old_fun_prime_fails:
  "\<not> pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute>
      pp_t_T6_punctured_right_tip) [True]"
proof
  assume Jp:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute>
          pp_t_T6_punctured_right_tip) [True]"
  have p:
      "Elem pp_t_T6_punctured_right_tip (pp_t_domain Prop)"
    by (rule pp_t_T6_punctured_right_tip_in_domain)
  have base:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True]
        pp_t_T6_punctured_right_tip"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF p, of "[True]"]
      pp_t_fun_prime_stabilizes[OF p, of "[True]"]
      Jp by blast
  obtain u v where "prefix [True] u"
    and "pp_t_eqv Prop u pp_t_T6_punctured_right_tip
      (pp_zf_truth True)"
    and future_v: "prefix [True] v"
    and false_v:
      "pp_t_eqv Prop v pp_t_T6_punctured_right_tip
        (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF p base] by blast
  have true_child:
      "pp_t_holds pp_t_T6_punctured_right_tip
        (v @ [False])"
    by (rule pp_t_T6_punctured_right_tip_true_below[
      OF future_v])
  have false_child:
      "\<not> pp_t_holds pp_t_T6_punctured_right_tip
        (v @ [False])"
    using pp_t_prop_eqv_at[
      OF false_v, of "v @ [False]"]
    by simp
  show False using true_child false_child by blast
qed

theorem pp_t_T6_old_diagonal_holds_on_punctured_right_tip:
  "pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_T6_punctured_right_tip) [True]"
proof -
  let ?p = pp_t_T6_punctured_right_tip
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_T6_punctured_right_tip_in_domain)
  show ?thesis
    unfolding pp_t_fun_prime_T6_operator_holds[OF p]
  proof (intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_fun_prime_unary_pure [True] X
          \<and> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> q) [True]
          \<and> pp_t_eqv Prop [True] ?p (X \<acute> q)"
    have pure_X: "pp_t_fun_prime_unary_pure [True] X"
      using antecedent by blast
    have Jq:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
      using antecedent by blast
    have p_Xq: "pp_t_eqv Prop [True] ?p (X \<acute> q)"
      using antecedent by blast
    obtain A where A:
        "A \<in> pp_t_fun_prime_nine_representatives"
      and AX:
        "pp_t_eqv pp_t_constants_unary_type [True] A X"
      using pp_t_fun_prime_unary_pure_represented[OF X]
        pure_X by blast
    have A_domain:
        "Elem A (pp_t_domain pp_t_constants_unary_type)"
      by (rule pp_t_fun_prime_nine_representative_in_domain[
        OF A])
    have Aq_Xq:
        "pp_t_eqv Prop [True] (A \<acute> q) (X \<acute> q)"
      by (rule pp_t_app_respects[
        OF AX q q pp_t_eqv_reflexive[OF q]])
    have p_Aq: "pp_t_eqv Prop [True] ?p (A \<acute> q)"
      using p q A_domain X
        pp_t_app_closed[OF A_domain q]
        pp_t_app_closed[OF X q]
        p_Xq Aq_Xq
      by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
    have Ap_Xp:
        "pp_t_eqv Prop [True] (A \<acute> ?p) (X \<acute> ?p)"
      by (rule pp_t_app_respects[
        OF AX p p pp_t_eqv_reflexive[OF p]])
    have output_transfer:
        "pp_t_holds (A \<acute> ?p) [True] =
         pp_t_holds (X \<acute> ?p) [True]"
      using pp_t_prop_eqv_at[
        OF Ap_Xp, of "[True]"] by simp
    have base_q:
        "pp_t_fun_prime_predicate
          pp_t_quantified_unary_pure [True] q"
      using pp_t_fun_prime_stock_J_holds_iff[
          OF q, of "[True]"]
        pp_t_fun_prime_stabilizes[OF q, of "[True]"]
        Jq by blast
    obtain u v where future_u: "prefix [True] u"
      and true_u:
        "pp_t_eqv Prop u q (pp_zf_truth True)"
      and future_v: "prefix [True] v"
      and false_v:
        "pp_t_eqv Prop v q (pp_zf_truth False)"
      using pp_t_base_injective_has_homogeneous_cones[
        OF q base_q] by blast
    from A consider
        (identity) "A = pp_t_identity_operator"
      | (negation) "A = pp_t_negation_operator"
      | (truth) "A = pp_t_constant_operator True"
      | (falsity) "A = pp_t_constant_operator False"
      | (necessity) "A = pp_t_necessity_operator"
      | (possibility) "A = pp_t_possibility_operator"
      | (necessary_falsity)
          "A = pp_t_necessary_falsity_operator"
      | (possible_falsity)
          "A = pp_t_possible_falsity_operator"
      | (old_fun_prime)
          "A = pp_t_quantified_fun_prime_operator"
      unfolding pp_t_fun_prime_nine_representatives_def
        pp_t_fun_prime_probe_representatives_def
      by auto
    then show "\<not> pp_t_holds (X \<acute> ?p) [True]"
    proof cases
      case identity
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) [True]"
        using pp_t_T6_punctured_right_tip_false_at_tip
          p
        unfolding identity
        by (simp add: pp_t_identity_operator_def Lambda_app)
      show ?thesis using not_Ap output_transfer by blast
    next
      case falsity
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) [True]"
        using pp_t_constant_operator_holds[
          OF p, of False "[True]"]
        unfolding falsity by simp
      show ?thesis using not_Ap output_transfer by blast
    next
      case necessity
      have not_true:
          "\<not> pp_t_eqv Prop [True] ?p (pp_zf_truth True)"
      proof
        assume settled:
            "pp_t_eqv Prop [True] ?p (pp_zf_truth True)"
        have at_tip: "pp_t_holds ?p [True]"
          using pp_t_prop_eqv_at[
            OF settled, of "[True]"] by simp
        show False
          using at_tip
            pp_t_T6_punctured_right_tip_false_at_tip
          by blast
      qed
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) [True]"
        using pp_t_necessity_operator_holds[OF p, of "[True]"]
          not_true unfolding necessity by blast
      show ?thesis using not_Ap output_transfer by blast
    next
      case necessary_falsity
      have not_false:
          "\<not> pp_t_eqv Prop [True] ?p (pp_zf_truth False)"
      proof
        assume settled:
            "pp_t_eqv Prop [True] ?p (pp_zf_truth False)"
        have at_child:
            "\<not> pp_t_holds ?p [True, False]"
          using pp_t_prop_eqv_at[
            OF settled, of "[True, False]"] by simp
        have child_true:
            "pp_t_holds ?p [True, False]"
          using pp_t_T6_punctured_right_tip_true_below[
            of "[True]"] by simp
        show False using at_child child_true by blast
      qed
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) [True]"
        using pp_t_necessary_falsity_operator_holds[
          OF p, of "[True]"]
          not_false unfolding necessary_falsity by blast
      show ?thesis using not_Ap output_transfer by blast
    next
      case old_fun_prime
      have not_Ap: "\<not> pp_t_holds (A \<acute> ?p) [True]"
        using pp_t_T6_punctured_right_tip_old_fun_prime_fails
        unfolding old_fun_prime .
      show ?thesis using not_Ap output_transfer by blast
    next
      case truth
      have p_false: "\<not> pp_t_holds ?p [True]"
        by (rule pp_t_T6_punctured_right_tip_false_at_tip)
      have Aq_true: "pp_t_holds (A \<acute> q) [True]"
        using pp_t_constant_operator_holds[
          OF q, of True "[True]"]
        unfolding truth by simp
      have p_true: "pp_t_holds ?p [True]"
        using pp_t_prop_eqv_at[
          OF p_Aq, of "[True]"]
          Aq_true by blast
      show ?thesis using p_false p_true by blast
    next
      case negation
      have right_tip_q:
          "pp_t_eqv Prop [True] pp_t_right_tip q"
        unfolding pp_t_eqv.simps
      proof (intro allI impI)
        fix z
        assume future_z: "prefix [True] z"
        have applications:
            "pp_t_holds ?p z =
             pp_t_holds (A \<acute> q) z"
          using pp_t_prop_eqv_at[
            OF p_Aq, of z]
            future_z .
        show "pp_t_holds pp_t_right_tip z =
            pp_t_holds q z"
          using applications
            pp_t_negation_operator_holds[
              OF pp_t_right_tip_in_domain, of z]
            pp_t_negation_operator_holds[OF q, of z]
          unfolding pp_t_T6_punctured_right_tip_def
            negation
          by simp
      qed
      have J_applications:
          "pp_t_eqv Prop [True]
            (pp_t_quantified_fun_prime_operator \<acute>
              pp_t_right_tip)
            (pp_t_quantified_fun_prime_operator \<acute> q)"
        by (rule pp_t_app_respects[
          OF pp_t_eqv_reflexive[
              OF pp_t_quantified_fun_prime_operator_in_domain,
              of "[True]"]
            pp_t_right_tip_in_domain q right_tip_q])
      have J_right_tip:
          "pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute>
              pp_t_right_tip) [True]"
        using pp_t_prop_eqv_at[
          OF J_applications, of "[True]"]
          Jq by blast
      show ?thesis
        using J_right_tip pp_t_right_tip_old_fun_prime_fails
        by blast
    next
      case possibility
      have q_true_at_u: "pp_t_holds q u"
        using pp_t_prop_eqv_at[
          OF true_u, of u] by simp
      have Aq_true: "pp_t_holds (A \<acute> q) [True]"
        using pp_t_possibility_operator_holds[
          OF q, of "[True]"]
          future_u q_true_at_u
        unfolding possibility by blast
      have p_true: "pp_t_holds ?p [True]"
        using pp_t_prop_eqv_at[
          OF p_Aq, of "[True]"]
          Aq_true by blast
      show ?thesis
        using p_true
          pp_t_T6_punctured_right_tip_false_at_tip
        by blast
    next
      case possible_falsity
      have q_false_at_v: "\<not> pp_t_holds q v"
        using pp_t_prop_eqv_at[
          OF false_v, of v] by simp
      have not_true:
          "\<not> pp_t_eqv Prop [True] q (pp_zf_truth True)"
      proof
        assume settled:
            "pp_t_eqv Prop [True] q (pp_zf_truth True)"
        have q_true_at_v: "pp_t_holds q v"
          using pp_t_prop_eqv_at[
            OF settled, of v]
            future_v by simp
        show False using q_false_at_v q_true_at_v by blast
      qed
      have Aq_true: "pp_t_holds (A \<acute> q) [True]"
        using pp_t_possible_falsity_operator_holds[
          OF q, of "[True]"]
          not_true unfolding possible_falsity by blast
      have p_true: "pp_t_holds ?p [True]"
        using pp_t_prop_eqv_at[
          OF p_Aq, of "[True]"]
          Aq_true by blast
      show ?thesis
        using p_true
          pp_t_T6_punctured_right_tip_false_at_tip
        by blast
    qed
  qed
qed

definition pp_t_T6_punctured_right_tip_old_diagonal_reachable ::
    bool where
  "pp_t_T6_punctured_right_tip_old_diagonal_reachable
    \<longleftrightarrow>
    (\<exists>q.
      Elem q (pp_t_domain Prop)
      \<and> pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]
      \<and> pp_t_eqv Prop [True] pp_t_T6_punctured_right_tip
        (pp_t_fun_prime_T6_operator \<acute> q))"

theorem pp_t_T6_punctured_right_tip_old_diagonal_unreachable:
  "\<not> pp_t_T6_punctured_right_tip_old_diagonal_reachable"
proof
  assume reachable:
      "pp_t_T6_punctured_right_tip_old_diagonal_reachable"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]"
    and image:
      "pp_t_eqv Prop [True] pp_t_T6_punctured_right_tip
        (pp_t_fun_prime_T6_operator \<acute> q)"
    using reachable
    unfolding
      pp_t_T6_punctured_right_tip_old_diagonal_reachable_def
    by blast
  have old_Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
    by (rule pp_t_T6_diagonal_new_fun_prime_implies_old[
      OF q new_Jq])
  have old_fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] q"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF q, of "[True]"]
      pp_t_fun_prime_stabilizes[OF q, of "[True]"]
      old_Jq by blast
  obtain u v where future_u: "prefix [True] u"
    and true_u:
      "pp_t_eqv Prop u q (pp_zf_truth True)"
    and "prefix [True] v"
    and "pp_t_eqv Prop v q (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF q old_fun_prime] by blast
  let ?r = "u @ [False]"
  have future_r: "prefix [True] ?r"
    using future_u
    by (auto simp: prefix_def append_assoc)
  have old_D_settled:
      "pp_t_eqv Prop u
        (pp_t_fun_prime_T6_operator \<acute> q)
        (pp_zf_truth False)"
    using pp_t_fun_prime_T6_on_settled[
      OF q true_u pp_t_fun_prime_has_witness_everywhere]
    by simp
  have not_old_D_r:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[
      OF old_D_settled, of ?r]
    by simp
  have p_r:
      "pp_t_holds pp_t_T6_punctured_right_tip ?r"
    by (rule pp_t_T6_punctured_right_tip_true_below[
      OF future_u])
  have image_r:
      "pp_t_holds pp_t_T6_punctured_right_tip ?r =
       pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[OF image, of ?r] future_r .
  show False using p_r not_old_D_r image_r by blast
qed

theorem pp_t_T6_recomputed_diagonal_holds_on_punctured_right_tip:
  "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      pp_t_T6_punctured_right_tip) [True]"
proof -
  let ?p = pp_t_T6_punctured_right_tip
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_T6_punctured_right_tip_in_domain)
  have old_Dp:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> ?p) [True]"
    by (rule pp_t_T6_old_diagonal_holds_on_punctured_right_tip)
  show ?thesis
    unfolding pp_t_eval_T6_diagonal_T6_operator_holds[OF p]
  proof (intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_T6_diagonal_unary_pure [True] X
          \<and> pp_t_holds
            (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]
          \<and> pp_t_eqv Prop [True] ?p (X \<acute> q)"
    have pure_X: "pp_t_T6_diagonal_unary_pure [True] X"
      using antecedent by blast
    have new_Jq:
        "pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> q) [True]"
      using antecedent by blast
    have old_Jq:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
      by (rule pp_t_T6_diagonal_new_fun_prime_implies_old[
        OF q new_Jq])
    have p_Xq: "pp_t_eqv Prop [True] ?p (X \<acute> q)"
      using antecedent by blast
    from pure_X consider
        (old) "pp_t_fun_prime_unary_pure [True] X"
      | (diagonal)
          "pp_t_eqv pp_t_constants_unary_type
            [True] pp_t_fun_prime_T6_operator X"
      unfolding pp_t_T6_diagonal_unary_pure_def
      by blast
    then show "\<not> pp_t_holds (X \<acute> ?p) [True]"
    proof cases
      case old
      show ?thesis
        using pp_t_fun_prime_T6_operator_holds[
            OF p, of "[True]"]
          old_Dp X q old old_Jq p_Xq
        by blast
    next
      case diagonal
      have Dq_Xq:
          "pp_t_eqv Prop [True]
            (pp_t_fun_prime_T6_operator \<acute> q)
            (X \<acute> q)"
        by (rule pp_t_app_respects[
          OF diagonal q q pp_t_eqv_reflexive[OF q]])
      have p_Dq:
          "pp_t_eqv Prop [True] ?p
            (pp_t_fun_prime_T6_operator \<acute> q)"
        using p q X
          pp_t_app_closed[
            OF pp_t_fun_prime_T6_operator_in_domain q]
          pp_t_app_closed[OF X q]
          p_Xq Dq_Xq
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have reachable:
          "pp_t_T6_punctured_right_tip_old_diagonal_reachable"
        unfolding
          pp_t_T6_punctured_right_tip_old_diagonal_reachable_def
        using q new_Jq p_Dq
        by blast
      show ?thesis
        using reachable
          pp_t_T6_punctured_right_tip_old_diagonal_unreachable
        by blast
    qed
  qed
qed

definition pp_t_T6_modal_tip_discriminator_battery :: "ZF set" where
  "pp_t_T6_modal_tip_discriminator_battery = {
    pp_zf_truth True,
    pp_zf_truth False,
    pp_t_right_tip,
    pp_t_T6_punctured_right_tip}"

theorem pp_t_T6_modal_tip_discriminator_values:
  "\<not> pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth True)
      [True]"
  "\<not> pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth True)
      [True]"
  "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth False)
      [True]"
  "pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth False)
      [True]"
  "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute> pp_t_right_tip)
      [True]"
  "pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> pp_t_right_tip)
      [True]"
  "pp_t_holds
    (pp_t_T6_diagonal_T6_operator \<acute>
      pp_t_T6_punctured_right_tip) [True]"
  "pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_T6_punctured_right_tip) [True]"
proof -
  have top:
      "pp_t_eqv Prop [True]
        (pp_zf_truth True) (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF pp_t_truth_in_domain])
  have bottom:
      "pp_t_eqv Prop [True]
        (pp_zf_truth False) (pp_zf_truth False)"
    by (rule pp_t_eqv_reflexive[OF pp_t_truth_in_domain])
  have new_top:
      "pp_t_eqv Prop [True]
        (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth True)
        (pp_zf_truth False)"
    using pp_t_T6_recomputed_diagonal_on_settled_unconditional[
      OF pp_t_truth_in_domain top]
    by simp
  have old_top:
      "pp_t_eqv Prop [True]
        (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth True)
        (pp_zf_truth False)"
    using pp_t_fun_prime_T6_on_settled[
      OF pp_t_truth_in_domain top
        pp_t_fun_prime_has_witness_everywhere]
    by simp
  have new_bottom:
      "pp_t_eqv Prop [True]
        (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth False)
        (pp_zf_truth True)"
    using pp_t_T6_recomputed_diagonal_on_settled_unconditional[
      OF pp_t_truth_in_domain bottom]
    by simp
  have old_bottom:
      "pp_t_eqv Prop [True]
        (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth False)
        (pp_zf_truth True)"
    using pp_t_fun_prime_T6_on_settled[
      OF pp_t_truth_in_domain bottom
        pp_t_fun_prime_has_witness_everywhere]
    by simp
  show "\<not> pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth True)
        [True]"
    using pp_t_prop_eqv_at[OF new_top, of "[True]"]
    by simp
  show "\<not> pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth True)
        [True]"
    using pp_t_prop_eqv_at[OF old_top, of "[True]"]
    by simp
  show "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> pp_zf_truth False)
        [True]"
    using pp_t_prop_eqv_at[OF new_bottom, of "[True]"]
    by simp
  show "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth False)
        [True]"
    using pp_t_prop_eqv_at[OF old_bottom, of "[True]"]
    by simp
  show "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> pp_t_right_tip)
        [True]"
    by (rule pp_t_T6_recomputed_right_tip_holds)
  show "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> pp_t_right_tip)
        [True]"
    by (rule pp_t_right_tip_T6_holds)
  show "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute>
        pp_t_T6_punctured_right_tip) [True]"
    by (rule
      pp_t_T6_recomputed_diagonal_holds_on_punctured_right_tip)
  show "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute>
        pp_t_T6_punctured_right_tip) [True]"
    by (rule pp_t_T6_old_diagonal_holds_on_punctured_right_tip)
qed

corollary pp_t_T6_modal_tip_discriminator_battery_agrees:
  assumes "p \<in> pp_t_T6_modal_tip_discriminator_battery"
  shows "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> p) [True]
    =
    pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> p) [True]"
  using assms pp_t_T6_modal_tip_discriminator_values
  unfolding pp_t_T6_modal_tip_discriminator_battery_def
  by auto

definition pp_t_T6_negated_old_diagonal :: "ZF \<Rightarrow> ZF" where
  "pp_t_T6_negated_old_diagonal p =
    pp_t_negation_operator \<acute>
      (pp_t_fun_prime_T6_operator \<acute> p)"

lemma pp_t_T6_negated_old_diagonal_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_T6_negated_old_diagonal p)
    (pp_t_domain Prop)"
  unfolding pp_t_T6_negated_old_diagonal_def
  by (rule pp_t_app_closed[
    OF pp_t_negation_operator_in_domain
      pp_t_app_closed[
        OF pp_t_fun_prime_T6_operator_in_domain p]])

lemma pp_t_T6_negated_old_diagonal_on_truth:
  "pp_t_eqv Prop w
    (pp_t_T6_negated_old_diagonal (pp_zf_truth b))
    (pp_zf_truth b)"
proof -
  have truth: "Elem (pp_zf_truth b) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have settled:
      "pp_t_eqv Prop w (pp_zf_truth b) (pp_zf_truth b)"
    by (rule pp_t_eqv_reflexive[OF truth])
  have D_settled:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth b)
        (pp_zf_truth (\<not> b))"
    by (rule pp_t_fun_prime_T6_on_settled[
      OF truth settled pp_t_fun_prime_has_witness_everywhere])
  have D_domain:
      "Elem
        (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth b)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain truth])
  show ?thesis
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have D_value:
        "pp_t_holds
          (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth b) v
        = (\<not> b)"
      using pp_t_prop_eqv_at[
        OF D_settled, of v]
        future by simp
    show "pp_t_holds
        (pp_t_T6_negated_old_diagonal (pp_zf_truth b)) v
      =
      pp_t_holds (pp_zf_truth b) v"
      unfolding pp_t_T6_negated_old_diagonal_def
      using pp_t_negation_operator_holds[
        OF D_domain, of v]
        D_value by simp
  qed
qed

lemma pp_t_T6_negated_old_diagonal_recurrent_values:
  "pp_t_holds
    (pp_t_T6_negated_old_diagonal pp_t_recurrent_fun_prime) []"
  "\<not> pp_t_holds
    (pp_t_T6_negated_old_diagonal pp_t_recurrent_fun_prime)
      [False]"
proof -
  have p: "Elem pp_t_recurrent_fun_prime (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have D_domain:
      "Elem
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain p])
  have not_D_root:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_recurrent_T6_false_on_spine[of 0]
    by simp
  show "pp_t_holds
      (pp_t_T6_negated_old_diagonal
        pp_t_recurrent_fun_prime) []"
    unfolding pp_t_T6_negated_old_diagonal_def
    using pp_t_negation_operator_holds[
      OF D_domain, of "[]"]
      not_D_root by simp
  have settled:
      "pp_t_eqv Prop [False] pp_t_recurrent_fun_prime
        (pp_zf_truth False)"
    using pp_t_recurrent_fun_prime_off_spine_settled[
      of 0 "[]"]
    by simp
  have D_settled:
      "pp_t_eqv Prop [False]
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime)
        (pp_zf_truth True)"
    using pp_t_fun_prime_T6_on_settled[
      OF p settled pp_t_fun_prime_has_witness_everywhere]
    by simp
  have D_left:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) [False]"
    using pp_t_prop_eqv_at[
      OF D_settled, of "[False]"] by simp
  show "\<not> pp_t_holds
      (pp_t_T6_negated_old_diagonal
        pp_t_recurrent_fun_prime) [False]"
    unfolding pp_t_T6_negated_old_diagonal_def
    using pp_t_negation_operator_holds[
      OF D_domain, of "[False]"]
      D_left by simp
qed

lemma pp_t_T6_negated_old_diagonal_punctured_values:
  "\<not> pp_t_holds
    (pp_t_T6_negated_old_diagonal
      pp_t_T6_punctured_right_tip) [True]"
  "pp_t_holds
    (pp_t_T6_negated_old_diagonal
      pp_t_T6_punctured_right_tip) [True, False]"
proof -
  have p:
      "Elem pp_t_T6_punctured_right_tip (pp_t_domain Prop)"
    by (rule pp_t_T6_punctured_right_tip_in_domain)
  have D_domain:
      "Elem
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_T6_punctured_right_tip)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain p])
  show "\<not> pp_t_holds
      (pp_t_T6_negated_old_diagonal
        pp_t_T6_punctured_right_tip) [True]"
    unfolding pp_t_T6_negated_old_diagonal_def
    using pp_t_negation_operator_holds[
        OF D_domain, of "[True]"]
      pp_t_T6_old_diagonal_holds_on_punctured_right_tip
    by simp
  have D_settled:
      "pp_t_eqv Prop [True, False]
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_T6_punctured_right_tip)
        (pp_zf_truth False)"
    using pp_t_fun_prime_T6_on_settled[
      OF p pp_t_T6_punctured_right_tip_settled_below
        pp_t_fun_prime_has_witness_everywhere]
    by simp
  have not_D_child:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_T6_punctured_right_tip) [True, False]"
    using pp_t_prop_eqv_at[
      OF D_settled, of "[True, False]"]
    by simp
  show "pp_t_holds
      (pp_t_T6_negated_old_diagonal
        pp_t_T6_punctured_right_tip) [True, False]"
    unfolding pp_t_T6_negated_old_diagonal_def
    using pp_t_negation_operator_holds[
      OF D_domain, of "[True, False]"]
      not_D_child by simp
qed

definition pp_t_T6_negated_diagonal_transform_signature ::
    "ZF \<Rightarrow> bool list" where
  "pp_t_T6_negated_diagonal_transform_signature A = [
    pp_t_holds
      (A \<acute>
        pp_t_T6_negated_old_diagonal (pp_zf_truth True)) [],
    pp_t_holds
      (A \<acute>
        pp_t_T6_negated_old_diagonal (pp_zf_truth False)) [],
    pp_t_holds
      (A \<acute>
        pp_t_T6_negated_old_diagonal
          pp_t_recurrent_fun_prime) [],
    pp_t_holds
      (A \<acute>
        pp_t_T6_negated_old_diagonal
          pp_t_T6_punctured_right_tip) [True]]"

lemma pp_t_T6_negated_diagonal_transform_signatures:
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_identity_operator =
    [True, False, True, False]"
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_negation_operator =
    [False, True, False, True]"
  "pp_t_T6_negated_diagonal_transform_signature
      (pp_t_constant_operator True) =
    [True, True, True, True]"
  "pp_t_T6_negated_diagonal_transform_signature
      (pp_t_constant_operator False) =
    [False, False, False, False]"
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_necessity_operator =
    [True, False, False, False]"
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_possibility_operator =
    [True, False, True, True]"
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_necessary_falsity_operator =
    [False, True, False, False]"
  "pp_t_T6_negated_diagonal_transform_signature
      pp_t_possible_falsity_operator =
    [False, True, True, True]"
proof -
  let ?hT =
    "pp_t_T6_negated_old_diagonal (pp_zf_truth True)"
  let ?hF =
    "pp_t_T6_negated_old_diagonal (pp_zf_truth False)"
  let ?hR =
    "pp_t_T6_negated_old_diagonal pp_t_recurrent_fun_prime"
  let ?hP =
    "pp_t_T6_negated_old_diagonal
      pp_t_T6_punctured_right_tip"
  have hT: "Elem ?hT (pp_t_domain Prop)"
    by (rule pp_t_T6_negated_old_diagonal_in_domain[
      OF pp_t_truth_in_domain])
  have hF: "Elem ?hF (pp_t_domain Prop)"
    by (rule pp_t_T6_negated_old_diagonal_in_domain[
      OF pp_t_truth_in_domain])
  have hR: "Elem ?hR (pp_t_domain Prop)"
    by (rule pp_t_T6_negated_old_diagonal_in_domain[
      OF pp_t_recurrent_fun_prime_in_domain])
  have hP: "Elem ?hP (pp_t_domain Prop)"
    by (rule pp_t_T6_negated_old_diagonal_in_domain[
      OF pp_t_T6_punctured_right_tip_in_domain])
  have hT_settled:
      "pp_t_eqv Prop [] ?hT (pp_zf_truth True)"
    by (rule pp_t_T6_negated_old_diagonal_on_truth)
  have hF_settled:
      "pp_t_eqv Prop [] ?hF (pp_zf_truth False)"
    by (rule pp_t_T6_negated_old_diagonal_on_truth)
  have hT_root: "pp_t_holds ?hT []"
    using pp_t_prop_eqv_at[
      OF hT_settled, of "[]"] by simp
  have not_hF_root: "\<not> pp_t_holds ?hF []"
    using pp_t_prop_eqv_at[
      OF hF_settled, of "[]"] by simp
  note recurrent =
    pp_t_T6_negated_old_diagonal_recurrent_values
  note punctured =
    pp_t_T6_negated_old_diagonal_punctured_values
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_identity_operator =
      [True, False, True, False]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using hT hF hR hP hT_root not_hF_root
      recurrent punctured
    by (simp add: pp_t_identity_operator_def Lambda_app)
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_negation_operator =
      [False, True, False, True]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using pp_t_negation_operator_holds[OF hT]
      pp_t_negation_operator_holds[OF hF]
      pp_t_negation_operator_holds[OF hR]
      pp_t_negation_operator_holds[OF hP]
      hT_root not_hF_root recurrent punctured
    by simp
  show "pp_t_T6_negated_diagonal_transform_signature
      (pp_t_constant_operator True) =
      [True, True, True, True]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using pp_t_constant_operator_holds[OF hT, of True]
      pp_t_constant_operator_holds[OF hF, of True]
      pp_t_constant_operator_holds[OF hR, of True]
      pp_t_constant_operator_holds[OF hP, of True]
    by simp
  show "pp_t_T6_negated_diagonal_transform_signature
      (pp_t_constant_operator False) =
      [False, False, False, False]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using pp_t_constant_operator_holds[OF hT, of False]
      pp_t_constant_operator_holds[OF hF, of False]
      pp_t_constant_operator_holds[OF hR, of False]
      pp_t_constant_operator_holds[OF hP, of False]
    by simp
  have not_hR_true:
      "\<not> pp_t_eqv Prop [] ?hR (pp_zf_truth True)"
  proof
    assume settled:
        "pp_t_eqv Prop [] ?hR (pp_zf_truth True)"
    have left_true: "pp_t_holds ?hR [False]"
      using pp_t_prop_eqv_at[
        OF settled, of "[False]"] by simp
    show False using left_true recurrent by blast
  qed
  have not_hR_false:
      "\<not> pp_t_eqv Prop [] ?hR (pp_zf_truth False)"
  proof
    assume settled:
        "pp_t_eqv Prop [] ?hR (pp_zf_truth False)"
    have root_false: "\<not> pp_t_holds ?hR []"
      using pp_t_prop_eqv_at[
        OF settled, of "[]"] by simp
    show False using root_false recurrent by blast
  qed
  have not_hP_true:
      "\<not> pp_t_eqv Prop [True] ?hP (pp_zf_truth True)"
  proof
    assume settled:
        "pp_t_eqv Prop [True] ?hP (pp_zf_truth True)"
    have root_true: "pp_t_holds ?hP [True]"
      using pp_t_prop_eqv_at[
        OF settled, of "[True]"] by simp
    show False using root_true punctured by blast
  qed
  have not_hP_false:
      "\<not> pp_t_eqv Prop [True] ?hP (pp_zf_truth False)"
  proof
    assume settled:
        "pp_t_eqv Prop [True] ?hP (pp_zf_truth False)"
    have child_false: "\<not> pp_t_holds ?hP [True, False]"
      using pp_t_prop_eqv_at[
        OF settled, of "[True, False]"] by simp
    show False using child_false punctured by blast
  qed
  have necessity_hT:
      "pp_t_holds (pp_t_necessity_operator \<acute> ?hT) []"
    using pp_t_necessity_operator_holds[OF hT, of "[]"]
      hT_settled by blast
  have not_necessity_hF:
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> ?hF) []"
    using pp_t_necessity_operator_holds[OF hF, of "[]"]
      hF_settled by simp
  have not_necessity_hR:
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> ?hR) []"
    using pp_t_necessity_operator_holds[OF hR, of "[]"]
      not_hR_true by blast
  have not_necessity_hP:
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> ?hP) [True]"
    using pp_t_necessity_operator_holds[OF hP, of "[True]"]
      not_hP_true by blast
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_necessity_operator =
      [True, False, False, False]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using necessity_hT not_necessity_hF
      not_necessity_hR not_necessity_hP
    by simp
  have possibility_hT:
      "pp_t_holds (pp_t_possibility_operator \<acute> ?hT) []"
    unfolding pp_t_possibility_operator_holds[OF hT]
    using hT_root by blast
  have not_possibility_hF:
      "\<not> pp_t_holds
        (pp_t_possibility_operator \<acute> ?hF) []"
    using pp_t_settled_operator_values(2)[
      OF hF hF_settled] by simp
  have possibility_hR:
      "pp_t_holds (pp_t_possibility_operator \<acute> ?hR) []"
    unfolding pp_t_possibility_operator_holds[OF hR]
    using recurrent by blast
  have possibility_hP:
      "pp_t_holds
        (pp_t_possibility_operator \<acute> ?hP) [True]"
    unfolding pp_t_possibility_operator_holds[OF hP]
    using punctured by (intro exI[of _ "[True, False]"]) simp
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_possibility_operator =
      [True, False, True, True]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using possibility_hT not_possibility_hF
      possibility_hR possibility_hP
    by simp
  have not_NF_hT:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?hT) []"
    using pp_t_necessary_falsity_operator_holds[
        OF hT, of "[]"]
      hT_settled by simp
  have NF_hF:
      "pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?hF) []"
    using pp_t_necessary_falsity_operator_holds[
        OF hF, of "[]"]
      hF_settled by blast
  have not_NF_hR:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?hR) []"
    using pp_t_necessary_falsity_operator_holds[
        OF hR, of "[]"]
      not_hR_false by blast
  have not_NF_hP:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?hP) [True]"
    using pp_t_necessary_falsity_operator_holds[
        OF hP, of "[True]"]
      not_hP_false by blast
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_necessary_falsity_operator =
      [False, True, False, False]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using not_NF_hT NF_hF not_NF_hR not_NF_hP
    by simp
  have not_PF_hT:
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?hT) []"
    using pp_t_possible_falsity_operator_holds[
        OF hT, of "[]"]
      hT_settled by simp
  have PF_hF:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?hF) []"
    using pp_t_possible_falsity_operator_holds[
        OF hF, of "[]"]
      hF_settled by simp
  have PF_hR:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?hR) []"
    using pp_t_possible_falsity_operator_holds[
        OF hR, of "[]"]
      not_hR_true by blast
  have PF_hP:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?hP) [True]"
    using pp_t_possible_falsity_operator_holds[
        OF hP, of "[True]"]
      not_hP_true by blast
  show "pp_t_T6_negated_diagonal_transform_signature
      pp_t_possible_falsity_operator =
      [False, True, True, True]"
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using not_PF_hT PF_hF PF_hR PF_hP
    by simp
qed

lemma pp_t_T6_negated_diagonal_transform_point_agreement:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and operators:
      "pp_b_T6_negated_diagonal_then A =
        pp_b_T6_negated_diagonal_then B"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (A \<acute> pp_t_T6_negated_old_diagonal p) v
    =
    pp_t_holds
      (B \<acute> pp_t_T6_negated_old_diagonal p) v"
proof -
  have applications:
      "pp_b_T6_negated_diagonal_then A (pp_b_of_zf p) =
       pp_b_T6_negated_diagonal_then B (pp_b_of_zf p)"
    by (rule fun_cong[OF operators])
  have A_application:
      "pp_b_T6_negated_diagonal_then A (pp_b_of_zf p) =
       pp_b_of_zf
        (A \<acute> pp_t_T6_negated_old_diagonal p)"
    using pp_b_T6_negated_diagonal_then_application[OF A p]
    unfolding pp_t_T6_negated_old_diagonal_def .
  have B_application:
      "pp_b_T6_negated_diagonal_then B (pp_b_of_zf p) =
       pp_b_of_zf
        (B \<acute> pp_t_T6_negated_old_diagonal p)"
    using pp_b_T6_negated_diagonal_then_application[OF B p]
    unfolding pp_t_T6_negated_old_diagonal_def .
  show ?thesis
    using applications A_application B_application
    unfolding pp_b_of_zf_def
    by auto
qed

lemma pp_t_T6_negated_diagonal_transform_signature_agreement:
  assumes A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and operators:
      "pp_b_T6_negated_diagonal_then A =
        pp_b_T6_negated_diagonal_then B"
  shows "pp_t_T6_negated_diagonal_transform_signature A =
    pp_t_T6_negated_diagonal_transform_signature B"
proof -
  have hT:
      "pp_t_holds
        (A \<acute>
          pp_t_T6_negated_old_diagonal (pp_zf_truth True)) []
      =
      pp_t_holds
        (B \<acute>
          pp_t_T6_negated_old_diagonal (pp_zf_truth True)) []"
    by (rule pp_t_T6_negated_diagonal_transform_point_agreement[
      OF A B operators pp_t_truth_in_domain])
  have hF:
      "pp_t_holds
        (A \<acute>
          pp_t_T6_negated_old_diagonal (pp_zf_truth False)) []
      =
      pp_t_holds
        (B \<acute>
          pp_t_T6_negated_old_diagonal (pp_zf_truth False)) []"
    by (rule pp_t_T6_negated_diagonal_transform_point_agreement[
      OF A B operators pp_t_truth_in_domain])
  have hR:
      "pp_t_holds
        (A \<acute>
          pp_t_T6_negated_old_diagonal
            pp_t_recurrent_fun_prime) []
      =
      pp_t_holds
        (B \<acute>
          pp_t_T6_negated_old_diagonal
            pp_t_recurrent_fun_prime) []"
    by (rule pp_t_T6_negated_diagonal_transform_point_agreement[
      OF A B operators pp_t_recurrent_fun_prime_in_domain])
  have hP:
      "pp_t_holds
        (A \<acute>
          pp_t_T6_negated_old_diagonal
            pp_t_T6_punctured_right_tip) [True]
      =
      pp_t_holds
        (B \<acute>
          pp_t_T6_negated_old_diagonal
            pp_t_T6_punctured_right_tip) [True]"
    by (rule pp_t_T6_negated_diagonal_transform_point_agreement[
      OF A B operators pp_t_T6_punctured_right_tip_in_domain])
  show ?thesis
    unfolding pp_t_T6_negated_diagonal_transform_signature_def
    using hT hF hR hP
    by simp
qed

theorem pp_t_T6_negated_diagonal_transforms_injective:
  "pp_t_T6_negated_diagonal_transforms_injective"
  unfolding pp_t_T6_negated_diagonal_transforms_injective_def
proof (intro ballI impI)
  fix A B
  assume A:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and B:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and operators:
      "pp_b_T6_negated_diagonal_then A =
        pp_b_T6_negated_diagonal_then B"
  have signatures:
      "pp_t_T6_negated_diagonal_transform_signature A =
       pp_t_T6_negated_diagonal_transform_signature B"
    by (rule
      pp_t_T6_negated_diagonal_transform_signature_agreement[
        OF A B operators])
  show "A = B"
    using A B signatures
      pp_t_T6_negated_diagonal_transform_signatures
    unfolding pp_t_fun_prime_probe_representatives_def
    by auto
qed

lemma pp_t_T6_joint_generic_boolean_separator:
  assumes injective:
      "pp_t_T6_negated_diagonal_transforms_injective"
  shows "\<exists>R.
    [] \<in> R
    \<and>
    (\<forall>A \<in> pp_t_T6_ten_representatives.
      \<forall>B \<in> pp_t_T6_ten_representatives.
        (pp_b_operator_of A R = pp_b_operator_of B R
          \<longleftrightarrow> A = B))
    \<and>
    (\<forall>A \<in> pp_t_fun_prime_probe_representatives.
      \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        (pp_b_T6_negated_diagonal_then A R =
          pp_b_T6_negated_diagonal_then B R
          \<longleftrightarrow> A = B))"
proof -
  let ?Current =
    "pp_b_operator_of ` pp_t_T6_ten_representatives"
  let ?Transformed =
    "pp_b_T6_negated_diagonal_then `
      pp_t_fun_prime_probe_representatives"
  let ?Stock = "?Current \<union> ?Transformed"
  have countable: "countable ?Stock"
    unfolding pp_t_T6_ten_representatives_def
      pp_t_fun_prime_probe_representatives_def
    by simp
  have stock_equivariant:
      "\<And>F. F \<in> ?Stock \<Longrightarrow> pp_b_equivariant F"
  proof -
    fix F
    assume "F \<in> ?Stock"
    then consider
        (current) A where
          "A \<in> pp_t_T6_ten_representatives"
          "F = pp_b_operator_of A"
      | (transformed) A where
          "A \<in> pp_t_fun_prime_probe_representatives"
          "F = pp_b_T6_negated_diagonal_then A"
      by blast
    then show "pp_b_equivariant F"
    proof cases
      case current
      show ?thesis
        using pp_t_T6_ten_representatives_equivariant
          current
        unfolding pp_t_T6_ten_representatives_equivariant_def
        by blast
    next
      case transformed
      show ?thesis
        unfolding transformed(2)
        by (rule
          pp_b_T6_negated_diagonal_then_equivariant[
            OF transformed(1)])
    qed
  qed
  obtain R where root: "[] \<in> R"
    and separator:
      "\<forall>F \<in> ?Stock. \<forall>G \<in> ?Stock.
        (F R = G R \<longleftrightarrow> F = G)"
    using pp_b_generic_separator_for_countable_stock_with_root[
      OF countable stock_equivariant, where b=True]
    by auto
  have current:
      "A \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       B \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       (pp_b_operator_of A R = pp_b_operator_of B R
        \<longleftrightarrow> A = B)"
    for A B
  proof
    assume A:
        "A \<in> pp_t_T6_ten_representatives"
      and B:
        "B \<in> pp_t_T6_ten_representatives"
      and outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
    have operators:
        "pp_b_operator_of A = pp_b_operator_of B"
      using separator A B outputs by blast
    show "A = B"
      by (rule pp_b_operator_of_injective_on_unary_domain[
        OF pp_t_T6_ten_representative_in_domain[OF A]
          pp_t_T6_ten_representative_in_domain[OF B]
          operators])
  next
    assume "A \<in> pp_t_T6_ten_representatives"
      and "B \<in> pp_t_T6_ten_representatives"
      and "A = B"
    then show
        "pp_b_operator_of A R = pp_b_operator_of B R"
      by simp
  qed
  have transformed:
      "A \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
       B \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
       (pp_b_T6_negated_diagonal_then A R =
        pp_b_T6_negated_diagonal_then B R
        \<longleftrightarrow> A = B)"
    for A B
  proof
    assume A:
        "A \<in> pp_t_fun_prime_probe_representatives"
      and B:
        "B \<in> pp_t_fun_prime_probe_representatives"
      and outputs:
        "pp_b_T6_negated_diagonal_then A R =
         pp_b_T6_negated_diagonal_then B R"
    have operators:
        "pp_b_T6_negated_diagonal_then A =
         pp_b_T6_negated_diagonal_then B"
      using separator A B outputs by blast
    show "A = B"
      using injective A B operators
      unfolding
        pp_t_T6_negated_diagonal_transforms_injective_def
      by blast
  next
    assume "A \<in> pp_t_fun_prime_probe_representatives"
      and "B \<in> pp_t_fun_prime_probe_representatives"
      and "A = B"
    then show
        "pp_b_T6_negated_diagonal_then A R =
         pp_b_T6_negated_diagonal_then B R"
      by simp
  qed
  show ?thesis
    using root current transformed by blast
qed

theorem pp_t_T6_joint_fun_prime_witness_if_transforms_injective:
  assumes injective:
      "pp_t_T6_negated_diagonal_transforms_injective"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds q w
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute>
        (pp_t_negation_operator \<acute>
          (pp_t_fun_prime_T6_operator \<acute> q))) w"
proof -
  obtain R where root: "[] \<in> R"
    and current:
      "\<forall>A \<in> pp_t_T6_ten_representatives.
       \<forall>B \<in> pp_t_T6_ten_representatives.
        (pp_b_operator_of A R = pp_b_operator_of B R
          \<longleftrightarrow> A = B)"
    and transformed:
      "\<forall>A \<in> pp_t_fun_prime_probe_representatives.
       \<forall>B \<in> pp_t_fun_prime_probe_representatives.
        (pp_b_T6_negated_diagonal_then A R =
          pp_b_T6_negated_diagonal_then B R
          \<longleftrightarrow> A = B)"
    using pp_t_T6_joint_generic_boolean_separator[
      OF injective]
    by blast
  let ?P = "pp_b_lift w R"
  let ?q = "pp_zf_of_b ?P"
  let ?s =
    "pp_t_negation_operator \<acute>
      (pp_t_fun_prime_T6_operator \<acute> ?q)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have q_true: "pp_t_holds ?q w"
    using root pp_b_view_membership_root[
      of w ?P]
    by simp
  have current_separated:
      "A \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       B \<in> pp_t_T6_ten_representatives \<Longrightarrow>
       pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)
       \<Longrightarrow> A = B"
    for A B
  proof -
    assume A:
        "A \<in> pp_t_T6_ten_representatives"
      and B:
        "B \<in> pp_t_T6_ten_representatives"
      and agreement:
        "pp_t_eqv Prop w (A \<acute> ?q) (B \<acute> ?q)"
    have view_outputs:
        "pp_b_view w
            (pp_b_operator_of A ?P)
        =
         pp_b_view w
            (pp_b_operator_of B ?P)"
      using agreement
      unfolding pp_t_eqv.simps pp_b_view_def
        pp_b_operator_of_def pp_b_of_zf_def
      by auto
    have A_equivariant:
        "pp_b_equivariant (pp_b_operator_of A)"
      using pp_t_T6_ten_representatives_equivariant A
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have B_equivariant:
        "pp_b_equivariant (pp_b_operator_of B)"
      using pp_t_T6_ten_representatives_equivariant B
      unfolding pp_t_T6_ten_representatives_equivariant_def
      by blast
    have outputs:
        "pp_b_operator_of A R = pp_b_operator_of B R"
      using view_outputs A_equivariant B_equivariant
      unfolding pp_b_equivariant_def
      by simp
    show "A = B"
      using current A B outputs by blast
  qed
  have new_predicate:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w ?q"
    by (rule pp_t_T6_ten_separated_implies_fun_prime[
      OF q current_separated])
  have new_Jq:
      "pp_t_holds
        (pp_t_T6_diagonal_fun_prime_operator \<acute> ?q) w"
    using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
      OF q, of w]
      new_predicate by blast
  have Dq:
      "Elem (pp_t_fun_prime_T6_operator \<acute> ?q)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_fun_prime_T6_operator_in_domain q])
  have s: "Elem ?s (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain Dq])
  have transformed_separated:
      "A \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
       B \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
       pp_t_eqv Prop w (A \<acute> ?s) (B \<acute> ?s)
       \<Longrightarrow> A = B"
    for A B
  proof -
    assume A:
        "A \<in> pp_t_fun_prime_probe_representatives"
      and B:
        "B \<in> pp_t_fun_prime_probe_representatives"
      and agreement:
        "pp_t_eqv Prop w (A \<acute> ?s) (B \<acute> ?s)"
    have A_application:
        "pp_b_T6_negated_diagonal_then A ?P =
         pp_b_of_zf (A \<acute> ?s)"
      using pp_b_T6_negated_diagonal_then_application[
        OF A q]
      by simp
    have B_application:
        "pp_b_T6_negated_diagonal_then B ?P =
         pp_b_of_zf (B \<acute> ?s)"
      using pp_b_T6_negated_diagonal_then_application[
        OF B q]
      by simp
    have application_views:
        "pp_b_view w (pp_b_of_zf (A \<acute> ?s)) =
         pp_b_view w (pp_b_of_zf (B \<acute> ?s))"
      using pp_t_eqv_Prop_iff_boolean_views[
        OF pp_t_app_closed[
            OF pp_t_fun_prime_probe_representative_in_domain[
              OF A] s]
          pp_t_app_closed[
            OF pp_t_fun_prime_probe_representative_in_domain[
              OF B] s],
        of w]
        agreement
      by blast
    have view_outputs:
        "pp_b_view w
            (pp_b_T6_negated_diagonal_then A ?P)
        =
         pp_b_view w
            (pp_b_T6_negated_diagonal_then B ?P)"
      using application_views A_application B_application
      by simp
    have A_equivariant:
        "pp_b_equivariant
          (pp_b_T6_negated_diagonal_then A)"
      by (rule pp_b_T6_negated_diagonal_then_equivariant[
        OF A])
    have B_equivariant:
        "pp_b_equivariant
          (pp_b_T6_negated_diagonal_then B)"
      by (rule pp_b_T6_negated_diagonal_then_equivariant[
        OF B])
    have outputs:
        "pp_b_T6_negated_diagonal_then A R =
         pp_b_T6_negated_diagonal_then B R"
      using view_outputs A_equivariant B_equivariant
      unfolding pp_b_equivariant_def
      by simp
    show "A = B"
      using transformed A B outputs by blast
  qed
  have old_predicate:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w ?s"
    by (rule
      pp_t_representatives_separated_implies_base_fun_prime[
        OF s transformed_separated])
  have old_Js:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> ?s) w"
    using pp_t_quantified_fun_prime_operator_holds[
      OF s, of w]
      old_predicate by blast
  show ?thesis
    using q q_true new_Jq old_Js by blast
qed

theorem pp_t_T6_joint_fun_prime_witness:
  "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> pp_t_holds q w
    \<and> pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
    \<and> pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute>
        (pp_t_negation_operator \<acute>
          (pp_t_fun_prime_T6_operator \<acute> q))) w"
  by (rule
      pp_t_T6_joint_fun_prime_witness_if_transforms_injective[
        OF pp_t_T6_negated_diagonal_transforms_injective])

lemma pp_t_T6_global_necessary_falsity_collision_implies_reachable:
  assumes collision:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator"
  shows "pp_t_T6_right_tip_old_diagonal_reachable"
proof (rule ccontr)
  assume unreachable:
      "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
  have recomputed:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute>
          pp_t_right_tip) [True]"
    using pp_t_T6_recomputed_right_tip_iff_unreachable
      unreachable by blast
  have not_NF:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute>
          pp_t_right_tip) [True]"
    by (rule pp_t_right_tip_necessary_falsity_fails)
  show False using recomputed not_NF collision by simp
qed

lemma pp_t_T6_global_old_diagonal_collision_implies_unreachable:
  assumes collision:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  shows "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
proof -
  have recomputed:
      "pp_t_holds
        (pp_t_T6_diagonal_T6_operator \<acute>
          pp_t_right_tip) [True]"
    using pp_t_right_tip_T6_holds collision by simp
  show ?thesis
    using pp_t_T6_recomputed_right_tip_iff_unreachable
      recomputed by blast
qed

theorem pp_t_T6_absorption_selects_collision_by_reachability:
  assumes absorbed: "pp_t_T6_recomputed_diagonal_absorbed"
  shows
    "pp_t_T6_right_tip_old_diagonal_reachable
      \<longleftrightarrow>
      pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator"
    "\<not> pp_t_T6_right_tip_old_diagonal_reachable
      \<longleftrightarrow>
      pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
proof -
  have collision:
      "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator
      \<or>
      pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    using absorbed
    unfolding
      pp_t_T6_recomputed_diagonal_absorbed_iff_global_collision
    by blast
  show "pp_t_T6_right_tip_old_diagonal_reachable
      \<longleftrightarrow>
      pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator"
  proof
    assume reachable:
        "pp_t_T6_right_tip_old_diagonal_reachable"
    show "pp_t_T6_diagonal_T6_operator =
        pp_t_necessary_falsity_operator"
    proof (rule ccontr)
      assume not_NF:
          "pp_t_T6_diagonal_T6_operator \<noteq>
            pp_t_necessary_falsity_operator"
      have old_D:
          "pp_t_T6_diagonal_T6_operator =
            pp_t_fun_prime_T6_operator"
        using collision not_NF by blast
      show False
        using reachable
          pp_t_T6_global_old_diagonal_collision_implies_unreachable[
            OF old_D]
        by blast
    qed
  next
    assume NF:
        "pp_t_T6_diagonal_T6_operator =
          pp_t_necessary_falsity_operator"
    show "pp_t_T6_right_tip_old_diagonal_reachable"
      by (rule
        pp_t_T6_global_necessary_falsity_collision_implies_reachable[
          OF NF])
  qed
  show "\<not> pp_t_T6_right_tip_old_diagonal_reachable
      \<longleftrightarrow>
      pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
  proof
    assume unreachable:
        "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
    show "pp_t_T6_diagonal_T6_operator =
        pp_t_fun_prime_T6_operator"
    proof (rule ccontr)
      assume not_old_D:
          "pp_t_T6_diagonal_T6_operator \<noteq>
            pp_t_fun_prime_T6_operator"
      have NF:
          "pp_t_T6_diagonal_T6_operator =
            pp_t_necessary_falsity_operator"
        using collision not_old_D by blast
      show False
        using unreachable
          pp_t_T6_global_necessary_falsity_collision_implies_reachable[
            OF NF]
        by blast
    qed
  next
    assume old_D:
        "pp_t_T6_diagonal_T6_operator =
          pp_t_fun_prime_T6_operator"
    show "\<not> pp_t_T6_right_tip_old_diagonal_reachable"
      by (rule
        pp_t_T6_global_old_diagonal_collision_implies_unreachable[
          OF old_D])
  qed
qed

text \<open>
  The prescribed-value separation theorem supplies both true and false
  \<open>fun\<acute>\<close> propositions for the enlarged ten-class stock.  It follows
  that the recomputed T6 operator is equivalent to none of identity,
  negation, constant truth, constant falsity, necessity, possibility,
  necessary falsity, possible falsity, or the old \<open>fun\<acute>\<close> operator.
  Hence application closure for the logical T6 builder is equivalent to the
  single global equality between the recomputed and old T6 operators.

  That equality has a strong necessary consequence.  At every world there
  must be two distinct propositions \<open>q\<close> and \<open>r\<close>, with \<open>q\<close>
  \<open>fun\<acute>\<close> for the enlarged stock and \<open>r\<close> \<open>fun\<acute>\<close> for the old
  stock, such that the old T6 operator applied to \<open>q\<close> is equivalent to
  the negation of \<open>r\<close>.  Moreover, every future cone on which \<open>q\<close> is
  uniformly true or uniformly false is a cone on which \<open>r\<close> has the same
  uniform value.  Constructing such pairs uniformly, or proving that one
  cannot exist, is the remaining semantic test for this first
  classifier-bearing cyclic package.
\<close>

end
