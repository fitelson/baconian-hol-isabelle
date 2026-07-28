theory Bacon_PP_ZF_Fresh_Conjunction_Fragment_Model
  imports Bacon_PP_ZF_Fresh_Constant_Builder_Fragment_Model
begin

section \<open>Adding conjunction\<close>

text \<open>
  We add the closed curried conjunction operator.  Its application to truth
  is equivalent to identity, and its application to falsity is equivalent
  to the constant-falsity operator.  Hence the proposition and unary stocks
  are unchanged.
\<close>

definition pp_conjunction_builder :: oterm where
  "pp_conjunction_builder =
    Lam Prop (Lam Prop (Conj (Var 1) (Var 0)))"

lemma typed_pp_conjunction_builder:
  "\<Gamma> \<turnstile> pp_conjunction_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_conjunction_builder_def pp_unary_ty_def lookup_def)

lemma pp_conjunction_builder_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      pp_conjunction_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_conjunction_builder :
      Prop \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_conjunction_builder)
  show "consts_of pp_conjunction_builder = {}"
    by (simp add: pp_conjunction_builder_def)
  show "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_conjunction_builder =
      pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_conjunction_builder"
    by simp
qed

abbreviation pp_t_conjunction_builder_type :: otype where
  "pp_t_conjunction_builder_type \<equiv>
    Prop \<rightarrow>\<^sub>o pp_t_constants_unary_type"

definition pp_t_conjunction_result :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_conjunction_result p q =
    pp_t_prop (\<lambda>w. pp_t_holds p w \<and> pp_t_holds q w)"

lemma pp_t_conjunction_result_in_domain:
  "Elem (pp_t_conjunction_result p q) (pp_t_domain Prop)"
  unfolding pp_t_conjunction_result_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_conjunction_result_respects:
  assumes p: "Elem p (pp_t_domain Prop)"
    and p': "Elem p' (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and q': "Elem q' (pp_t_domain Prop)"
    and pp': "pp_t_eqv Prop w p p'"
    and qq': "pp_t_eqv Prop w q q'"
  shows "pp_t_eqv Prop w
    (pp_t_conjunction_result p q)
    (pp_t_conjunction_result p' q')"
  unfolding pp_t_conjunction_result_def
    pp_t_prop_eqv_pp_t_prop_iff
  using pp_t_prop_eqv_at[OF pp']
    pp_t_prop_eqv_at[OF qq']
  by blast

definition pp_t_conjunction_unary :: "ZF \<Rightarrow> ZF" where
  "pp_t_conjunction_unary p =
    Lambda (pp_t_domain Prop) (pp_t_conjunction_result p)"

lemma pp_t_conjunction_unary_in_domain:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "Elem (pp_t_conjunction_unary p)
    (pp_t_domain pp_t_constants_unary_type)"
proof (unfold pp_t_conjunction_unary_def, rule pp_t_lambda_closed)
  show "\<And>q. Elem q (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_t_conjunction_result p q) (pp_t_domain Prop)"
    by (rule pp_t_conjunction_result_in_domain)
  show "\<And>w q q'.
      Elem q (pp_t_domain Prop) \<Longrightarrow>
      Elem q' (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w q q' \<Longrightarrow>
      pp_t_eqv Prop w
        (pp_t_conjunction_result p q)
        (pp_t_conjunction_result p q')"
  proof -
    fix w q q'
    assume q: "Elem q (pp_t_domain Prop)"
      and q': "Elem q' (pp_t_domain Prop)"
      and qq': "pp_t_eqv Prop w q q'"
    show "pp_t_eqv Prop w
        (pp_t_conjunction_result p q)
        (pp_t_conjunction_result p q')"
      by (rule pp_t_conjunction_result_respects[
        OF p p q q' pp_t_eqv_reflexive[OF p] qq'])
  qed
qed

lemma pp_t_conjunction_unary_apply:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_conjunction_unary p \<acute> q =
    pp_t_conjunction_result p q"
  using q
  by (simp add: pp_t_conjunction_unary_def Lambda_app)

lemma pp_t_conjunction_unary_respects:
  assumes p: "Elem p (pp_t_domain Prop)"
    and p': "Elem p' (pp_t_domain Prop)"
    and pp': "pp_t_eqv Prop w p p'"
  shows "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_conjunction_unary p)
    (pp_t_conjunction_unary p')"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem (pp_t_conjunction_unary p)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_conjunction_unary_in_domain[OF p])
  show "Elem (pp_t_conjunction_unary p')
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_conjunction_unary_in_domain[OF p'])
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_conjunction_unary p \<acute> q)
          (pp_t_conjunction_unary p' \<acute> q))"
  proof (intro allI impI)
    fix v q
    assume future: "prefix w v"
      and q: "Elem q (pp_t_domain Prop)"
    have pp'_v: "pp_t_eqv Prop v p p'"
      by (rule pp_t_eqv_persistent[OF pp' future])
    show "pp_t_eqv Prop v
        (pp_t_conjunction_unary p \<acute> q)
        (pp_t_conjunction_unary p' \<acute> q)"
      unfolding
        pp_t_conjunction_unary_apply[OF q]
        pp_t_conjunction_unary_apply[OF q]
      by (rule pp_t_conjunction_result_respects[
        OF p p' q q pp'_v pp_t_eqv_reflexive[OF q]])
  qed
qed

definition pp_t_conjunction_builder :: ZF where
  "pp_t_conjunction_builder =
    Lambda (pp_t_domain Prop) pp_t_conjunction_unary"

lemma pp_t_conjunction_builder_in_domain:
  "Elem pp_t_conjunction_builder
    (pp_t_domain pp_t_conjunction_builder_type)"
proof (unfold pp_t_conjunction_builder_def, rule pp_t_lambda_closed)
  show "\<And>p. Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem (pp_t_conjunction_unary p)
        (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_conjunction_unary_in_domain)
  show "\<And>w p p'.
      Elem p (pp_t_domain Prop) \<Longrightarrow>
      Elem p' (pp_t_domain Prop) \<Longrightarrow>
      pp_t_eqv Prop w p p' \<Longrightarrow>
      pp_t_eqv pp_t_constants_unary_type w
        (pp_t_conjunction_unary p)
        (pp_t_conjunction_unary p')"
    by (rule pp_t_conjunction_unary_respects)
qed

lemma pp_t_conjunction_builder_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_conjunction_builder \<acute> p =
    pp_t_conjunction_unary p"
  using p
  by (simp add: pp_t_conjunction_builder_def Lambda_app)

lemma pp_t_eval_conjunction_builder[simp]:
  "pp_t_eval C \<rho> pp_conjunction_builder =
    pp_t_conjunction_builder"
proof -
  show ?thesis
    unfolding pp_conjunction_builder_def
      pp_t_conjunction_builder_def pp_t_conjunction_unary_def
      pp_t_conjunction_result_def
    by (simp add: Lambda_ext)
qed

section \<open>The enlarged pure stock\<close>

definition pp_t_conjunction_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_conjunction_fragment_pure \<sigma> w x \<longleftrightarrow>
    pp_t_constant_builder_fragment_pure \<sigma> w x
    \<or>
    (\<sigma> = pp_t_conjunction_builder_type
      \<and> pp_t_eqv pp_t_conjunction_builder_type
        w pp_t_conjunction_builder x)"

lemma pp_t_conjunction_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_conjunction_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_constant_builder_fragment_pure \<sigma>)"
    by (rule pp_t_constant_builder_fragment_pure_admissible)
  have builder:
      "pp_t_predicate_admissible pp_t_conjunction_builder_type
        (\<lambda>w x. pp_t_eqv pp_t_conjunction_builder_type
          w pp_t_conjunction_builder x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_conjunction_builder_in_domain] .
  show ?thesis
    using old builder
    unfolding pp_t_predicate_admissible_def
      pp_t_conjunction_fragment_pure_def
    by blast
qed

lemma pp_t_conjunction_is_pure[simp]:
  "pp_t_conjunction_fragment_pure
    pp_t_conjunction_builder_type w pp_t_conjunction_builder"
  unfolding pp_t_conjunction_fragment_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_conjunction_builder_in_domain]
  by blast

lemma pp_t_conjunction_pure_Prop_iff:
  "pp_t_conjunction_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_constant_builder_fragment_pure Prop w P"
  unfolding pp_t_conjunction_fragment_pure_def by simp

lemma pp_t_conjunction_pure_unary_iff:
  "pp_t_conjunction_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow>
    pp_t_constant_builder_fragment_pure
      pp_t_constants_unary_type w X"
  unfolding pp_t_conjunction_fragment_pure_def by simp

lemma pp_t_conjunction_pure_classifier_iff:
  "pp_t_conjunction_fragment_pure
      pp_t_constants_classifier_type w X
    \<longleftrightarrow>
    pp_t_constant_builder_fragment_pure
      pp_t_constants_classifier_type w X"
  unfolding pp_t_conjunction_fragment_pure_def by simp

lemma pp_t_conjunction_old_input:
  assumes pure_f:
      "pp_t_constant_builder_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_conjunction_fragment_pure \<sigma> w x"
  shows "pp_t_constant_builder_fragment_pure \<sigma> w x"
proof -
  from pure_x show ?thesis
    unfolding pp_t_conjunction_fragment_pure_def
  proof
    assume
      "pp_t_constant_builder_fragment_pure \<sigma> w x"
    then show ?thesis .
  next
    assume new:
      "\<sigma> = pp_t_conjunction_builder_type
        \<and> pp_t_eqv pp_t_conjunction_builder_type
          w pp_t_conjunction_builder x"
    then have sigma:
        "\<sigma> = pp_t_conjunction_builder_type"
      by blast
    have False
      using pure_f
      unfolding sigma
        pp_t_constant_builder_fragment_pure_def
        pp_t_constants_fragment_pure_def
      by simp
    then show ?thesis by blast
  qed
qed

lemma pp_t_conjunction_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_conjunction_builder_type)"
    and x: "Elem x (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_conjunction_builder_type
        w pp_t_conjunction_builder f"
    and pure_x:
      "pp_t_conjunction_fragment_pure Prop w x"
  shows "pp_t_conjunction_fragment_pure
    pp_t_constants_unary_type w (f \<acute> x)"
proof -
  have x_class:
      "pp_t_eqv Prop w (pp_zf_truth True) x
        \<or> pp_t_eqv Prop w (pp_zf_truth False) x"
    using pure_x
    unfolding pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff .
  have x_refl: "pp_t_eqv Prop w x x"
    by (rule pp_t_eqv_reflexive[OF x])
  have application:
      "pp_t_eqv pp_t_constants_unary_type w
        (pp_t_conjunction_builder \<acute> x) (f \<acute> x)"
    by (rule pp_t_app_respects[
      OF representative x x x_refl])
  from x_class show ?thesis
  proof
    assume truth:
        "pp_t_eqv Prop w (pp_zf_truth True) x"
    have constant_class:
        "pp_t_eqv pp_t_constants_unary_type w
          pp_t_identity_operator
          (pp_t_conjunction_builder \<acute> x)"
    proof -
      have first:
          "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_conjunction_unary (pp_zf_truth True))
            (pp_t_conjunction_unary x)"
        by (rule pp_t_conjunction_unary_respects[
          OF pp_t_truth_in_domain x truth])
      have truth_identity:
          "pp_t_eqv pp_t_constants_unary_type w
            pp_t_identity_operator
            (pp_t_conjunction_unary (pp_zf_truth True))"
      proof (rule pp_t_arrow_eqv_if_pointwise)
        show "Elem pp_t_identity_operator
            (pp_t_domain pp_t_constants_unary_type)"
          by (rule pp_t_identity_operator_in_domain)
        show "Elem (pp_t_conjunction_unary (pp_zf_truth True))
            (pp_t_domain pp_t_constants_unary_type)"
          by (rule pp_t_conjunction_unary_in_domain[
            OF pp_t_truth_in_domain])
        show "\<forall>v. prefix w v \<longrightarrow>
            (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
              pp_t_eqv Prop v
                (pp_t_identity_operator \<acute> q)
                (pp_t_conjunction_unary
                  (pp_zf_truth True) \<acute> q))"
          by (intro allI impI)
            (simp add: pp_t_identity_operator_def
              pp_t_conjunction_unary_apply
              pp_t_conjunction_result_def Lambda_app)
      qed
      have middle:
          "Elem (pp_t_conjunction_unary (pp_zf_truth True))
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_conjunction_unary_in_domain[
          OF pp_t_truth_in_domain])
      have final:
          "Elem (pp_t_conjunction_unary x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_conjunction_unary_in_domain[OF x])
      have trans:
          "pp_t_eqv pp_t_constants_unary_type w
            pp_t_identity_operator
            (pp_t_conjunction_unary x)"
        using pp_t_identity_operator_in_domain middle final
          truth_identity first
        by (meson pp_t_eqv_transitive)
      show ?thesis
        using trans
        unfolding pp_t_conjunction_builder_apply[OF x] .
    qed
    have result:
        "pp_t_eqv pp_t_constants_unary_type w
          pp_t_identity_operator (f \<acute> x)"
    proof -
      have middle:
          "Elem (pp_t_conjunction_builder \<acute> x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_app_closed[
          OF pp_t_conjunction_builder_in_domain x])
      have final:
          "Elem (f \<acute> x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_app_closed[OF f x])
      show ?thesis
        using pp_t_identity_operator_in_domain middle final
          constant_class application
        by (meson pp_t_eqv_transitive)
    qed
    show ?thesis
      unfolding pp_t_conjunction_pure_unary_iff
        pp_t_constant_builder_pure_unary_iff
        pp_t_constants_fragment_pure_unary_iff
        pp_t_constants_unary_pure_def
        pp_t_idneg_unary_pure_def
      using result by blast
  next
    assume falsity:
        "pp_t_eqv Prop w (pp_zf_truth False) x"
    have constant_class:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_constant_operator False)
          (pp_t_conjunction_builder \<acute> x)"
    proof -
      have first:
          "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_conjunction_unary (pp_zf_truth False))
            (pp_t_conjunction_unary x)"
        by (rule pp_t_conjunction_unary_respects[
          OF pp_t_truth_in_domain x falsity])
      have falsity_constant:
          "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_constant_operator False)
            (pp_t_conjunction_unary (pp_zf_truth False))"
      proof (rule pp_t_arrow_eqv_if_pointwise)
        show "Elem (pp_t_constant_operator False)
            (pp_t_domain pp_t_constants_unary_type)"
          by (rule pp_t_constant_operator_in_domain)
        show "Elem (pp_t_conjunction_unary (pp_zf_truth False))
            (pp_t_domain pp_t_constants_unary_type)"
          by (rule pp_t_conjunction_unary_in_domain[
            OF pp_t_truth_in_domain])
        show "\<forall>v. prefix w v \<longrightarrow>
            (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
              pp_t_eqv Prop v
                (pp_t_constant_operator False \<acute> q)
                (pp_t_conjunction_unary
                  (pp_zf_truth False) \<acute> q))"
          by (intro allI impI)
            (simp add: pp_t_constant_operator_apply
              pp_t_conjunction_unary_apply
              pp_t_conjunction_result_def)
      qed
      have middle:
          "Elem (pp_t_conjunction_unary (pp_zf_truth False))
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_conjunction_unary_in_domain[
          OF pp_t_truth_in_domain])
      have final:
          "Elem (pp_t_conjunction_unary x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_conjunction_unary_in_domain[OF x])
      have trans:
          "pp_t_eqv pp_t_constants_unary_type w
            (pp_t_constant_operator False)
            (pp_t_conjunction_unary x)"
        using pp_t_constant_operator_in_domain middle final
          falsity_constant first
        by (meson pp_t_eqv_transitive)
      show ?thesis
        using trans
        unfolding pp_t_conjunction_builder_apply[OF x] .
    qed
    have result:
        "pp_t_eqv pp_t_constants_unary_type w
          (pp_t_constant_operator False) (f \<acute> x)"
    proof -
      have middle:
          "Elem (pp_t_conjunction_builder \<acute> x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_app_closed[
          OF pp_t_conjunction_builder_in_domain x])
      have final:
          "Elem (f \<acute> x)
            (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_app_closed[OF f x])
      show ?thesis
        using pp_t_constant_operator_in_domain middle final
          constant_class application
        by (meson pp_t_eqv_transitive)
    qed
    show ?thesis
      unfolding pp_t_conjunction_pure_unary_iff
        pp_t_constant_builder_pure_unary_iff
        pp_t_constants_fragment_pure_unary_iff
        pp_t_constants_unary_pure_def
      using result by blast
  qed
qed

lemma pp_t_conjunction_fragment_application:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_conjunction_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_conjunction_fragment_pure \<sigma> w x"
  shows "pp_t_conjunction_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_constant_builder_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    | (builder)
        "\<sigma> = Prop" "\<tau> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_conjunction_builder_type
          w pp_t_conjunction_builder f"
    unfolding pp_t_conjunction_fragment_pure_def
    by auto
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_constant_builder_fragment_pure \<sigma> w x"
      by (rule pp_t_conjunction_old_input[
        OF old pure_x])
    have old_result:
        "pp_t_constant_builder_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_constant_builder_fragment_application[
        OF f x old old_x])
    show ?thesis
      unfolding pp_t_conjunction_fragment_pure_def
      using old_result by blast
  next
    case builder
    show ?thesis
      using pp_t_conjunction_application[
        OF _ _ builder(3)] f x pure_x builder
      by simp
  qed
qed

section \<open>The moving-fundamental interpretation\<close>

interpretation ConjunctionFragment:
  pp_t_moving_internal_parameters
    pp_t_conjunction_fragment_pure
  by standard
    (rule pp_t_conjunction_fragment_pure_admissible)

abbreviation pp_t_conjunction_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_conjunction_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_conjunction_fragment_pure"

lemma pp_t_conjunction_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      (pp_pure pp_t_conjunction_builder_type
        pp_conjunction_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_conjunction_builder :
        pp_t_conjunction_builder_type"
    using typed_pp_conjunction_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
    by simp
qed

theorem pp_t_conjunction_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_conjunction_builder_type pp_conjunction_builder)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_purity_holds by blast

lemma pp_t_conjunction_constant_builder_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      (pp_pure pp_t_conjunction_builder_type
        pp_constant_builder)) w"
proof -
  have typed:
      "[] \<turnstile> pp_constant_builder :
        pp_t_conjunction_builder_type"
    using typed_pp_constant_builder[of "[]"]
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have pure:
      "pp_t_conjunction_fragment_pure
        pp_t_conjunction_builder_type w pp_t_constant_builder"
    unfolding pp_t_conjunction_fragment_pure_def
    using pp_t_constant_builder_is_pure by blast
  show ?thesis
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w] pure
    by simp
qed

theorem pp_t_conjunction_constant_builder_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_conjunction_builder_type pp_constant_builder)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_constant_builder_purity_holds by blast

lemma pp_t_conjunction_identity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type prop_id)) w"
proof -
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed_prop_id env, of w]
    by (simp add: pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_conjunction_identity_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type prop_id)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_identity_purity_holds by blast

lemma pp_t_conjunction_negation_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      (pp_pure pp_t_constants_unary_type
        pp_negation_operator)) w"
proof -
  have typed:
      "[] \<turnstile> pp_negation_operator :
        pp_t_constants_unary_type"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have env: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
    by (simp add: pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_conjunction_negation_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type pp_negation_operator)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_negation_purity_holds by blast

lemma pp_t_conjunction_constant_truth_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
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
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
    by (simp add: pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_conjunction_constant_truth_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjTrue))"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using
    pp_t_conjunction_constant_truth_purity_holds
  by blast

lemma pp_t_conjunction_constant_falsity_purity_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
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
    using
      ConjunctionFragment.pp_t_moving_eval_pure_holds[
        OF typed env, of w]
    by (simp add: pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_conjunction_constant_falsity_purity_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure pp_t_constants_unary_type
      (pp_constant_operator ObjFalse))"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using
    pp_t_conjunction_constant_falsity_purity_holds
  by blast

lemma pp_t_conjunction_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_conjunction_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_constants_stock_classifier"
    unfolding pp_t_constants_stock_classifier_def
      pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def
      pp_t_constants_fragment_pure_def
    by simp
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_constants_stock_classifier_in_domain,
      of "pp_t_conjunction_fragment_pure
        pp_t_constants_classifier_type" w]
    by (simp add: unary_classifier
      pp_t_conjunction_fragment_pure_def
      pp_t_constant_builder_fragment_pure_def)
qed

theorem pp_t_conjunction_target_PP_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_target_PP_holds by blast

lemma pp_t_conjunction_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_conjunction_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_conjunction_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_conjunction_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_conjunction_application_closure_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ConjunctionFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      ConjunctionFragment.MovingTreeConstants.pp_t_den_def
      pp_t_conjunction_application_closure_holds_iff
    using pp_t_conjunction_fragment_application by blast
qed

theorem pp_t_conjunction_unique_fundamental_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using
    ConjunctionFragment.pp_t_moving_unique_fundamental_holds
  by blast

theorem pp_t_conjunction_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows
    "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
      (pp_no_fundamentals \<sigma>)"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using
    ConjunctionFragment.pp_t_moving_no_fundamentals_holds[
      OF assms]
  by blast

section \<open>Recombination, Exhaustion, and functionality\<close>

lemma pp_t_conjunction_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
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
          (pp_t_eval pp_t_conjunction_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_conjunction_fragment_pure Prop w P"
      using
        ConjunctionFragment.pp_t_moving_eval_pure_holds[
          OF var_type extended, of w]
      by simp
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
        (pp_t_eval pp_t_conjunction_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
        pp_t_conjunction_pure_Prop_iff
        pp_t_constant_builder_pure_Prop_iff
        pp_t_constants_fragment_pure_Prop_iff
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

lemma pp_t_conjunction_pure_true_implies_necessary:
  assumes P: "Elem P (pp_t_domain Prop)"
    and pure:
      "pp_t_conjunction_fragment_pure Prop w P"
    and true_now: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  have old_pure:
      "pp_t_constant_builder_fragment_pure Prop w P"
    using pure
    unfolding pp_t_conjunction_pure_Prop_iff .
  show ?thesis
    by (rule pp_t_constant_builder_pure_true_implies_necessary[
      OF P old_pure true_now])
qed

lemma pp_t_conjunction_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
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
          (pp_t_eval pp_t_conjunction_fragment_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow>
        pp_t_conjunction_fragment_pure Prop w P"
      using
        ConjunctionFragment.pp_t_moving_eval_pure_holds[
          OF var_type extended, of w]
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_conjunction_fragment_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff
        pp_t_conjunction_pure_true_implies_necessary[OF P]
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_conjunction_zeroary_recombination_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_zeroary_recombination_holds
  by blast

theorem pp_t_conjunction_zeroary_exhaustion_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_zeroary_exhaustion_holds
  by blast

lemma pp_t_conjunction_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_conjunction_fragment_pure
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

lemma pp_t_conjunction_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_conjunction_fragment_pure
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

theorem pp_t_conjunction_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding
    pp_t_conjunction_unary_recombination_holds_iff
    pp_t_conjunction_pure_unary_iff
    pp_t_constant_builder_pure_unary_iff
  using pp_t_constants_pure_unary_QLN(1)
  by blast

theorem pp_t_conjunction_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding
    pp_t_conjunction_unary_exhaustion_holds_iff
    pp_t_conjunction_pure_unary_iff
    pp_t_constant_builder_pure_unary_iff
  using pp_t_constants_pure_unary_QLN(2)
  by blast

theorem pp_t_conjunction_unary_recombination_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_unary_recombination_holds
  by blast

theorem pp_t_conjunction_unary_exhaustion_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    ConjunctionFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_conjunction_unary_exhaustion_holds
  by blast

lemma pp_t_conjunction_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_conjunction_fragment_constants \<rho>
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

theorem pp_t_conjunction_modalized_functionality_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (ConjunctionFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      ConjunctionFragment.MovingTreeConstants.pp_t_den_def
      pp_t_conjunction_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

section \<open>The conjunction fragment\<close>

definition pp_conjunction_fragment_PP_axioms ::
    "oterm set"
where
  "pp_conjunction_fragment_PP_axioms =
    insert
      (pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_conjunction_builder)
      pp_constant_builder_fragment_PP_axioms"

theorem pp_t_conjunction_fragment_PP_gvalid:
  "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_conjunction_fragment_PP_axioms"
  unfolding
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_conjunction_fragment_PP_axioms"
  from A consider
      (builder)
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
    unfolding pp_conjunction_fragment_PP_axioms_def
      pp_constant_builder_fragment_PP_axioms_def
      pp_logical_constants_fragment_PP_axioms_def
      pp_identity_negation_fragment_PP_axioms_def
      pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show
      "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> A"
  proof cases
    case builder
    then show ?thesis
      using pp_t_conjunction_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_builder
    then show ?thesis
      using pp_t_conjunction_constant_builder_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_truth
    then show ?thesis
      using pp_t_conjunction_constant_truth_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case constant_falsity
    then show ?thesis
      using pp_t_conjunction_constant_falsity_purity_gvalid
      unfolding pp_unary_ty_def by simp
  next
    case identity_purity
    then show ?thesis
      using pp_t_conjunction_identity_purity_gvalid by simp
  next
    case negation_purity
    then show ?thesis
      using pp_t_conjunction_negation_purity_gvalid by simp
  next
    case target
    then show ?thesis
      using pp_t_conjunction_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_conjunction_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_conjunction_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule
        pp_t_conjunction_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_conjunction_zeroary_recombination_gvalid
      by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_conjunction_unary_recombination_gvalid
      by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_conjunction_zeroary_exhaustion_gvalid
      by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_conjunction_unary_exhaustion_gvalid
      by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_conjunction_modalized_functionality_gvalid)
  qed
qed

theorem pp_conjunction_fragment_PP_axioms_consistent:
  "CEV_axiom_consistent []
    pp_conjunction_fragment_PP_axioms"
  using
    ConjunctionFragment.MovingTreeConstants.pp_t_base_sound
    ConjunctionFragment.MovingTreeConstants.pp_t_zeta_sound
    pp_t_conjunction_fragment_PP_gvalid
  by (rule
    ConjunctionFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_conjunction_fragment_consistent:
  assumes "U \<subseteq> pp_conjunction_fragment_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_conjunction_fragment_PP_gvalid
    unfolding
      ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using
      ConjunctionFragment.MovingTreeConstants.pp_t_base_sound
      ConjunctionFragment.MovingTreeConstants.pp_t_zeta_sound
      valid
    by (rule
      ConjunctionFragment.MovingTreeConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
