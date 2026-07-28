theory Bacon_PP_ZF_Fresh_T6_Diagonal_Fragment_Model
  imports
    "Higher_Order_Metaphysics_PP_ZF_Fun_Prime.Bacon_PP_ZF_Fresh_Fun_Prime_Fragment_Model"
begin

section \<open>Goodman's T6 diagonal over the fun-prime stock\<close>

text \<open>
  This is the denotation of the exact closed object-language term
  \<open>pp_T6_liar\<close> before that denotation is added to the pure unary stock.
  The later stabilization lemmas must show that reevaluating both
  \<open>fun\<acute>\<close> and the T6 diagonal against the enlarged stock leaves these
  denotations unchanged.
\<close>

definition pp_t_fun_prime_T6_operator :: ZF where
  "pp_t_fun_prime_T6_operator =
    pp_t_eval pp_t_fun_prime_fragment_constants
      pp_t_closed_env pp_T6_liar"

lemma pp_t_fun_prime_T6_operator_in_domain:
  "Elem pp_t_fun_prime_T6_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_fun_prime_T6_operator_def
  using
    FunPrimeFragment.MovingTreeConstants.pp_t_eval_type[
      OF typed_pp_T6_liar pp_t_empty_env_typed]
  by (simp add: pp_t_dom_def pp_unary_ty_def)

lemma pp_t_fun_prime_T6_operator_holds_raw:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>q.
        Elem q (pp_t_domain Prop) \<longrightarrow>
        (pp_t_fun_prime_unary_pure w X
          \<and> pp_t_holds
            (pp_t_eval pp_t_fun_prime_fragment_constants
              (extend_env q
                (extend_env X
                  (extend_env p pp_t_closed_env)))
              (pp_fun_prime (Var 0))) w
          \<and> pp_t_eqv Prop w p (X \<acute> q))
        \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
proof -
  have beta:
      "pp_t_eval pp_t_fun_prime_fragment_constants
          pp_t_closed_env pp_T6_liar \<acute> p
       =
       pp_t_eval pp_t_fun_prime_fragment_constants
          (extend_env p pp_t_closed_env)
          (Forall pp_t_constants_unary_type
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_t_constants_unary_type (Var 1))
                  (Conj
                    (pp_fun_prime (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))"
    unfolding pp_T6_liar_def pp_unary_ty_def
    using p by (simp add: Lambda_app)
  show ?thesis
  unfolding pp_t_fun_prime_T6_operator_def beta
    pp_pure_def
  apply (simp only: pp_t_eval_Forall_holds
    pp_t_eval_Imp_holds pp_t_eval_Conj_holds
    pp_t_eval_Neg_holds pp_t_eval_Eq_holds)
  by (simp del: pp_t_eqv.simps
    add: pp_t_classifier_holds extend_env.simps
    pp_t_three_extensions_index_two shift_by_def shift_ren_def
    pp_t_fun_prime_pure_unary_iff)
qed

lemma pp_t_embedded_fun_prime_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval pp_t_fun_prime_fragment_constants
        (extend_env q
          (extend_env X
            (extend_env p pp_t_closed_env)))
        (pp_fun_prime (Var 0))) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> q) w"
proof -
  let ?nested =
    "extend_env q
      (extend_env X (extend_env p pp_t_closed_env))"
  let ?single = "extend_env q pp_t_closed_env"
  have env_eqv:
      "pp_t_env_eqv w [Prop] ?nested ?single"
    unfolding pp_t_env_eqv_def pp_t_env_typed_def
    using q pp_t_eqv_reflexive[OF q]
    by (simp add: lookup_def)
  have related:
      "pp_t_eqv Prop w
        (pp_t_eval pp_t_fun_prime_fragment_constants
          ?nested (pp_fun_prime (Var 0)))
        (pp_t_eval pp_t_fun_prime_fragment_constants
          ?single (pp_fun_prime (Var 0)))"
    using
      FunPrimeFragment.MovingTreeConstants.pp_t_eval_respects[
        OF typed_pp_fun_prime[OF typed_var0] env_eqv] .
  have beta:
      "pp_t_eval pp_t_fun_prime_fragment_constants
          ?single (pp_fun_prime (Var 0))
       =
       pp_t_quantified_fun_prime_operator \<acute> q"
  proof -
    have evaluated:
        "pp_t_eval pp_t_fun_prime_fragment_constants
            pp_t_closed_env pp_fun_prime_operator
          = pp_t_quantified_fun_prime_operator"
      by (rule pp_t_eval_fun_prime_operator)
    have application:
        "pp_t_eval pp_t_fun_prime_fragment_constants
            pp_t_closed_env pp_fun_prime_operator \<acute> q
          = pp_t_quantified_fun_prime_operator \<acute> q"
      using evaluated by simp
    have beta_application:
        "pp_t_eval pp_t_fun_prime_fragment_constants
            pp_t_closed_env pp_fun_prime_operator \<acute> q
          =
         pp_t_eval pp_t_fun_prime_fragment_constants
            ?single (pp_fun_prime (Var 0))"
      unfolding pp_fun_prime_operator_def
      using q by (simp add: Lambda_app)
    show ?thesis
      using application beta_application by simp
  qed
  show ?thesis
    using pp_t_prop_eqv_at[OF related, of w]
    unfolding beta by simp
qed

lemma pp_t_fun_prime_T6_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>q.
        Elem q (pp_t_domain Prop) \<longrightarrow>
        (pp_t_fun_prime_unary_pure w X
          \<and> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> q) w
          \<and> pp_t_eqv Prop w p (X \<acute> q))
        \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
  unfolding pp_t_fun_prime_T6_operator_holds_raw[OF p]
  using pp_t_embedded_fun_prime_holds[OF p]
  by blast

definition pp_t_T6_diagonal_unary_pure ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_T6_diagonal_unary_pure w X \<longleftrightarrow>
    pp_t_fun_prime_unary_pure w X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_fun_prime_T6_operator X"

lemma pp_t_T6_diagonal_unary_pure_admissible:
  "pp_t_predicate_admissible pp_t_constants_unary_type
    pp_t_T6_diagonal_unary_pure"
proof -
  have old:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        pp_t_fun_prime_unary_pure"
    by (rule pp_t_fun_prime_unary_pure_admissible)
  have added:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator X)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_fun_prime_T6_operator_in_domain] .
  show ?thesis
    using old added
    unfolding pp_t_predicate_admissible_def
      pp_t_T6_diagonal_unary_pure_def
    by blast
qed

definition pp_t_T6_diagonal_stock_classifier :: ZF where
  "pp_t_T6_diagonal_stock_classifier =
    pp_t_classifier pp_t_constants_unary_type
      pp_t_T6_diagonal_unary_pure"

lemma pp_t_T6_diagonal_stock_classifier_in_domain:
  "Elem pp_t_T6_diagonal_stock_classifier
    (pp_t_domain pp_t_constants_classifier_type)"
  unfolding pp_t_T6_diagonal_stock_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_T6_diagonal_unary_pure_admissible)

definition pp_t_T6_diagonal_fragment_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_T6_diagonal_fragment_pure \<sigma> w x \<longleftrightarrow>
    (pp_t_fun_prime_fragment_pure \<sigma> w x
      \<and> \<sigma> \<noteq> pp_t_constants_classifier_type)
    \<or>
    (\<sigma> = pp_t_constants_unary_type
      \<and> pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator x)
    \<or>
    (\<sigma> = pp_t_constants_classifier_type
      \<and> pp_t_eqv pp_t_constants_classifier_type
        w pp_t_T6_diagonal_stock_classifier x)"

lemma pp_t_T6_diagonal_fragment_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_T6_diagonal_fragment_pure \<sigma>)"
proof -
  have old:
      "pp_t_predicate_admissible \<sigma>
        (pp_t_fun_prime_fragment_pure \<sigma>)"
    by (rule pp_t_fun_prime_fragment_pure_admissible)
  have added:
      "pp_t_predicate_admissible pp_t_constants_unary_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_fun_prime_T6_operator_in_domain] .
  have classifier:
      "pp_t_predicate_admissible pp_t_constants_classifier_type
        (\<lambda>w x. pp_t_eqv pp_t_constants_classifier_type
          w pp_t_T6_diagonal_stock_classifier x)"
    using pp_t_eqv_classifier_admissible[
      OF pp_t_T6_diagonal_stock_classifier_in_domain] .
  show ?thesis
    unfolding pp_t_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_t_domain \<sigma>)"
      and y: "Elem y (pp_t_domain \<sigma>)"
      and xy: "pp_t_eqv \<sigma> w x y"
      and future: "prefix w v"
    have old_iff:
        "pp_t_fun_prime_fragment_pure \<sigma> v x
          \<longleftrightarrow>
         pp_t_fun_prime_fragment_pure \<sigma> v y"
      using old x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have added_iff:
        "\<sigma> = pp_t_constants_unary_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_fun_prime_T6_operator x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_unary_type
            v pp_t_fun_prime_T6_operator y"
      using added x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    have classifier_iff:
        "\<sigma> = pp_t_constants_classifier_type \<Longrightarrow>
        pp_t_eqv pp_t_constants_classifier_type v
            pp_t_T6_diagonal_stock_classifier x
          \<longleftrightarrow>
        pp_t_eqv pp_t_constants_classifier_type v
            pp_t_T6_diagonal_stock_classifier y"
      using classifier x y xy future
      unfolding pp_t_predicate_admissible_def by blast
    show "pp_t_T6_diagonal_fragment_pure \<sigma> v x =
        pp_t_T6_diagonal_fragment_pure \<sigma> v y"
      unfolding pp_t_T6_diagonal_fragment_pure_def
      using old_iff added_iff classifier_iff by blast
  qed
qed

interpretation T6DiagonalFragment:
  pp_t_moving_internal_parameters
    pp_t_T6_diagonal_fragment_pure
  by standard
    (rule pp_t_T6_diagonal_fragment_pure_admissible)

abbreviation pp_t_T6_diagonal_fragment_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_T6_diagonal_fragment_constants \<equiv>
    pp_t_moving_internal_constants
      pp_t_T6_diagonal_fragment_pure"

lemma pp_t_T6_diagonal_pure_unary_iff:
  "pp_t_T6_diagonal_fragment_pure
      pp_t_constants_unary_type w X
    \<longleftrightarrow> pp_t_T6_diagonal_unary_pure w X"
  unfolding pp_t_T6_diagonal_fragment_pure_def
    pp_t_T6_diagonal_unary_pure_def
    pp_t_fun_prime_pure_unary_iff
  by simp

lemma pp_t_T6_diagonal_pure_Prop_iff:
  "pp_t_T6_diagonal_fragment_pure Prop w P
    \<longleftrightarrow>
    pp_t_fun_prime_fragment_pure Prop w P"
  unfolding pp_t_T6_diagonal_fragment_pure_def by simp

lemma pp_t_T6_diagonal_pure_classifier_iff:
  "pp_t_T6_diagonal_fragment_pure
      pp_t_constants_classifier_type w C
    \<longleftrightarrow>
    pp_t_eqv pp_t_constants_classifier_type
      w pp_t_T6_diagonal_stock_classifier C"
  unfolding pp_t_T6_diagonal_fragment_pure_def by simp

lemma pp_t_T6_diagonal_added_is_pure[simp]:
  "pp_t_T6_diagonal_fragment_pure
    pp_t_constants_unary_type w
    pp_t_fun_prime_T6_operator"
  unfolding pp_t_T6_diagonal_pure_unary_iff
    pp_t_T6_diagonal_unary_pure_def
  using pp_t_eqv_reflexive[
    OF pp_t_fun_prime_T6_operator_in_domain]
  by blast

lemma pp_t_T6_diagonal_classifier_is_pure[simp]:
  "pp_t_T6_diagonal_fragment_pure
    pp_t_constants_classifier_type w
    pp_t_T6_diagonal_stock_classifier"
  unfolding pp_t_T6_diagonal_pure_classifier_iff
  by (rule pp_t_eqv_reflexive[
    OF pp_t_T6_diagonal_stock_classifier_in_domain])

section \<open>The joint fun-prime/diagonal fixed-point test\<close>

definition pp_t_T6_diagonal_fun_prime_operator :: ZF where
  "pp_t_T6_diagonal_fun_prime_operator =
    pp_t_eval pp_t_T6_diagonal_fragment_constants
      pp_t_closed_env pp_fun_prime_operator"

definition pp_t_T6_diagonal_T6_operator :: ZF where
  "pp_t_T6_diagonal_T6_operator =
    pp_t_eval pp_t_T6_diagonal_fragment_constants
      pp_t_closed_env pp_T6_liar"

lemma pp_t_T6_diagonal_fun_prime_operator_in_domain:
  "Elem pp_t_T6_diagonal_fun_prime_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_T6_diagonal_fun_prime_operator_def
  using
    T6DiagonalFragment.MovingTreeConstants.pp_t_eval_type[
      OF typed_pp_fun_prime_operator pp_t_empty_env_typed]
  by (simp add: pp_t_dom_def)

lemma pp_t_T6_diagonal_T6_operator_in_domain:
  "Elem pp_t_T6_diagonal_T6_operator
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_T6_diagonal_T6_operator_def
  using
    T6DiagonalFragment.MovingTreeConstants.pp_t_eval_type[
      OF typed_pp_T6_liar pp_t_empty_env_typed]
  by (simp add: pp_t_dom_def pp_unary_ty_def)

definition pp_t_T6_diagonal_joint_fixed_point :: bool where
  "pp_t_T6_diagonal_joint_fixed_point \<longleftrightarrow>
    pp_t_T6_diagonal_fun_prime_operator =
      pp_t_quantified_fun_prime_operator
    \<and>
    pp_t_T6_diagonal_T6_operator =
      pp_t_fun_prime_T6_operator"

lemma pp_t_T6_diagonal_fun_prime_predicate_shrinks:
  assumes p: "Elem p (pp_t_domain Prop)"
    and enlarged:
      "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w p"
  shows "pp_t_fun_prime_predicate
    pp_t_fun_prime_unary_pure w p"
proof (unfold pp_t_fun_prime_predicate_def, intro allI impI)
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and old_pure:
      "pp_t_fun_prime_unary_pure w X
        \<and> pp_t_fun_prime_unary_pure w Y"
    and agreement:
      "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
  have enlarged_pure:
      "pp_t_T6_diagonal_unary_pure w X
        \<and> pp_t_T6_diagonal_unary_pure w Y"
    using old_pure
    unfolding pp_t_T6_diagonal_unary_pure_def
    by blast
  show "pp_t_eqv pp_t_constants_unary_type w X Y"
    using enlarged X Y enlarged_pure agreement
    unfolding pp_t_fun_prime_predicate_def by blast
qed

text \<open>
  Thus adding the diagonal can only remove fun-prime propositions.  The
  converse is the substantive absorption condition: every proposition that
  separated the fun-prime stock must also separate the new diagonal from all
  its old members.
\<close>

definition pp_t_T6_diagonal_absorbs_fun_prime :: bool where
  "pp_t_T6_diagonal_absorbs_fun_prime \<longleftrightarrow>
    (\<forall>w p.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p
      \<longrightarrow>
      pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w p)"

lemma pp_t_T6_diagonal_fun_prime_stabilizes_iff:
  "(\<forall>w p.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      (pp_t_fun_prime_predicate
          pp_t_T6_diagonal_unary_pure w p
        \<longleftrightarrow>
       pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p))
    \<longleftrightarrow>
    pp_t_T6_diagonal_absorbs_fun_prime"
  unfolding pp_t_T6_diagonal_absorbs_fun_prime_def
  using pp_t_T6_diagonal_fun_prime_predicate_shrinks
  by blast

lemma pp_t_eval_T6_diagonal_fun_prime_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> p) w
    \<longleftrightarrow>
      pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w p"
proof -
  have beta:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_fun_prime_operator \<acute> p
        =
       pp_t_eval pp_t_T6_diagonal_fragment_constants
          (extend_env p pp_t_closed_env)
          (pp_fun_prime (Var 0))"
    unfolding pp_fun_prime_operator_def
    using p by (simp add: Lambda_app)
  show ?thesis
    unfolding pp_t_T6_diagonal_fun_prime_operator_def beta
      pp_fun_prime_def pp_t_fun_prime_predicate_def pp_pure_def
    using p
    apply (simp only: pp_t_eval_Forall_holds
      pp_t_eval_Imp_holds pp_t_eval_Conj_holds
      pp_t_eval_Eq_holds)
    apply (simp del: pp_t_eqv.simps
      add: pp_t_classifier_holds extend_env.simps
      pp_t_three_extensions_index_two shift_by_def shift_ren_def
      pp_t_T6_diagonal_pure_unary_iff)
    apply (simp only: pp_t_T6_diagonal_pure_unary_iff
      pp_unary_ty_def)
    by simp
qed

lemma pp_t_eval_T6_diagonal_T6_operator_holds_raw:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>q.
        Elem q (pp_t_domain Prop) \<longrightarrow>
        (pp_t_T6_diagonal_unary_pure w X
          \<and> pp_t_holds
            (pp_t_eval pp_t_T6_diagonal_fragment_constants
              (extend_env q
                (extend_env X
                  (extend_env p pp_t_closed_env)))
              (pp_fun_prime (Var 0))) w
          \<and> pp_t_eqv Prop w p (X \<acute> q))
        \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
proof -
  have beta:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          pp_t_closed_env pp_T6_liar \<acute> p
       =
       pp_t_eval pp_t_T6_diagonal_fragment_constants
          (extend_env p pp_t_closed_env)
          (Forall pp_t_constants_unary_type
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_t_constants_unary_type (Var 1))
                  (Conj
                    (pp_fun_prime (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))"
    unfolding pp_T6_liar_def pp_unary_ty_def
    using p by (simp add: Lambda_app)
  show ?thesis
    unfolding pp_t_T6_diagonal_T6_operator_def beta pp_pure_def
    apply (simp only: pp_t_eval_Forall_holds
      pp_t_eval_Imp_holds pp_t_eval_Conj_holds
      pp_t_eval_Neg_holds pp_t_eval_Eq_holds)
    by (simp del: pp_t_eqv.simps
      add: pp_t_classifier_holds extend_env.simps
      pp_t_three_extensions_index_two shift_by_def shift_ren_def
      pp_t_T6_diagonal_pure_unary_iff)
qed

lemma pp_t_T6_diagonal_embedded_fun_prime_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval pp_t_T6_diagonal_fragment_constants
        (extend_env q
          (extend_env X
            (extend_env p pp_t_closed_env)))
        (pp_fun_prime (Var 0))) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w"
proof -
  let ?nested =
    "extend_env q
      (extend_env X (extend_env p pp_t_closed_env))"
  let ?single = "extend_env q pp_t_closed_env"
  have env_eqv:
      "pp_t_env_eqv w [Prop] ?nested ?single"
    unfolding pp_t_env_eqv_def pp_t_env_typed_def
    using q pp_t_eqv_reflexive[OF q]
    by (simp add: lookup_def)
  have related:
      "pp_t_eqv Prop w
        (pp_t_eval pp_t_T6_diagonal_fragment_constants
          ?nested (pp_fun_prime (Var 0)))
        (pp_t_eval pp_t_T6_diagonal_fragment_constants
          ?single (pp_fun_prime (Var 0)))"
    using
      T6DiagonalFragment.MovingTreeConstants.pp_t_eval_respects[
        OF typed_pp_fun_prime[OF typed_var0] env_eqv] .
  have beta:
      "pp_t_eval pp_t_T6_diagonal_fragment_constants
          ?single (pp_fun_prime (Var 0))
       =
       pp_t_T6_diagonal_fun_prime_operator \<acute> q"
  proof -
    have beta_application:
        "pp_t_eval pp_t_T6_diagonal_fragment_constants
            pp_t_closed_env pp_fun_prime_operator \<acute> q
          =
         pp_t_eval pp_t_T6_diagonal_fragment_constants
            ?single (pp_fun_prime (Var 0))"
      unfolding pp_fun_prime_operator_def
      using q by (simp add: Lambda_app)
    show ?thesis
      using beta_application
      unfolding pp_t_T6_diagonal_fun_prime_operator_def
      by simp
  qed
  show ?thesis
    using pp_t_prop_eqv_at[OF related, of w]
    unfolding beta by simp
qed

lemma pp_t_eval_T6_diagonal_T6_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_T6_diagonal_T6_operator \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>q.
        Elem q (pp_t_domain Prop) \<longrightarrow>
        (pp_t_T6_diagonal_unary_pure w X
          \<and> pp_t_holds
            (pp_t_T6_diagonal_fun_prime_operator \<acute> q) w
          \<and> pp_t_eqv Prop w p (X \<acute> q))
        \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
  unfolding pp_t_eval_T6_diagonal_T6_operator_holds_raw[OF p]
  using pp_t_T6_diagonal_embedded_fun_prime_holds[OF p]
  by blast

theorem pp_t_T6_diagonal_fun_prime_operator_stabilizes_iff:
  "pp_t_T6_diagonal_fun_prime_operator =
      pp_t_quantified_fun_prime_operator
    \<longleftrightarrow>
    pp_t_T6_diagonal_absorbs_fun_prime"
proof
  assume equality:
      "pp_t_T6_diagonal_fun_prime_operator =
        pp_t_quantified_fun_prime_operator"
  show "pp_t_T6_diagonal_absorbs_fun_prime"
    unfolding pp_t_T6_diagonal_absorbs_fun_prime_def
  proof (intro allI impI)
    fix w p
    assume p: "Elem p (pp_t_domain Prop)"
      and old:
        "pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p"
    have old_holds:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> p) w"
      using pp_t_quantified_fun_prime_operator_holds[OF p, of w]
        pp_t_fun_prime_stabilizes[OF p, of w] old
      by blast
    have new_holds:
        "pp_t_holds
          (pp_t_T6_diagonal_fun_prime_operator \<acute> p) w"
      using old_holds equality by simp
    show "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w p"
      using pp_t_eval_T6_diagonal_fun_prime_operator_holds[
        OF p, of w] new_holds
      by blast
  qed
next
  assume absorption:
      "pp_t_T6_diagonal_absorbs_fun_prime"
  have predicates:
      "\<And>w p. Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_fun_prime_predicate
            pp_t_T6_diagonal_unary_pure w p
          \<longleftrightarrow>
         pp_t_fun_prime_predicate
            pp_t_fun_prime_unary_pure w p)"
    using pp_t_T6_diagonal_fun_prime_stabilizes_iff
      absorption by blast
  have root_eqv:
      "pp_t_eqv pp_t_constants_unary_type []
        pp_t_T6_diagonal_fun_prime_operator
        pp_t_quantified_fun_prime_operator"
  proof (rule pp_t_arrow_eqv_if_pointwise[
      OF pp_t_T6_diagonal_fun_prime_operator_in_domain
        pp_t_quantified_fun_prime_operator_in_domain])
    show "\<forall>v. prefix [] v \<longrightarrow>
        (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
          pp_t_eqv Prop v
            (pp_t_T6_diagonal_fun_prime_operator \<acute> p)
            (pp_t_quantified_fun_prime_operator \<acute> p))"
      unfolding pp_t_eqv.simps
      using pp_t_eval_T6_diagonal_fun_prime_operator_holds
        pp_t_quantified_fun_prime_operator_holds
        pp_t_fun_prime_stabilizes predicates
      by blast
  qed
  show "pp_t_T6_diagonal_fun_prime_operator =
      pp_t_quantified_fun_prime_operator"
    using pp_t_root_eqv_iff_eq[
      OF pp_t_T6_diagonal_fun_prime_operator_in_domain
        pp_t_quantified_fun_prime_operator_in_domain]
      root_eqv by blast
qed

lemma pp_t_fun_prime_stock_J_holds_iff:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_quantified_fun_prime_operator \<acute> q) w
    \<longleftrightarrow>
    pp_t_fun_prime_predicate
      pp_t_fun_prime_unary_pure w q"
  using pp_t_quantified_fun_prime_operator_holds[OF q, of w]
    pp_t_fun_prime_stabilizes[OF q, of w]
  by blast

lemma pp_t_fun_prime_constant_operator_is_pure:
  "pp_t_fun_prime_unary_pure w (pp_t_constant_operator b)"
proof (cases b)
  case False
  show ?thesis
    apply (subst False)
    unfolding pp_t_fun_prime_unary_pure_def
      pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain]
    by blast
next
  case True
  show ?thesis
    apply (subst True)
    unfolding pp_t_fun_prime_unary_pure_def
      pp_t_quantified_unary_pure_classes
    using pp_t_eqv_reflexive[
      OF pp_t_constant_operator_in_domain]
    by blast
qed

lemma pp_t_fun_prime_representation_at_J:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) w"
    and pure_X: "pp_t_fun_prime_unary_pure w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_eqv pp_t_constants_unary_type
    w X (pp_t_constant_operator b)"
proof -
  have J_predicate:
      "pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w q"
    using pp_t_fun_prime_stock_J_holds_iff[OF q, of w] Jq
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
      pure_X pp_t_fun_prime_constant_operator_is_pure agreement
    unfolding pp_t_fun_prime_predicate_def
    by blast
qed

lemma pp_t_fun_prime_representation_value:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) w"
    and pure_X: "pp_t_fun_prime_unary_pure w X"
    and p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
    and p_as_b: "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows "pp_t_holds (X \<acute> p) w = b"
proof -
  have operators:
      "pp_t_eqv pp_t_constants_unary_type
        w X (pp_t_constant_operator b)"
    by (rule pp_t_fun_prime_representation_at_J[
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

lemma pp_t_fun_prime_T6_false_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and false_p:
      "pp_t_eqv Prop w p (pp_zf_truth False)"
  shows "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> p) w"
proof -
  have semantic:
      "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> p) w
      \<longleftrightarrow>
      (\<forall>X.
        Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
        (\<forall>q.
          Elem q (pp_t_domain Prop) \<longrightarrow>
          (pp_t_fun_prime_unary_pure w X
            \<and> pp_t_holds
              (pp_t_quantified_fun_prime_operator \<acute> q) w
            \<and> pp_t_eqv Prop w p (X \<acute> q))
          \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w))"
    by (rule pp_t_fun_prime_T6_operator_holds[OF p])
  show ?thesis
  proof (rule iffD2[OF semantic], intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_fun_prime_unary_pure w X \<and>
         pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w \<and>
         pp_t_eqv Prop w p (X \<acute> q)"
    have pure_X: "pp_t_fun_prime_unary_pure w X"
      using antecedent by blast
    have Jq:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w"
      using antecedent by blast
    have p_as_Xq: "pp_t_eqv Prop w p (X \<acute> q)"
      using antecedent by blast
    show "\<not> pp_t_holds (X \<acute> p) w"
      using pp_t_fun_prime_representation_value[
        OF p q X Jq pure_X p_as_Xq false_p]
      by simp
  qed
qed

lemma pp_t_fun_prime_T6_true_input:
  assumes p: "Elem p (pp_t_domain Prop)"
    and true_p:
      "pp_t_eqv Prop w p (pp_zf_truth True)"
    and witness:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w"
  shows "\<not> pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> p) w"
proof
  assume Dp:
      "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> p) w"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) w"
    using witness by blast
  let ?K = "pp_t_constant_operator True"
  have Kq: "?K \<acute> q = pp_zf_truth True"
    by (rule pp_t_constant_operator_apply[OF q])
  have antecedent:
      "pp_t_fun_prime_unary_pure w ?K
        \<and> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w
        \<and> pp_t_eqv Prop w p (?K \<acute> q)"
    using pp_t_fun_prime_constant_operator_is_pure Jq true_p
    unfolding Kq by blast
  have not_Kp: "\<not> pp_t_holds (?K \<acute> p) w"
    using pp_t_fun_prime_T6_operator_holds[OF p, of w]
      Dp pp_t_constant_operator_in_domain q antecedent
    by blast
  show False
    using not_Kp pp_t_constant_operator_holds[OF p, of True w]
    by simp
qed

subsection \<open>An explicit fun-prime witness in every cone\<close>

definition pp_t_fun_prime_probe :: "bool list \<Rightarrow> ZF" where
  "pp_t_fun_prime_probe w =
    pp_t_prop
      (\<lambda>v. prefix (w @ [False]) v \<or> v = w @ [True])"

lemma pp_t_fun_prime_probe_in_domain:
  "Elem (pp_t_fun_prime_probe w) (pp_t_domain Prop)"
  unfolding pp_t_fun_prime_probe_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_fun_prime_probe_holds[simp]:
  "pp_t_holds (pp_t_fun_prime_probe w) v
    \<longleftrightarrow>
    prefix (w @ [False]) v \<or> v = w @ [True]"
  by (simp add: pp_t_fun_prime_probe_def)

lemma pp_t_fun_prime_probe_point_values:
  "\<not> pp_t_holds (pp_t_fun_prime_probe w) w"
  "pp_t_holds (pp_t_fun_prime_probe w) (w @ [False])"
  "pp_t_holds (pp_t_fun_prime_probe w) (w @ [True])"
  "\<not> pp_t_holds
    (pp_t_fun_prime_probe w) (w @ [True, False])"
  by (auto simp: prefix_def)

lemma pp_t_fun_prime_probe_modal_values:
  "\<not> pp_t_eqv Prop w
      (pp_t_fun_prime_probe w) (pp_zf_truth True)"
  "pp_t_eqv Prop (w @ [False])
      (pp_t_fun_prime_probe w) (pp_zf_truth True)"
  "\<not> pp_t_eqv Prop (w @ [True])
      (pp_t_fun_prime_probe w) (pp_zf_truth True)"
  "\<not> pp_t_eqv Prop (w @ [True, False])
      (pp_t_fun_prime_probe w) (pp_zf_truth True)"
  "\<not> pp_t_eqv Prop w
      (pp_t_fun_prime_probe w) (pp_zf_truth False)"
  "\<not> pp_t_eqv Prop (w @ [False])
      (pp_t_fun_prime_probe w) (pp_zf_truth False)"
  "\<not> pp_t_eqv Prop (w @ [True])
      (pp_t_fun_prime_probe w) (pp_zf_truth False)"
  "pp_t_eqv Prop (w @ [True, False])
      (pp_t_fun_prime_probe w) (pp_zf_truth False)"
  unfolding pp_t_eqv.simps
  by (auto simp: prefix_def)

definition pp_t_fun_prime_probe_signature ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool list"
where
  "pp_t_fun_prime_probe_signature w F = [
    pp_t_holds (F \<acute> pp_t_fun_prime_probe w) w,
    pp_t_holds (F \<acute> pp_t_fun_prime_probe w) (w @ [False]),
    pp_t_holds (F \<acute> pp_t_fun_prime_probe w) (w @ [True]),
    pp_t_holds (F \<acute> pp_t_fun_prime_probe w)
      (w @ [True, False])]"

lemma pp_t_fun_prime_probe_signatures:
  "pp_t_fun_prime_probe_signature w pp_t_identity_operator =
    [False, True, True, False]"
  "pp_t_fun_prime_probe_signature w pp_t_negation_operator =
    [True, False, False, True]"
  "pp_t_fun_prime_probe_signature w (pp_t_constant_operator True) =
    [True, True, True, True]"
  "pp_t_fun_prime_probe_signature w (pp_t_constant_operator False) =
    [False, False, False, False]"
  "pp_t_fun_prime_probe_signature w pp_t_necessity_operator =
    [False, True, False, False]"
  "pp_t_fun_prime_probe_signature w pp_t_possibility_operator =
    [True, True, True, False]"
  "pp_t_fun_prime_probe_signature w pp_t_necessary_falsity_operator =
    [False, False, False, True]"
  "pp_t_fun_prime_probe_signature w pp_t_possible_falsity_operator =
    [True, False, True, True]"
proof -
  have p:
      "Elem (pp_t_fun_prime_probe w) (pp_t_domain Prop)"
    by (rule pp_t_fun_prime_probe_in_domain)
  note points = pp_t_fun_prime_probe_point_values[of w]
  note modal = pp_t_fun_prime_probe_modal_values[of w]
  have necessity_values:
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_fun_prime_probe w) w"
      "pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [False])"
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True])"
      "\<not> pp_t_holds
        (pp_t_necessity_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True, False])"
    using pp_t_necessity_operator_holds[OF p]
      modal(1-4) by blast+
  have possibility_values:
      "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w) w"
      "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [False])"
      "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True])"
      "\<not> pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True, False])"
  proof -
    show "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w) w"
      unfolding pp_t_possibility_operator_holds[OF p]
      by (rule exI[of _ "w @ [False]"]) simp
    show "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [False])"
      unfolding pp_t_possibility_operator_holds[OF p]
      by (rule exI[of _ "w @ [False]"]) simp
    show "pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True])"
      unfolding pp_t_possibility_operator_holds[OF p]
      by (rule exI[of _ "w @ [True]"]) simp
    show "\<not> pp_t_holds
        (pp_t_possibility_operator \<acute> pp_t_fun_prime_probe w)
        (w @ [True, False])"
      unfolding pp_t_possibility_operator_holds[OF p]
      by (auto simp: prefix_def)
  qed
  have necessary_falsity_values:
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute>
          pp_t_fun_prime_probe w) w"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [False])"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [True])"
      "pp_t_holds
        (pp_t_necessary_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [True, False])"
    using pp_t_necessary_falsity_operator_holds[OF p]
      modal(5-8) by blast+
  have possible_falsity_values:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_fun_prime_probe w) w"
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [False])"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [True])"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_fun_prime_probe w) (w @ [True, False])"
    using pp_t_possible_falsity_operator_holds[OF p]
      modal(1-4) by blast+
  show "pp_t_fun_prime_probe_signature w pp_t_identity_operator =
      [False, True, True, False]"
    unfolding pp_t_fun_prime_probe_signature_def
    using points p
    by (simp add: pp_t_identity_operator_def Lambda_app)
  show "pp_t_fun_prime_probe_signature w pp_t_negation_operator =
      [True, False, False, True]"
    unfolding pp_t_fun_prime_probe_signature_def
    using points pp_t_negation_operator_holds[OF p]
    by blast
  show "pp_t_fun_prime_probe_signature w
      (pp_t_constant_operator True) =
      [True, True, True, True]"
    unfolding pp_t_fun_prime_probe_signature_def
    using pp_t_constant_operator_holds[OF p, of True]
    by simp
  show "pp_t_fun_prime_probe_signature w
      (pp_t_constant_operator False) =
      [False, False, False, False]"
    unfolding pp_t_fun_prime_probe_signature_def
    using pp_t_constant_operator_holds[OF p, of False]
    by simp
  show "pp_t_fun_prime_probe_signature w pp_t_necessity_operator =
      [False, True, False, False]"
    unfolding pp_t_fun_prime_probe_signature_def
    using necessity_values by simp
  show "pp_t_fun_prime_probe_signature w pp_t_possibility_operator =
      [True, True, True, False]"
    unfolding pp_t_fun_prime_probe_signature_def
    using possibility_values by simp
  show "pp_t_fun_prime_probe_signature w
      pp_t_necessary_falsity_operator =
      [False, False, False, True]"
    unfolding pp_t_fun_prime_probe_signature_def
    using necessary_falsity_values by simp
  show "pp_t_fun_prime_probe_signature w
      pp_t_possible_falsity_operator =
      [True, False, True, True]"
    unfolding pp_t_fun_prime_probe_signature_def
    using possible_falsity_values by simp
qed

definition pp_t_fun_prime_probe_representatives :: "ZF set" where
  "pp_t_fun_prime_probe_representatives = {
    pp_t_identity_operator,
    pp_t_negation_operator,
    pp_t_constant_operator True,
    pp_t_constant_operator False,
    pp_t_necessity_operator,
    pp_t_possibility_operator,
    pp_t_necessary_falsity_operator,
    pp_t_possible_falsity_operator}"

lemma pp_t_fun_prime_probe_representative_in_domain:
  assumes "A \<in> pp_t_fun_prime_probe_representatives"
  shows "Elem A (pp_t_domain pp_t_constants_unary_type)"
  using assms
  unfolding pp_t_fun_prime_probe_representatives_def
  using pp_t_identity_operator_in_domain
    pp_t_negation_operator_in_domain
    pp_t_constant_operator_in_domain
    pp_t_necessity_operator_in_domain
    pp_t_possibility_operator_in_domain
    pp_t_necessary_falsity_operator_in_domain
    pp_t_possible_falsity_operator_in_domain
  by blast

lemma pp_t_fun_prime_probe_representative:
  assumes pure: "pp_t_quantified_unary_pure w X"
  shows "\<exists>A \<in> pp_t_fun_prime_probe_representatives.
    pp_t_eqv pp_t_constants_unary_type w A X"
  using pure
  unfolding pp_t_quantified_unary_pure_classes
    pp_t_fun_prime_probe_representatives_def
  by blast

lemma pp_t_fun_prime_probe_representatives_separated:
  assumes A: "A \<in> pp_t_fun_prime_probe_representatives"
    and B: "B \<in> pp_t_fun_prime_probe_representatives"
    and agreement:
      "pp_t_eqv Prop w
        (A \<acute> pp_t_fun_prime_probe w)
        (B \<acute> pp_t_fun_prime_probe w)"
  shows "A = B"
proof -
  have at_root:
      "pp_t_holds (A \<acute> pp_t_fun_prime_probe w) w =
       pp_t_holds (B \<acute> pp_t_fun_prime_probe w) w"
    using pp_t_prop_eqv_at[OF agreement, of w] by simp
  have at_left:
      "pp_t_holds (A \<acute> pp_t_fun_prime_probe w) (w @ [False]) =
       pp_t_holds (B \<acute> pp_t_fun_prime_probe w) (w @ [False])"
    using pp_t_prop_eqv_at[
      OF agreement, of "w @ [False]"] by simp
  have at_right:
      "pp_t_holds (A \<acute> pp_t_fun_prime_probe w) (w @ [True]) =
       pp_t_holds (B \<acute> pp_t_fun_prime_probe w) (w @ [True])"
    using pp_t_prop_eqv_at[
      OF agreement, of "w @ [True]"] by simp
  have at_right_left:
      "pp_t_holds
          (A \<acute> pp_t_fun_prime_probe w) (w @ [True, False]) =
       pp_t_holds
          (B \<acute> pp_t_fun_prime_probe w) (w @ [True, False])"
    using pp_t_prop_eqv_at[
      OF agreement, of "w @ [True, False]"] by simp
  have signatures:
      "pp_t_fun_prime_probe_signature w A =
       pp_t_fun_prime_probe_signature w B"
    unfolding pp_t_fun_prime_probe_signature_def
    using at_root at_left at_right at_right_left by simp
  show ?thesis
    using A B signatures pp_t_fun_prime_probe_signatures[of w]
    unfolding pp_t_fun_prime_probe_representatives_def
    by auto
qed

lemma pp_t_fun_prime_probe_is_base_fun_prime:
  "pp_t_fun_prime_predicate pp_t_quantified_unary_pure
    w (pp_t_fun_prime_probe w)"
proof (unfold pp_t_fun_prime_predicate_def, intro allI impI)
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and pure:
      "pp_t_quantified_unary_pure w X
        \<and> pp_t_quantified_unary_pure w Y"
    and agreement:
      "pp_t_eqv Prop w
        (X \<acute> pp_t_fun_prime_probe w)
        (Y \<acute> pp_t_fun_prime_probe w)"
  obtain A where A_rep:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    using pp_t_fun_prime_probe_representative[OF pure[THEN conjunct1]]
    by blast
  obtain B where B_rep:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and BY:
      "pp_t_eqv pp_t_constants_unary_type w B Y"
    using pp_t_fun_prime_probe_representative[OF pure[THEN conjunct2]]
    by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[OF A_rep])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[OF B_rep])
  have probe: "Elem (pp_t_fun_prime_probe w) (pp_t_domain Prop)"
    by (rule pp_t_fun_prime_probe_in_domain)
  have A_X:
      "pp_t_eqv Prop w
        (A \<acute> pp_t_fun_prime_probe w)
        (X \<acute> pp_t_fun_prime_probe w)"
    by (rule pp_t_app_respects[
      OF AX probe probe pp_t_eqv_reflexive[OF probe]])
  have B_Y:
      "pp_t_eqv Prop w
        (B \<acute> pp_t_fun_prime_probe w)
        (Y \<acute> pp_t_fun_prime_probe w)"
    by (rule pp_t_app_respects[
      OF BY probe probe pp_t_eqv_reflexive[OF probe]])
  have AB_outputs:
      "pp_t_eqv Prop w
        (A \<acute> pp_t_fun_prime_probe w)
        (B \<acute> pp_t_fun_prime_probe w)"
    using pp_t_app_closed[OF A_domain probe]
      pp_t_app_closed[OF X probe]
      pp_t_app_closed[OF Y probe]
      pp_t_app_closed[OF B_domain probe]
      A_X agreement B_Y
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have AB: "A = B"
    by (rule pp_t_fun_prime_probe_representatives_separated[
      OF A_rep B_rep AB_outputs])
  have XB:
      "pp_t_eqv pp_t_constants_unary_type w X B"
    by (rule pp_t_eqv_symmetric[OF A_domain X AX, unfolded AB])
  show "pp_t_eqv pp_t_constants_unary_type w X Y"
    using pp_t_eqv_transitive[
      OF X B_domain Y XB BY] .
qed

theorem pp_t_fun_prime_probe_is_fun_prime:
  "pp_t_fun_prime_predicate pp_t_fun_prime_unary_pure
    w (pp_t_fun_prime_probe w)"
  using pp_t_fun_prime_stabilizes[
    OF pp_t_fun_prime_probe_in_domain, of w]
    pp_t_fun_prime_probe_is_base_fun_prime[of w]
  by blast

theorem pp_t_fun_prime_probe_J_holds:
  "pp_t_holds
    (pp_t_quantified_fun_prime_operator
      \<acute> pp_t_fun_prime_probe w) w"
  using pp_t_fun_prime_stock_J_holds_iff[
      OF pp_t_fun_prime_probe_in_domain, of w]
    pp_t_fun_prime_probe_is_fun_prime[of w]
  by blast

definition pp_t_fun_prime_has_witness_everywhere :: bool where
  "pp_t_fun_prime_has_witness_everywhere \<longleftrightarrow>
    (\<forall>w.
      \<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w)"

theorem pp_t_fun_prime_has_witness_everywhere:
  "pp_t_fun_prime_has_witness_everywhere"
  unfolding pp_t_fun_prime_has_witness_everywhere_def
  using pp_t_fun_prime_probe_in_domain
    pp_t_fun_prime_probe_J_holds
  by blast

lemma pp_t_fun_prime_T6_on_settled:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
    and witnesses: "pp_t_fun_prime_has_witness_everywhere"
  shows "pp_t_eqv Prop w
    (pp_t_fun_prime_T6_operator \<acute> p)
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
          (pp_t_quantified_fun_prime_operator \<acute> q) v"
    using witnesses
    unfolding pp_t_fun_prime_has_witness_everywhere_def
    by blast
  show "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> p) v
      = pp_t_holds (pp_zf_truth (\<not> b)) v"
  proof (cases b)
    case False
    have Dp:
        "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> p) v"
      using pp_t_fun_prime_T6_false_input[OF p]
        settled_v False
      by simp
    show ?thesis using Dp False by simp
  next
    case True
    have not_Dp:
        "\<not> pp_t_holds
          (pp_t_fun_prime_T6_operator \<acute> p) v"
      using pp_t_fun_prime_T6_true_input[
        OF p _ witness_v] settled_v True
      by simp
    show ?thesis using not_Dp True by simp
  qed
qed

section \<open>Reduction of diagonal absorption to three unary classes\<close>

text \<open>
  Every fun-prime proposition has a future cone on which it is settled true
  and a future cone on which it is settled false.  On those cones the T6
  diagonal exchanges truth and falsity.  These two observations exclude six
  of the nine classes in the fun-prime stock as possible collisions with the
  diagonal.  Only negation, necessary falsity, and possible falsity remain.
\<close>

lemma pp_t_fun_prime_T6_collision_transfer:
  assumes p: "Elem p (pp_t_domain Prop)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and A:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    and collision:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
  shows "pp_t_eqv Prop w
    (pp_t_fun_prime_T6_operator \<acute> p) (A \<acute> p)"
proof -
  have AX:
      "pp_t_eqv Prop w (A \<acute> p) (X \<acute> p)"
    by (rule pp_t_app_respects[
      OF representative p p pp_t_eqv_reflexive[OF p]])
  have XA:
      "pp_t_eqv Prop w (X \<acute> p) (A \<acute> p)"
    by (rule pp_t_eqv_symmetric[
      OF pp_t_app_closed[OF A p]
        pp_t_app_closed[OF X p] AX])
  show ?thesis
    by (rule pp_t_eqv_transitive[
      OF pp_t_app_closed[
          OF pp_t_fun_prime_T6_operator_in_domain p]
        pp_t_app_closed[OF X p]
        pp_t_app_closed[OF A p]
        collision XA])
qed

theorem pp_t_fun_prime_T6_collision_only_negation_like:
  assumes p: "Elem p (pp_t_domain Prop)"
    and fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and pure_X: "pp_t_fun_prime_unary_pure w X"
    and collision:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
  shows "pp_t_eqv pp_t_constants_unary_type
      w pp_t_negation_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_necessary_falsity_operator X
    \<or> pp_t_eqv pp_t_constants_unary_type
      w pp_t_possible_falsity_operator X"
proof -
  have base_fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure w p"
    using pp_t_fun_prime_stabilizes[OF p, of w]
      fun_prime by blast
  obtain u v where wu: "prefix w u"
    and p_true:
      "pp_t_eqv Prop u p (pp_zf_truth True)"
    and wv: "prefix w v"
    and p_false:
      "pp_t_eqv Prop v p (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF p base_fun_prime] by blast
  have D_true_cone:
      "pp_t_eqv Prop u
        (pp_t_fun_prime_T6_operator \<acute> p)
        (pp_zf_truth False)"
    using pp_t_fun_prime_T6_on_settled[
      OF p p_true pp_t_fun_prime_has_witness_everywhere]
    by simp
  have D_false_cone:
      "pp_t_eqv Prop v
        (pp_t_fun_prime_T6_operator \<acute> p)
        (pp_zf_truth True)"
    using pp_t_fun_prime_T6_on_settled[
      OF p p_false pp_t_fun_prime_has_witness_everywhere]
    by simp
  have not_D_u:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> p) u"
    using pp_t_prop_eqv_at[OF D_true_cone, of u] by simp
  have D_v:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> p) v"
    using pp_t_prop_eqv_at[OF D_false_cone, of v] by simp
  have p_u: "pp_t_holds p u"
    using pp_t_prop_eqv_at[OF p_true, of u] by simp
  have not_p_v: "\<not> pp_t_holds p v"
    using pp_t_prop_eqv_at[OF p_false, of v] by simp
  have collision_with:
      "\<And>A.
        Elem A (pp_t_domain pp_t_constants_unary_type) \<Longrightarrow>
        pp_t_eqv pp_t_constants_unary_type w A X \<Longrightarrow>
        pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p) (A \<acute> p)"
    using pp_t_fun_prime_T6_collision_transfer[
      OF p X _ _ collision] by blast
  from pure_X consider
      (old) "pp_t_quantified_unary_pure w X"
    | (fun_prime_operator)
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_quantified_fun_prime_operator X"
    unfolding pp_t_fun_prime_unary_pure_def by blast
  then show ?thesis
  proof cases
    case old
    from old consider
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
      have at_u:
          "pp_t_holds
              (pp_t_fun_prime_T6_operator \<acute> p) u
            \<longleftrightarrow>
           pp_t_holds (pp_t_identity_operator \<acute> p) u"
        using pp_t_prop_eqv_at[
          OF collision_with[
            OF pp_t_identity_operator_in_domain identity] wu] .
      show ?thesis
        using not_D_u p_u at_u p
        by (simp add: pp_t_identity_operator_def Lambda_app)
    next
      case negation
      show ?thesis using negation by blast
    next
      case truth
      have at_u:
          "pp_t_holds
              (pp_t_fun_prime_T6_operator \<acute> p) u
            \<longleftrightarrow>
           pp_t_holds (pp_t_constant_operator True \<acute> p) u"
        using pp_t_prop_eqv_at[
          OF collision_with[
            OF pp_t_constant_operator_in_domain truth] wu] .
      show ?thesis
        using not_D_u at_u
          pp_t_constant_operator_holds[OF p, of True u]
        by blast
    next
      case falsity
      have at_v:
          "pp_t_holds
              (pp_t_fun_prime_T6_operator \<acute> p) v
            \<longleftrightarrow>
           pp_t_holds (pp_t_constant_operator False \<acute> p) v"
        using pp_t_prop_eqv_at[
          OF collision_with[
            OF pp_t_constant_operator_in_domain falsity] wv] .
      show ?thesis
        using D_v at_v
          pp_t_constant_operator_holds[OF p, of False v]
        by blast
    next
      case necessity
      have at_u:
          "pp_t_holds
              (pp_t_fun_prime_T6_operator \<acute> p) u
            \<longleftrightarrow>
           pp_t_holds (pp_t_necessity_operator \<acute> p) u"
        using pp_t_prop_eqv_at[
          OF collision_with[
            OF pp_t_necessity_operator_in_domain necessity] wu] .
      have box_p_u:
          "pp_t_holds (pp_t_necessity_operator \<acute> p) u"
        using pp_t_necessity_operator_holds[OF p, of u]
          p_true by blast
      show ?thesis using not_D_u at_u box_p_u by blast
    next
      case possibility
      have at_u:
          "pp_t_holds
              (pp_t_fun_prime_T6_operator \<acute> p) u
            \<longleftrightarrow>
           pp_t_holds (pp_t_possibility_operator \<acute> p) u"
        using pp_t_prop_eqv_at[
          OF collision_with[
            OF pp_t_possibility_operator_in_domain possibility] wu] .
      have diamond_p_u:
          "pp_t_holds (pp_t_possibility_operator \<acute> p) u"
        unfolding pp_t_possibility_operator_holds[OF p]
        using p_u by blast
      show ?thesis using not_D_u at_u diamond_p_u by blast
    next
      case necessary_falsity
      show ?thesis using necessary_falsity by blast
    next
      case possible_falsity
      show ?thesis using possible_falsity by blast
    qed
  next
    case fun_prime_operator
    have at_v:
        "pp_t_holds
            (pp_t_fun_prime_T6_operator \<acute> p) v
          \<longleftrightarrow>
         pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> p) v"
      using pp_t_prop_eqv_at[
        OF collision_with[
          OF pp_t_quantified_fun_prime_operator_in_domain
            fun_prime_operator] wv] .
    have not_J_v:
        "\<not> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> p) v"
      by (rule pp_t_quantified_fun_prime_false_on_settled[
        OF p p_false])
    show ?thesis using D_v at_v not_J_v by blast
  qed
qed

definition pp_t_T6_diagonal_cross_absorption :: bool where
  "pp_t_T6_diagonal_cross_absorption \<longleftrightarrow>
    (\<forall>w p X.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p \<longrightarrow>
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      pp_t_fun_prime_unary_pure w X \<longrightarrow>
      pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)
      \<longrightarrow>
      pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X)"

lemma pp_t_T6_diagonal_absorbs_fun_prime_iff_cross:
  "pp_t_T6_diagonal_absorbs_fun_prime
    \<longleftrightarrow> pp_t_T6_diagonal_cross_absorption"
proof
  assume absorption: "pp_t_T6_diagonal_absorbs_fun_prime"
  show "pp_t_T6_diagonal_cross_absorption"
    unfolding pp_t_T6_diagonal_cross_absorption_def
  proof (intro allI impI)
    fix w p X
    assume p: "Elem p (pp_t_domain Prop)"
      and old_fun_prime:
        "pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p"
      and X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and old_X: "pp_t_fun_prime_unary_pure w X"
      and collision:
        "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
    have new_fun_prime:
        "pp_t_fun_prime_predicate
          pp_t_T6_diagonal_unary_pure w p"
      using absorption p old_fun_prime
      unfolding pp_t_T6_diagonal_absorbs_fun_prime_def
      by blast
    have new_D:
        "pp_t_T6_diagonal_unary_pure
          w pp_t_fun_prime_T6_operator"
      unfolding pp_t_T6_diagonal_unary_pure_def
      using pp_t_eqv_reflexive[
        OF pp_t_fun_prime_T6_operator_in_domain]
      by blast
    have new_X: "pp_t_T6_diagonal_unary_pure w X"
      using old_X
      unfolding pp_t_T6_diagonal_unary_pure_def by blast
    show "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X"
      using new_fun_prime
        pp_t_fun_prime_T6_operator_in_domain X
        new_D new_X collision
      unfolding pp_t_fun_prime_predicate_def
      by blast
  qed
next
  assume cross: "pp_t_T6_diagonal_cross_absorption"
  show "pp_t_T6_diagonal_absorbs_fun_prime"
    unfolding pp_t_T6_diagonal_absorbs_fun_prime_def
  proof (intro allI impI)
    fix w p
    assume p: "Elem p (pp_t_domain Prop)"
      and old_fun_prime:
        "pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p"
    show "pp_t_fun_prime_predicate
        pp_t_T6_diagonal_unary_pure w p"
      unfolding pp_t_fun_prime_predicate_def
    proof (intro allI impI)
      fix X Y
      assume X: "Elem X
          (pp_t_domain pp_t_constants_unary_type)"
        and Y: "Elem Y
          (pp_t_domain pp_t_constants_unary_type)"
        and new:
          "pp_t_T6_diagonal_unary_pure w X
            \<and> pp_t_T6_diagonal_unary_pure w Y"
        and outputs:
          "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
      have X_cases:
          "pp_t_fun_prime_unary_pure w X
            \<or> pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator X"
        using new
        unfolding pp_t_T6_diagonal_unary_pure_def by blast
      have Y_cases:
          "pp_t_fun_prime_unary_pure w Y
            \<or> pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator Y"
        using new
        unfolding pp_t_T6_diagonal_unary_pure_def by blast
      have app_D_X:
          "pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator X
            \<Longrightarrow>
           pp_t_eqv Prop w
              (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
        by (rule pp_t_app_respects[
          OF _ p p pp_t_eqv_reflexive[OF p]])
      have app_D_Y:
          "pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator Y
            \<Longrightarrow>
           pp_t_eqv Prop w
              (pp_t_fun_prime_T6_operator \<acute> p) (Y \<acute> p)"
        by (rule pp_t_app_respects[
          OF _ p p pp_t_eqv_reflexive[OF p]])
      from X_cases consider
          (old_X) "pp_t_fun_prime_unary_pure w X"
        | (added_X)
            "pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator X"
        by blast
      then show "pp_t_eqv pp_t_constants_unary_type w X Y"
      proof cases
        case old_X
        from Y_cases consider
            (old_Y) "pp_t_fun_prime_unary_pure w Y"
          | (added_Y)
              "pp_t_eqv pp_t_constants_unary_type
                w pp_t_fun_prime_T6_operator Y"
          by blast
        then show ?thesis
        proof cases
          case old_Y
          show ?thesis
            using old_fun_prime X Y old_X old_Y outputs
            unfolding pp_t_fun_prime_predicate_def by blast
        next
          case added_Y
          have D_Y:
              "pp_t_eqv Prop w
                (pp_t_fun_prime_T6_operator \<acute> p) (Y \<acute> p)"
            by (rule app_D_Y[OF added_Y])
          have D_X_output:
              "pp_t_eqv Prop w
                (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
            using pp_t_app_closed[
                OF pp_t_fun_prime_T6_operator_in_domain p]
              pp_t_app_closed[OF X p]
              pp_t_app_closed[OF Y p]
              D_Y outputs
            by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
          have D_X_operator:
              "pp_t_eqv pp_t_constants_unary_type
                w pp_t_fun_prime_T6_operator X"
            using cross p old_fun_prime X old_X D_X_output
            unfolding pp_t_T6_diagonal_cross_absorption_def
            by blast
          have X_D:
              "pp_t_eqv pp_t_constants_unary_type
                w X pp_t_fun_prime_T6_operator"
            by (rule pp_t_eqv_symmetric[
              OF pp_t_fun_prime_T6_operator_in_domain X D_X_operator])
          show ?thesis
            by (rule pp_t_eqv_transitive[
              OF X pp_t_fun_prime_T6_operator_in_domain Y
                X_D added_Y])
        qed
      next
        case added_X
        from Y_cases consider
            (old_Y) "pp_t_fun_prime_unary_pure w Y"
          | (added_Y)
              "pp_t_eqv pp_t_constants_unary_type
                w pp_t_fun_prime_T6_operator Y"
          by blast
        then show ?thesis
        proof cases
          case old_Y
          have D_X:
              "pp_t_eqv Prop w
                (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
            by (rule app_D_X[OF added_X])
          have D_Y_output:
              "pp_t_eqv Prop w
                (pp_t_fun_prime_T6_operator \<acute> p) (Y \<acute> p)"
            using pp_t_app_closed[
                OF pp_t_fun_prime_T6_operator_in_domain p]
              pp_t_app_closed[OF X p]
              pp_t_app_closed[OF Y p]
              D_X outputs
            by (meson pp_t_eqv_transitive)
          have D_Y_operator:
              "pp_t_eqv pp_t_constants_unary_type
                w pp_t_fun_prime_T6_operator Y"
            using cross p old_fun_prime Y old_Y D_Y_output
            unfolding pp_t_T6_diagonal_cross_absorption_def
            by blast
          have X_D:
              "pp_t_eqv pp_t_constants_unary_type
                w X pp_t_fun_prime_T6_operator"
            by (rule pp_t_eqv_symmetric[
              OF pp_t_fun_prime_T6_operator_in_domain X added_X])
          show ?thesis
            by (rule pp_t_eqv_transitive[
              OF X pp_t_fun_prime_T6_operator_in_domain Y
                X_D D_Y_operator])
        next
          case added_Y
          have X_D:
              "pp_t_eqv pp_t_constants_unary_type
                w X pp_t_fun_prime_T6_operator"
            by (rule pp_t_eqv_symmetric[
              OF pp_t_fun_prime_T6_operator_in_domain X added_X])
          show ?thesis
            by (rule pp_t_eqv_transitive[
              OF X pp_t_fun_prime_T6_operator_in_domain Y
                X_D added_Y])
        qed
      qed
    qed
  qed
qed

definition pp_t_T6_diagonal_three_class_absorption :: bool where
  "pp_t_T6_diagonal_three_class_absorption \<longleftrightarrow>
    (\<forall>w p.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p \<longrightarrow>
      (pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_negation_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator pp_t_negation_operator)
      \<and>
      (pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_necessary_falsity_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_necessary_falsity_operator)
      \<and>
      (pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_possible_falsity_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_possible_falsity_operator))"

theorem pp_t_T6_diagonal_cross_absorption_iff_three_classes:
  "pp_t_T6_diagonal_cross_absorption
    \<longleftrightarrow> pp_t_T6_diagonal_three_class_absorption"
proof
  assume cross: "pp_t_T6_diagonal_cross_absorption"
  show "pp_t_T6_diagonal_three_class_absorption"
    unfolding pp_t_T6_diagonal_three_class_absorption_def
  proof (intro allI impI)
    fix w p
    assume p: "Elem p (pp_t_domain Prop)"
      and fun_prime:
        "pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p"
    show "(pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_negation_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator pp_t_negation_operator)
        \<and>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_necessary_falsity_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_necessary_falsity_operator)
        \<and>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_possible_falsity_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_possible_falsity_operator)"
    proof (intro conjI)
    show "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_negation_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator pp_t_negation_operator"
      using cross p fun_prime pp_t_negation_operator_in_domain
      unfolding pp_t_T6_diagonal_cross_absorption_def
        pp_t_fun_prime_unary_pure_def
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_negation_operator_in_domain]
      by blast
    show "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_necessary_falsity_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_necessary_falsity_operator"
      using cross p fun_prime
        pp_t_necessary_falsity_operator_in_domain
      unfolding pp_t_T6_diagonal_cross_absorption_def
        pp_t_fun_prime_unary_pure_def
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_necessary_falsity_operator_in_domain]
      by blast
    show "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_possible_falsity_operator \<acute> p)
        \<longrightarrow>
        pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_possible_falsity_operator"
      using cross p fun_prime
        pp_t_possible_falsity_operator_in_domain
      unfolding pp_t_T6_diagonal_cross_absorption_def
        pp_t_fun_prime_unary_pure_def
        pp_t_quantified_unary_pure_classes
      using pp_t_eqv_reflexive[
        OF pp_t_possible_falsity_operator_in_domain]
      by blast
    qed
  qed
next
  assume three: "pp_t_T6_diagonal_three_class_absorption"
  show "pp_t_T6_diagonal_cross_absorption"
    unfolding pp_t_T6_diagonal_cross_absorption_def
  proof (intro allI impI)
    fix w p X
    assume p: "Elem p (pp_t_domain Prop)"
      and fun_prime:
        "pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p"
      and X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and pure_X: "pp_t_fun_prime_unary_pure w X"
      and collision:
        "pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p) (X \<acute> p)"
    have three_at_p:
        "(pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_negation_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator pp_t_negation_operator)
        \<and>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_necessary_falsity_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_necessary_falsity_operator)
        \<and>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_possible_falsity_operator \<acute> p)
          \<longrightarrow>
          pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_possible_falsity_operator)"
      using three p fun_prime
      unfolding pp_t_T6_diagonal_three_class_absorption_def
      by blast
    have cases:
        "pp_t_eqv pp_t_constants_unary_type
            w pp_t_negation_operator X
        \<or> pp_t_eqv pp_t_constants_unary_type
            w pp_t_necessary_falsity_operator X
        \<or> pp_t_eqv pp_t_constants_unary_type
            w pp_t_possible_falsity_operator X"
      by (rule pp_t_fun_prime_T6_collision_only_negation_like[
        OF p fun_prime X pure_X collision])
    then show "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X"
    proof
      assume negation:
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_negation_operator X"
      have D_negation_output:
          "pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_negation_operator \<acute> p)"
        by (rule pp_t_fun_prime_T6_collision_transfer[
          OF p X pp_t_negation_operator_in_domain
            negation collision])
      have D_negation:
          "pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator pp_t_negation_operator"
        using three_at_p D_negation_output by blast
      show ?thesis
        by (rule pp_t_eqv_transitive[
          OF pp_t_fun_prime_T6_operator_in_domain
            pp_t_negation_operator_in_domain X
            D_negation negation])
    next
      assume other:
          "pp_t_eqv pp_t_constants_unary_type
              w pp_t_necessary_falsity_operator X
          \<or> pp_t_eqv pp_t_constants_unary_type
              w pp_t_possible_falsity_operator X"
      then show ?thesis
      proof
        assume necessary_falsity:
            "pp_t_eqv pp_t_constants_unary_type
              w pp_t_necessary_falsity_operator X"
        have D_necessary_falsity_output:
            "pp_t_eqv Prop w
              (pp_t_fun_prime_T6_operator \<acute> p)
              (pp_t_necessary_falsity_operator \<acute> p)"
          by (rule pp_t_fun_prime_T6_collision_transfer[
            OF p X pp_t_necessary_falsity_operator_in_domain
              necessary_falsity collision])
        have D_necessary_falsity:
            "pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator
                pp_t_necessary_falsity_operator"
          using three_at_p D_necessary_falsity_output by blast
        show ?thesis
          by (rule pp_t_eqv_transitive[
            OF pp_t_fun_prime_T6_operator_in_domain
              pp_t_necessary_falsity_operator_in_domain X
              D_necessary_falsity necessary_falsity])
      next
        assume possible_falsity:
            "pp_t_eqv pp_t_constants_unary_type
              w pp_t_possible_falsity_operator X"
        have D_possible_falsity_output:
            "pp_t_eqv Prop w
              (pp_t_fun_prime_T6_operator \<acute> p)
              (pp_t_possible_falsity_operator \<acute> p)"
          by (rule pp_t_fun_prime_T6_collision_transfer[
            OF p X pp_t_possible_falsity_operator_in_domain
              possible_falsity collision])
        have D_possible_falsity:
            "pp_t_eqv pp_t_constants_unary_type
              w pp_t_fun_prime_T6_operator
                pp_t_possible_falsity_operator"
          using three_at_p D_possible_falsity_output by blast
        show ?thesis
          by (rule pp_t_eqv_transitive[
            OF pp_t_fun_prime_T6_operator_in_domain
              pp_t_possible_falsity_operator_in_domain X
              D_possible_falsity possible_falsity])
      qed
    qed
  qed
qed

theorem pp_t_T6_diagonal_absorbs_fun_prime_iff_three_classes:
  "pp_t_T6_diagonal_absorbs_fun_prime
    \<longleftrightarrow> pp_t_T6_diagonal_three_class_absorption"
  using pp_t_T6_diagonal_absorbs_fun_prime_iff_cross
    pp_t_T6_diagonal_cross_absorption_iff_three_classes
  by blast

corollary pp_t_T6_diagonal_three_noncollisions_imply_absorption:
  assumes negation:
      "\<And>w p.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p \<Longrightarrow>
        \<not> pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_negation_operator \<acute> p)"
    and necessary_falsity:
      "\<And>w p.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p \<Longrightarrow>
        \<not> pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_necessary_falsity_operator \<acute> p)"
    and possible_falsity:
      "\<And>w p.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p \<Longrightarrow>
        \<not> pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_possible_falsity_operator \<acute> p)"
  shows "pp_t_T6_diagonal_absorbs_fun_prime"
  using negation necessary_falsity possible_falsity
    pp_t_T6_diagonal_absorbs_fun_prime_iff_three_classes
  unfolding pp_t_T6_diagonal_three_class_absorption_def
  by blast

theorem pp_t_T6_diagonal_absorption_failure_iff:
  "\<not> pp_t_T6_diagonal_absorbs_fun_prime
    \<longleftrightarrow>
    (\<exists>w p.
      Elem p (pp_t_domain Prop)
      \<and> pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure w p
      \<and>
      ((pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_negation_operator \<acute> p)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator pp_t_negation_operator)
      \<or>
      (pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_necessary_falsity_operator \<acute> p)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_necessary_falsity_operator)
      \<or>
      (pp_t_eqv Prop w
          (pp_t_fun_prime_T6_operator \<acute> p)
          (pp_t_possible_falsity_operator \<acute> p)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator
            pp_t_possible_falsity_operator)))"
  using pp_t_T6_diagonal_absorbs_fun_prime_iff_three_classes
  unfolding pp_t_T6_diagonal_three_class_absorption_def
  by blast

section \<open>Application closure forced by the diagonal\<close>

lemma pp_t_T6_diagonal_old_input:
  assumes pure_f:
      "pp_t_fun_prime_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and retained:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
        \<noteq> pp_t_constants_classifier_type"
    and pure_x:
      "pp_t_T6_diagonal_fragment_pure \<sigma> w x"
  shows "pp_t_fun_prime_fragment_pure \<sigma> w x"
proof -
  from pure_x consider
      (old)
        "pp_t_fun_prime_fragment_pure \<sigma> w x"
        "\<sigma> \<noteq> pp_t_constants_classifier_type"
    | (added)
        "\<sigma> = pp_t_constants_unary_type"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator x"
    | (classifier)
        "\<sigma> = pp_t_constants_classifier_type"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_T6_diagonal_stock_classifier x"
    unfolding pp_t_T6_diagonal_fragment_pure_def
    by blast
  then show ?thesis
  proof cases
    case old
    then show ?thesis by blast
  next
    case added
    have no_retained:
        "\<not> pp_t_fun_prime_fragment_pure
          (pp_t_constants_unary_type \<rightarrow>\<^sub>o \<tau>) w f
        \<or> \<tau> = Prop"
      using pure_f added
      unfolding pp_t_fun_prime_fragment_pure_def
      using pp_t_quantified_pure_function_from_unary[
        of \<tau> w f]
      by (cases \<tau>) auto
    have tau: "\<tau> = Prop"
      using no_retained pure_f added by blast
    have False
      using retained added tau by simp
    then show ?thesis by blast
  next
    case classifier
    have no_old:
        "\<not> pp_t_fun_prime_fragment_pure
          (pp_t_constants_classifier_type \<rightarrow>\<^sub>o \<tau>) w f"
      unfolding pp_t_fun_prime_fragment_pure_def
        pp_t_quantified_fragment_pure_def
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

lemma pp_t_T6_diagonal_added_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator f"
    and pure_p:
      "pp_t_T6_diagonal_fragment_pure Prop w p"
    and witnesses: "pp_t_fun_prime_has_witness_everywhere"
  shows "pp_t_T6_diagonal_fragment_pure Prop w (f \<acute> p)"
proof -
  have old_p:
      "pp_t_quantified_fragment_pure Prop w p"
    using pure_p
    unfolding pp_t_T6_diagonal_pure_Prop_iff
      pp_t_fun_prime_pure_Prop_iff .
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
  have Dp:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> p)
        (pp_zf_truth (\<not> b))"
    by (rule pp_t_fun_prime_T6_on_settled[
      OF p pb witnesses])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_fun_prime_T6_operator \<acute> p)
        (f \<acute> p)"
    by (rule pp_t_app_respects[
      OF representative p p pp_t_eqv_reflexive[OF p]])
  have result:
      "pp_t_eqv Prop w
        (pp_zf_truth (\<not> b)) (f \<acute> p)"
    using
      pp_t_app_closed[OF pp_t_fun_prime_T6_operator_in_domain p]
      pp_t_app_closed[OF f p]
      pp_t_truth_in_domain Dp applications
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have old_result:
      "pp_t_quantified_fragment_pure Prop w (f \<acute> p)"
    unfolding pp_t_quantified_pure_Prop_iff
      pp_t_possibility_pure_Prop_iff
      pp_t_necessity_pure_Prop_iff
      pp_t_binary_truth_pure_Prop_iff
      pp_t_conjunction_pure_Prop_iff
      pp_t_constant_builder_pure_Prop_iff
      pp_t_constants_fragment_pure_Prop_iff
    using result by (cases b) simp_all
  show ?thesis
    unfolding pp_t_T6_diagonal_pure_Prop_iff
      pp_t_fun_prime_pure_Prop_iff
    using old_result .
qed

lemma pp_t_T6_diagonal_unary_pure_persistent:
  assumes pure: "pp_t_T6_diagonal_unary_pure w X"
    and future: "prefix w v"
  shows "pp_t_T6_diagonal_unary_pure v X"
  using pure pp_t_eqv_persistent[OF _ future]
    pp_t_fun_prime_unary_pure_persistent[OF _ future]
  unfolding pp_t_T6_diagonal_unary_pure_def
  by blast

lemma pp_t_T6_diagonal_classifier_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_constants_classifier_type)"
    and X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and representative:
      "pp_t_eqv pp_t_constants_classifier_type
        w pp_t_T6_diagonal_stock_classifier f"
    and pure_X: "pp_t_T6_diagonal_unary_pure w X"
  shows "pp_t_T6_diagonal_fragment_pure Prop w (f \<acute> X)"
proof -
  have classifier_true:
      "pp_t_eqv Prop w
        (pp_t_T6_diagonal_stock_classifier \<acute> X)
        (pp_zf_truth True)"
    unfolding pp_t_prop_eqv_truth_iff
      pp_t_T6_diagonal_stock_classifier_def
    using pp_t_classifier_holds[
        OF X, of pp_t_T6_diagonal_unary_pure]
      pp_t_T6_diagonal_unary_pure_persistent[
        OF pure_X]
    by blast
  have applications:
      "pp_t_eqv Prop w
        (pp_t_T6_diagonal_stock_classifier \<acute> X)
        (f \<acute> X)"
    by (rule pp_t_app_respects[
      OF representative X X pp_t_eqv_reflexive[OF X]])
  have result:
      "pp_t_eqv Prop w (pp_zf_truth True) (f \<acute> X)"
    using pp_t_app_closed[
        OF pp_t_T6_diagonal_stock_classifier_in_domain X]
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
    unfolding pp_t_T6_diagonal_pure_Prop_iff
      pp_t_fun_prime_pure_Prop_iff
    using old_result .
qed

theorem pp_t_T6_diagonal_fragment_application:
  assumes witnesses: "pp_t_fun_prime_has_witness_everywhere"
    and f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_T6_diagonal_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_T6_diagonal_fragment_pure \<sigma> w x"
  shows "pp_t_T6_diagonal_fragment_pure \<tau> w (f \<acute> x)"
proof -
  from pure_f consider
      (old)
        "pp_t_fun_prime_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
        "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<noteq> pp_t_constants_classifier_type"
    | (added)
        "\<sigma> = Prop" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator f"
    | (classifier)
        "\<sigma> = pp_t_constants_unary_type" "\<tau> = Prop"
        "pp_t_eqv pp_t_constants_classifier_type
          w pp_t_T6_diagonal_stock_classifier f"
    unfolding pp_t_T6_diagonal_fragment_pure_def
    by (cases \<sigma>; cases \<tau>; auto)
  then show ?thesis
  proof cases
    case old
    have old_x:
        "pp_t_fun_prime_fragment_pure \<sigma> w x"
      by (rule pp_t_T6_diagonal_old_input[
        OF old pure_x])
    have old_result:
        "pp_t_fun_prime_fragment_pure \<tau> w (f \<acute> x)"
      by (rule pp_t_fun_prime_fragment_application[
        OF f x old(1) old_x])
    have not_classifier:
        "\<tau> \<noteq> pp_t_constants_classifier_type"
    proof
      assume tau: "\<tau> = pp_t_constants_classifier_type"
      have no_old:
          "\<not> pp_t_fun_prime_fragment_pure
            (\<sigma> \<rightarrow>\<^sub>o
              pp_t_constants_classifier_type) w f"
        unfolding pp_t_fun_prime_fragment_pure_def
          pp_t_quantified_fragment_pure_def
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
      unfolding pp_t_T6_diagonal_fragment_pure_def
      using old_result not_classifier by blast
  next
    case added
    show ?thesis
      using pp_t_T6_diagonal_added_application[
        OF _ _ added(3) _ witnesses]
        f x pure_x added
      by simp
  next
    case classifier
    have pure_unary:
        "pp_t_T6_diagonal_unary_pure w x"
      using pp_t_T6_diagonal_pure_unary_iff[
        of w x] pure_x classifier by simp
    show ?thesis
      using pp_t_T6_diagonal_classifier_application[
        OF _ _ classifier(3) pure_unary]
        f x classifier
      by simp
  qed
qed

definition pp_t_T6_diagonal_D_QLN :: bool where
  "pp_t_T6_diagonal_D_QLN \<longleftrightarrow>
    (\<forall>w r.
      Elem r (pp_t_domain Prop) \<longrightarrow>
      pp_t_moving_fundamental_at Prop w r
      \<longrightarrow>
      (((\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)
        \<longrightarrow>
        (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w))
      \<and>
       ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)
        \<longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v))))"

theorem pp_t_T6_diagonal_D_QLN_from_witnesses:
  assumes witnesses: "pp_t_fun_prime_has_witness_everywhere"
  shows "pp_t_T6_diagonal_D_QLN"
  unfolding pp_t_T6_diagonal_D_QLN_def
proof (intro allI impI)
  fix w r
  assume r: "Elem r (pp_t_domain Prop)"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
  have witness_w:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) w"
    using witnesses
    unfolding pp_t_fun_prime_has_witness_everywhere_def
    by blast
  have truth: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have truth_refl:
      "pp_t_eqv Prop w
        (pp_zf_truth True) (pp_zf_truth True)"
    by (rule pp_t_eqv_reflexive[OF truth])
  have D_truth_false:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> pp_zf_truth True) w"
    by (rule pp_t_fun_prime_T6_true_input[
      OF truth truth_refl witness_w])
  have not_universal:
      "\<not> (\<forall>q.
        Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)"
    using truth D_truth_false by blast
  let ?v = "w @ [True]"
  have future: "prefix w ?v" by simp
  have r_seed:
      "pp_t_eqv Prop w r (pp_t_moving_seed w)"
    using fundamental by simp
  have r_seed_v:
      "pp_t_eqv Prop ?v r (pp_t_moving_seed w)"
    by (rule pp_t_eqv_persistent[OF r_seed future])
  have seed_true:
      "pp_t_eqv Prop ?v
        (pp_t_moving_seed w) (pp_zf_truth True)"
    by (rule pp_t_moving_seed_true_on_left)
  have r_true:
      "pp_t_eqv Prop ?v r (pp_zf_truth True)"
    using r pp_t_moving_seed_in_domain truth
      r_seed_v seed_true
    by (meson pp_t_eqv_transitive)
  have witness_v:
      "\<exists>q.
        Elem q (pp_t_domain Prop)
        \<and> pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) ?v"
    using witnesses
    unfolding pp_t_fun_prime_has_witness_everywhere_def
    by blast
  have D_r_false:
      "\<not> pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) ?v"
    by (rule pp_t_fun_prime_T6_true_input[
      OF r r_true witness_v])
  have not_necessary:
      "\<not> (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)"
    using future D_r_false by blast
  show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w))
    \<and>
     ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v))"
  proof
    show "(\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)"
      using not_necessary by blast
    show "(\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)"
      using not_universal by blast
  qed
qed

lemma pp_t_T6_diagonal_added_class_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and representative:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
    and D_QLN: "pp_t_T6_diagonal_D_QLN"
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
  have D_rule:
      "((\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v)
        \<longrightarrow>
        (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w))
      \<and>
       ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w)
        \<longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v))"
    using D_QLN r fundamental
    unfolding pp_t_T6_diagonal_D_QLN_def by blast
  show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
  proof
    assume necessary_X:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
    have necessary_D:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume future: "prefix w v"
      have representative_v:
          "pp_t_eqv pp_t_constants_unary_type
            v pp_t_fun_prime_T6_operator X"
        by (rule pp_t_eqv_persistent[OF representative future])
      have applications:
          "pp_t_eqv Prop v
            (pp_t_fun_prime_T6_operator \<acute> r) (X \<acute> r)"
        by (rule pp_t_app_respects[
          OF representative_v r r pp_t_eqv_reflexive[OF r]])
      show "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v"
        using necessary_X future
          pp_t_prop_eqv_at[OF applications, of v]
        by blast
    qed
    have universal_D:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w"
      using D_rule necessary_D by blast
    show "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
    proof (intro allI impI)
      fix q
      assume q: "Elem q (pp_t_domain Prop)"
      have applications:
          "pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> q) (X \<acute> q)"
        by (rule pp_t_app_respects[
          OF representative q q pp_t_eqv_reflexive[OF q]])
      show "pp_t_holds (X \<acute> q) w"
        using universal_D q
          pp_t_prop_eqv_at[OF applications, of w]
        by blast
    qed
  qed
  show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
  proof
    assume universal_X:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
    have universal_D:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w"
    proof (intro allI impI)
      fix q
      assume q: "Elem q (pp_t_domain Prop)"
      have applications:
          "pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> q) (X \<acute> q)"
        by (rule pp_t_app_respects[
          OF representative q q pp_t_eqv_reflexive[OF q]])
      show "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> q) w"
        using universal_X q
          pp_t_prop_eqv_at[OF applications, of w]
        by blast
    qed
    have necessary_D:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (pp_t_fun_prime_T6_operator \<acute> r) v"
      using D_rule universal_D by blast
    show "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume future: "prefix w v"
      have representative_v:
          "pp_t_eqv pp_t_constants_unary_type
            v pp_t_fun_prime_T6_operator X"
        by (rule pp_t_eqv_persistent[OF representative future])
      have applications:
          "pp_t_eqv Prop v
            (pp_t_fun_prime_T6_operator \<acute> r) (X \<acute> r)"
        by (rule pp_t_app_respects[
          OF representative_v r r pp_t_eqv_reflexive[OF r]])
      show "pp_t_holds (X \<acute> r) v"
        using necessary_D future
          pp_t_prop_eqv_at[OF applications, of v]
        by blast
    qed
  qed
qed

lemma pp_t_T6_diagonal_pure_unary_QLN:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_T6_diagonal_fragment_pure
        pp_t_constants_unary_type w X"
    and fundamental:
      "pp_t_moving_fundamental_at Prop w r"
    and D_QLN: "pp_t_T6_diagonal_D_QLN"
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
      "pp_t_T6_diagonal_unary_pure w X"
    using pp_t_T6_diagonal_pure_unary_iff[of w X] pure
    by blast
  have classes:
      "pp_t_fun_prime_unary_pure w X
        \<or> pp_t_eqv pp_t_constants_unary_type
          w pp_t_fun_prime_T6_operator X"
    using enlarged
    unfolding pp_t_T6_diagonal_unary_pure_def .
  from classes show
    "((\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w))"
  proof
    assume old: "pp_t_fun_prime_unary_pure w X"
    have old_pure:
        "pp_t_fun_prime_fragment_pure
          pp_t_constants_unary_type w X"
      using pp_t_fun_prime_pure_unary_iff[of w X] old
      by blast
    show ?thesis
      by (rule pp_t_fun_prime_pure_unary_QLN(1)[
        OF X r old_pure fundamental])
  next
    assume added:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X"
    show ?thesis
      by (rule pp_t_T6_diagonal_added_class_QLN(1)[
        OF X r added fundamental D_QLN])
  qed
  from classes show
    "((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v))"
  proof
    assume old: "pp_t_fun_prime_unary_pure w X"
    have old_pure:
        "pp_t_fun_prime_fragment_pure
          pp_t_constants_unary_type w X"
      using pp_t_fun_prime_pure_unary_iff[of w X] old
      by blast
    show ?thesis
      by (rule pp_t_fun_prime_pure_unary_QLN(2)[
        OF X r old_pure fundamental])
  next
    assume added:
      "pp_t_eqv pp_t_constants_unary_type
        w pp_t_fun_prime_T6_operator X"
    show ?thesis
      by (rule pp_t_T6_diagonal_added_class_QLN(2)[
        OF X r added fundamental D_QLN])
  qed
qed

theorem pp_t_T6_diagonal_D_QLN:
  "pp_t_T6_diagonal_D_QLN"
  by (rule pp_t_T6_diagonal_D_QLN_from_witnesses[
    OF pp_t_fun_prime_has_witness_everywhere])

theorem pp_t_T6_diagonal_pure_unary_QLN_unconditional:
  assumes X:
      "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and pure:
      "pp_t_T6_diagonal_fragment_pure
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
  by (rule pp_t_T6_diagonal_pure_unary_QLN[
      OF X r pure fundamental pp_t_T6_diagonal_D_QLN])+

theorem pp_t_T6_diagonal_fragment_application_unconditional:
  assumes f:
      "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and pure_f:
      "pp_t_T6_diagonal_fragment_pure
        (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and pure_x:
      "pp_t_T6_diagonal_fragment_pure \<sigma> w x"
  shows "pp_t_T6_diagonal_fragment_pure \<tau> w (f \<acute> x)"
  by (rule pp_t_T6_diagonal_fragment_application[
    OF pp_t_fun_prime_has_witness_everywhere
      f x pure_f pure_x])

section \<open>Unconditional retests after the one-step enlargement\<close>

lemma pp_t_T6_diagonal_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_T6_diagonal_fragment_pure
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

lemma pp_t_T6_diagonal_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain pp_t_constants_unary_type) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_T6_diagonal_fragment_pure
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

theorem pp_t_T6_diagonal_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_T6_diagonal_unary_recombination_holds_iff
  using pp_t_T6_diagonal_pure_unary_QLN_unconditional(1)
  by blast

theorem pp_t_T6_diagonal_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_T6_diagonal_unary_exhaustion_holds_iff
  using pp_t_T6_diagonal_pure_unary_QLN_unconditional(2)
  by blast

theorem pp_t_T6_diagonal_unary_recombination_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_T6_diagonal_unary_recombination_holds by blast

theorem pp_t_T6_diagonal_unary_exhaustion_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_T6_diagonal_unary_exhaustion_holds by blast

lemma pp_t_T6_diagonal_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_T6_diagonal_fragment_pure
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_T6_diagonal_fragment_pure \<sigma> w x
        \<longrightarrow>
        pp_t_T6_diagonal_fragment_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_T6_diagonal_application_closure_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (T6DiagonalFragment.MovingTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding
      T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
      pp_t_T6_diagonal_application_closure_holds_iff
    using pp_t_T6_diagonal_fragment_application_unconditional
    by blast
qed

lemma pp_t_T6_diagonal_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
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

theorem pp_t_T6_diagonal_modalized_functionality_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (T6DiagonalFragment.MovingTreeConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding
      T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
      pp_t_T6_diagonal_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

theorem pp_t_T6_diagonal_unique_fundamental_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
  using T6DiagonalFragment.pp_t_moving_unique_fundamental_holds
  by blast

lemma pp_t_T6_diagonal_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_T6_diagonal_fragment_constants \<rho>
      pp_target_PP) w"
proof -
  have unary_classifier:
      "pp_t_classifier pp_t_constants_unary_type
        (pp_t_T6_diagonal_fragment_pure
          pp_t_constants_unary_type) =
       pp_t_T6_diagonal_stock_classifier"
    unfolding pp_t_T6_diagonal_stock_classifier_def
      pp_t_classifier_def
    by (simp add: pp_t_T6_diagonal_pure_unary_iff)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def
      pp_pure_def
    using pp_t_classifier_holds[
      OF pp_t_T6_diagonal_stock_classifier_in_domain,
      of "pp_t_T6_diagonal_fragment_pure
        pp_t_constants_classifier_type" w]
      pp_t_T6_diagonal_classifier_is_pure
    by (simp add: unary_classifier)
qed

theorem pp_t_T6_diagonal_target_PP_gvalid:
  "T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_target_PP"
  unfolding
    T6DiagonalFragment.MovingTreeConstants.TreeHenkin.gvalid_def
    T6DiagonalFragment.MovingTreeConstants.pp_t_den_def
  using pp_t_T6_diagonal_target_PP_holds by blast

end
