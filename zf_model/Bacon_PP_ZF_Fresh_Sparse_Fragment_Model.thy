theory Bacon_PP_ZF_Fresh_Sparse_Fragment_Model
  imports Bacon_PP_ZF_Tree_CEV_Soundness
begin

section \<open>A model for the fragment without logical-purity instances\<close>

text \<open>
  The finite-fragment reduction makes it useful to determine exactly which
  finite collections of Goodman's additional principles already have models.
  The interpretation below validates PP, application closure, the
  fundamentality principles, and both directions of zeroary and unary QLN.
  Its unary pure stock is empty, so the unary QLN principles hold vacuously.
  The denotation of the empty unary-stock classifier is nevertheless pure at
  the next type, so PP holds.  This isolates the logical-purity instances as
  the first nonvacuous obstacle.
\<close>

abbreviation pp_fresh_unary_type :: otype where
  "pp_fresh_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_fresh_classifier_type :: otype where
  "pp_fresh_classifier_type \<equiv>
    pp_fresh_unary_type \<rightarrow>\<^sub>o Prop"

definition pp_t_fresh_empty_unary_classifier :: ZF where
  "pp_t_fresh_empty_unary_classifier =
    pp_t_classifier pp_fresh_unary_type (\<lambda>w x. False)"

definition pp_t_fresh_sparse_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_fresh_sparse_pure \<sigma> w x \<longleftrightarrow>
    \<sigma> = pp_fresh_classifier_type
    \<and> Elem x (pp_t_domain \<sigma>)
    \<and> pp_t_eqv \<sigma> w x pp_t_fresh_empty_unary_classifier"

definition pp_t_fresh_seed :: "bool list \<Rightarrow> ZF" where
  "pp_t_fresh_seed w = pp_t_default Prop"

lemma pp_t_fresh_empty_unary_classifier_in_domain:
  "Elem pp_t_fresh_empty_unary_classifier
    (pp_t_domain pp_fresh_classifier_type)"
proof -
  have admissible:
      "pp_t_predicate_admissible pp_fresh_unary_type
        (\<lambda>w x. False)"
    by (simp add: pp_t_predicate_admissible_def)
  show ?thesis
    unfolding pp_t_fresh_empty_unary_classifier_def
    using pp_t_classifier_in_domain[OF admissible] .
qed

lemma pp_t_fresh_sparse_pure_admissible:
  "pp_t_predicate_admissible \<sigma> (pp_t_fresh_sparse_pure \<sigma>)"
proof (unfold pp_t_predicate_admissible_def, intro allI impI)
  fix w x y v
  assume x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> w x y"
    and future: "prefix w v"
  have xy_v: "pp_t_eqv \<sigma> v x y"
    using pp_t_eqv_persistent[OF xy future] .
  show "pp_t_fresh_sparse_pure \<sigma> v x =
      pp_t_fresh_sparse_pure \<sigma> v y"
  proof (cases "\<sigma> = pp_fresh_classifier_type")
    case False
    then show ?thesis
      by (simp add: pp_t_fresh_sparse_pure_def)
  next
    case True
    have classifier:
        "Elem pp_t_fresh_empty_unary_classifier
          (pp_t_domain \<sigma>)"
      using True pp_t_fresh_empty_unary_classifier_in_domain by simp
    have classifier_refl:
        "pp_t_eqv \<sigma> v pp_t_fresh_empty_unary_classifier
          pp_t_fresh_empty_unary_classifier"
      using pp_t_eqv_reflexive[OF classifier] .
    have congruence:
        "pp_t_eqv \<sigma> v x pp_t_fresh_empty_unary_classifier
          \<longleftrightarrow>
         pp_t_eqv \<sigma> v y pp_t_fresh_empty_unary_classifier"
      using pp_t_eqv_congruence[
        OF x y classifier classifier xy_v classifier_refl] .
    show ?thesis
      using True x y congruence
      by (simp add: pp_t_fresh_sparse_pure_def)
  qed
qed

lemma pp_t_fresh_seed_typed:
  "Elem (pp_t_fresh_seed w) (pp_t_domain Prop)"
  unfolding pp_t_fresh_seed_def
  by (rule pp_t_default_in_domain)

definition pp_t_fresh_sparse_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_fresh_sparse_constants =
    pp_t_seeded_internal_constants
      pp_t_fresh_sparse_pure pp_t_fresh_seed"

interpretation FreshSparseConstants:
  pp_t_constants pp_t_fresh_sparse_constants
proof
  fix c \<sigma>
  show "Elem (pp_t_fresh_sparse_constants c \<sigma>)
      (pp_t_domain \<sigma>)"
  proof (cases \<sigma>)
    case Ind
    show ?thesis
      unfolding Ind pp_t_fresh_sparse_constants_def
      using pp_t_default_in_domain[of Ind] by simp
  next
    case Prop
    show ?thesis
      unfolding Prop pp_t_fresh_sparse_constants_def
      using pp_t_default_in_domain[of Prop] by simp
  next
    case (Arr \<sigma> \<tau>)
    have pure_classifier:
        "Elem (pp_t_classifier \<sigma> (pp_t_fresh_sparse_pure \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[
        OF pp_t_fresh_sparse_pure_admissible] .
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
            "pp_t_eqv Prop v (pp_t_fresh_seed v) (pp_t_fresh_seed v)"
          using pp_t_eqv_reflexive[OF pp_t_fresh_seed_typed] .
        show "pp_t_seeded_fundamental_at pp_t_fresh_seed Prop v x =
            pp_t_seeded_fundamental_at pp_t_fresh_seed Prop v y"
          using pp_t_eqv_congruence[
            OF x y pp_t_fresh_seed_typed pp_t_fresh_seed_typed
              xy_v seed_refl]
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
            (pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_t_classifier_in_domain[OF fundamental_admissible] .
    have default:
        "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
          (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      using pp_t_default_in_domain .
    show ?thesis
      using Arr pure_classifier fun_classifier default
      by (auto simp: pp_t_fresh_sparse_constants_def)
  qed
qed

lemma pp_t_fresh_sparse_pure_Prop[simp]:
  "\<not> pp_t_fresh_sparse_pure Prop w x"
  by (simp add: pp_t_fresh_sparse_pure_def)

lemma pp_t_fresh_sparse_pure_unary[simp]:
  "\<not> pp_t_fresh_sparse_pure pp_fresh_unary_type w x"
  by (simp add: pp_t_fresh_sparse_pure_def)

lemma pp_t_fresh_sparse_unary_classifier:
  "pp_t_classifier pp_fresh_unary_type
      (pp_t_fresh_sparse_pure pp_fresh_unary_type)
    = pp_t_fresh_empty_unary_classifier"
  unfolding pp_t_fresh_empty_unary_classifier_def
    pp_t_fresh_sparse_pure_def
  by simp

lemma pp_t_fresh_sparse_classifier_is_pure:
  "pp_t_fresh_sparse_pure pp_fresh_classifier_type w
    pp_t_fresh_empty_unary_classifier"
  unfolding pp_t_fresh_sparse_pure_def
proof (intro conjI)
  show "pp_fresh_classifier_type = pp_fresh_classifier_type"
    by simp
  show "Elem pp_t_fresh_empty_unary_classifier
      (pp_t_domain pp_fresh_classifier_type)"
    by (rule pp_t_fresh_empty_unary_classifier_in_domain)
  show "pp_t_eqv pp_fresh_classifier_type w
      pp_t_fresh_empty_unary_classifier
      pp_t_fresh_empty_unary_classifier"
    using pp_t_eqv_reflexive[
      OF pp_t_fresh_empty_unary_classifier_in_domain] .
qed

lemma pp_t_fresh_eval_Pure[simp]:
  "pp_t_eval pp_t_fresh_sparse_constants \<rho> (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma> (pp_t_fresh_sparse_pure \<sigma>)"
  by (simp add: pp_t_fresh_sparse_constants_def
      pp_Pure_def pp_pure_name_def)

lemma pp_t_fresh_eval_Fun[simp]:
  "pp_t_eval pp_t_fresh_sparse_constants \<rho> (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>)"
  by (simp add: pp_t_fresh_sparse_constants_def
      pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_fresh_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_fresh_sparse_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_fresh_sparse_pure \<sigma> w
        (pp_t_eval pp_t_fresh_sparse_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_fresh_sparse_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using FreshSparseConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[
      OF argument, of "pp_t_fresh_sparse_pure \<sigma>" w]
    by simp
qed

lemma pp_t_fresh_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval pp_t_fresh_sparse_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma> w
        (pp_t_eval pp_t_fresh_sparse_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_t_eval pp_t_fresh_sparse_constants \<rho> M)
        (pp_t_domain \<sigma>)"
    using FreshSparseConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at pp_t_fresh_seed \<sigma>" w]
    by simp
qed

lemma pp_t_fresh_sparse_pure_application:
  assumes pure_function:
      "pp_t_fresh_sparse_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and argument:
      "pp_t_fresh_sparse_pure \<sigma> w x"
  shows "pp_t_fresh_sparse_pure \<tau> w (f \<acute> x)"
  using pure_function argument
  unfolding pp_t_fresh_sparse_pure_def
  by (cases \<sigma>; cases \<tau>) auto

lemma pp_t_fresh_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_t_fresh_seed w"
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[OF base pp_t_fresh_seed_typed] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval pp_t_fresh_sparse_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      using pp_t_eqv_reflexive[OF pp_t_fresh_seed_typed] .
    show ?thesis
      using pp_t_fresh_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval pp_t_fresh_sparse_constants
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
          (pp_t_eval pp_t_fresh_sparse_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_fresh_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval pp_t_fresh_sparse_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval pp_t_fresh_sparse_constants
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
    using pp_t_fresh_seed_typed r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

lemma pp_t_fresh_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_t_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_t_domain \<sigma>)"
    have extended:
        "pp_t_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_t_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_t_seeded_fundamental_at
          pp_t_fresh_seed \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_t_holds
          (pp_t_eval pp_t_fresh_sparse_constants
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow>
          pp_t_seeded_fundamental_at
            pp_t_fresh_seed \<sigma> w x"
      using pp_t_fresh_eval_fun_holds[
        OF var_type extended, of w] by simp
    show "pp_t_holds
        (pp_t_eval pp_t_fresh_sparse_constants
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_t_eval_Neg_holds[
        of pp_t_fresh_sparse_constants
          "extend_env x \<rho>" "pp_fun \<sigma> (Var 0)" w]
        fun_iff fun_false
      by blast
  qed
qed

theorem pp_t_fresh_unique_fundamental_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_unique_fundamental_holds by blast

theorem pp_t_fresh_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_no_fundamentals_holds[OF assms]
  by blast

lemma pp_t_fresh_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fresh_sparse_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        pp_t_fresh_sparse_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_t_fresh_sparse_pure \<sigma> w x
        \<longrightarrow>
        pp_t_fresh_sparse_pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_fresh_application_closure_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule FreshSparseConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FreshSparseConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding FreshSparseConstants.pp_t_den_def
      pp_t_fresh_application_closure_holds_iff
    using pp_t_fresh_sparse_pure_application by blast
qed

lemma pp_t_fresh_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      pp_zeroary_recombination) w"
  by (simp add: pp_zeroary_recombination_def pp_pure_def
      pp_t_classifier_holds extend_env.simps)

lemma pp_t_fresh_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      pp_zeroary_exhaustion) w"
  by (simp add: pp_zeroary_exhaustion_def pp_pure_def
      pp_t_classifier_holds extend_env.simps)

lemma pp_t_fresh_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      pp_unary_recombination) w"
  by (simp add: pp_unary_recombination_def pp_pure_def
      pp_t_classifier_holds extend_env.simps)

lemma pp_t_fresh_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho>
      pp_unary_exhaustion) w"
  by (simp add: pp_unary_exhaustion_def pp_pure_def
      pp_t_classifier_holds extend_env.simps)

theorem pp_t_fresh_zeroary_recombination_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_zeroary_recombination_holds by blast

theorem pp_t_fresh_zeroary_exhaustion_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_zeroary_exhaustion_holds by blast

theorem pp_t_fresh_unary_recombination_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_unary_recombination_holds by blast

theorem pp_t_fresh_unary_exhaustion_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_def
    FreshSparseConstants.pp_t_den_def
  using pp_t_fresh_unary_exhaustion_holds by blast

lemma pp_t_arrow_eqv_if_pointwise:
  assumes f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and g: "Elem g (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and pointwise:
      "\<forall>v. prefix w v \<longrightarrow>
        (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
          pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> x))"
  shows "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
proof (simp only: pp_t_eqv.simps, intro allI impI)
  fix v x y
  assume future: "prefix w v"
    and x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
    and xy: "pp_t_eqv \<sigma> v x y"
  have fx: "Elem (f \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF f x] .
  have gx: "Elem (g \<acute> x) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF g x] .
  have gy: "Elem (g \<acute> y) (pp_t_domain \<tau>)"
    using pp_t_app_closed[OF g y] .
  have fgx: "pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> x)"
    using pointwise future x by blast
  have gxy: "pp_t_eqv \<tau> v (g \<acute> x) (g \<acute> y)"
    using pp_t_arrow_member_respects[OF g x y xy] .
  show "pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> y)"
    using pp_t_eqv_transitive[OF fx gx gy fgx gxy] .
qed

lemma pp_t_fresh_modalized_functionality_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_fresh_sparse_constants \<rho>
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

theorem pp_t_fresh_modalized_functionality_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma>
    (pp_modalized_functionality \<sigma> \<tau>)"
proof (rule FreshSparseConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FreshSparseConstants.pp_t_den
        (pp_modalized_functionality \<sigma> \<tau>) env) w"
    unfolding FreshSparseConstants.pp_t_den_def
      pp_t_fresh_modalized_functionality_holds_iff
    using pp_t_arrow_eqv_if_pointwise by blast
qed

lemma pp_t_fresh_target_PP_holds:
  "pp_t_holds
    (pp_t_eval pp_t_fresh_sparse_constants \<rho> pp_target_PP) w"
proof -
  have classifier_type:
      "Elem pp_t_fresh_empty_unary_classifier
        (pp_t_domain pp_fresh_classifier_type)"
    by (rule pp_t_fresh_empty_unary_classifier_in_domain)
  have pure:
      "pp_t_fresh_sparse_pure pp_fresh_classifier_type w
        pp_t_fresh_empty_unary_classifier"
    by (rule pp_t_fresh_sparse_classifier_is_pure)
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def pp_pure_def
    using pp_t_classifier_holds[
      OF classifier_type,
      of "pp_t_fresh_sparse_pure pp_fresh_classifier_type" w]
    by (simp add: pp_t_fresh_sparse_unary_classifier pure)
qed

theorem pp_t_fresh_target_PP_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid \<Gamma> pp_target_PP"
proof (rule FreshSparseConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (FreshSparseConstants.pp_t_den pp_target_PP env) w"
    unfolding FreshSparseConstants.pp_t_den_def
    by (rule pp_t_fresh_target_PP_holds)
qed

section \<open>The verified fragment\<close>

definition pp_fresh_sparse_background_axioms :: "oterm set" where
  "pp_fresh_sparse_background_axioms =
    pp_application_closure_schema \<union>
    {pp_unique_fundamental Prop} \<union>
    pp_no_other_fundamentals_schema \<union>
    {pp_zeroary_recombination, pp_unary_recombination} \<union>
    pp_exhaustion_axioms \<union>
    pp_modalized_functionality_schema"

definition pp_fresh_sparse_PP_axioms :: "oterm set" where
  "pp_fresh_sparse_PP_axioms =
    insert pp_target_PP pp_fresh_sparse_background_axioms"

theorem pp_t_fresh_sparse_PP_gvalid:
  "FreshSparseConstants.TreeHenkin.gvalid_set
    pp_fresh_sparse_PP_axioms"
  unfolding FreshSparseConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_fresh_sparse_PP_axioms"
  from A consider
      (target) "A = pp_target_PP"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary_recombination) "A = pp_zeroary_recombination"
    | (unary_recombination) "A = pp_unary_recombination"
    | (zeroary_exhaustion) "A = pp_zeroary_exhaustion"
    | (unary_exhaustion) "A = pp_unary_exhaustion"
    | (functionality) "A \<in> pp_modalized_functionality_schema"
    unfolding pp_fresh_sparse_PP_axioms_def
      pp_fresh_sparse_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  then show "FreshSparseConstants.TreeHenkin.gvalid \<Gamma> A"
  proof cases
    case target
    then show ?thesis
      using pp_t_fresh_target_PP_gvalid by simp
  next
    case application
    then obtain \<sigma> \<tau> where
        A: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_fresh_application_closure_gvalid)
  next
    case unique
    then show ?thesis
      using pp_t_fresh_unique_fundamental_gvalid by simp
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_fresh_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary_recombination
    then show ?thesis
      using pp_t_fresh_zeroary_recombination_gvalid by simp
  next
    case unary_recombination
    then show ?thesis
      using pp_t_fresh_unary_recombination_gvalid by simp
  next
    case zeroary_exhaustion
    then show ?thesis
      using pp_t_fresh_zeroary_exhaustion_gvalid by simp
  next
    case unary_exhaustion
    then show ?thesis
      using pp_t_fresh_unary_exhaustion_gvalid by simp
  next
    case functionality
    then obtain \<sigma> \<tau> where
        A: "A = pp_modalized_functionality \<sigma> \<tau>"
      unfolding pp_modalized_functionality_schema_def by blast
    show ?thesis
      unfolding A
      by (rule pp_t_fresh_modalized_functionality_gvalid)
  qed
qed

theorem pp_fresh_sparse_PP_axioms_consistent:
  "CEV_axiom_consistent [] pp_fresh_sparse_PP_axioms"
  using FreshSparseConstants.pp_t_base_sound
    FreshSparseConstants.pp_t_zeta_sound
    pp_t_fresh_sparse_PP_gvalid
  by (rule
    FreshSparseConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)

corollary pp_fresh_sparse_fragment_consistent:
  assumes "U \<subseteq> pp_fresh_sparse_PP_axioms"
  shows "CEV_axiom_consistent [] U"
proof -
  have valid:
      "FreshSparseConstants.TreeHenkin.gvalid_set U"
    using assms pp_t_fresh_sparse_PP_gvalid
    unfolding FreshSparseConstants.TreeHenkin.gvalid_set_def
    by blast
  show ?thesis
    using FreshSparseConstants.pp_t_base_sound
      FreshSparseConstants.pp_t_zeta_sound valid
    by (rule
      FreshSparseConstants.TreeHenkin.CEV_axiom_consistent_of_gvalid)
qed

end
