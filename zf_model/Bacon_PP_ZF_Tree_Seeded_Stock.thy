theory Bacon_PP_ZF_Tree_Seeded_Stock
  imports Bacon_PP_ZF_Tree_Basis_Stock
begin

section \<open>Uniform seeded-stock interpretations\<close>

fun pp_t_seeded_fundamental_at ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow>
      otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_seeded_fundamental_at seed Ind w x = False"
| "pp_t_seeded_fundamental_at seed Prop w x =
    pp_t_eqv Prop w x (seed w)"
| "pp_t_seeded_fundamental_at seed (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x =
    False"

fun pp_t_seeded_internal_constants ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      (bool list \<Rightarrow> ZF) \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_t_seeded_internal_constants Pure seed c Ind =
    pp_t_default Ind"
| "pp_t_seeded_internal_constants Pure seed c Prop =
    pp_t_default Prop"
| "pp_t_seeded_internal_constants Pure seed c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_t_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_t_classifier \<sigma>
       (pp_t_seeded_fundamental_at seed \<sigma>)
     else pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

locale pp_t_seeded_stock =
  fixes Pure :: "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
    and seed :: "bool list \<Rightarrow> ZF"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Pure \<sigma>)"
    and Pure_persistent:
      "\<And>\<sigma> w v x. Pure \<sigma> w x \<Longrightarrow>
        prefix w v \<Longrightarrow> Pure \<sigma> v x"
    and seed_typed:
      "\<And>w. Elem (seed w) (pp_t_domain Prop)"
    and seed_recombines:
      "\<And>w. pp_t_unary_recombines_at
        (Pure (Prop \<rightarrow>\<^sub>o Prop)) (seed w) w"
    and logical_eval:
      "\<And>\<sigma> M \<rho> w. [] \<turnstile> M : \<sigma> \<Longrightarrow>
        pp_logical_vocabulary M \<Longrightarrow>
        Pure \<sigma> w
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho> M)"
    and Pure_application:
      "\<And>\<sigma> \<tau> w f x.
        Pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f \<Longrightarrow>
        Pure \<sigma> w x \<Longrightarrow>
        Pure \<tau> w (f \<acute> x)"
begin

lemma pp_t_seeded_fundamental_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_seeded_fundamental_at seed \<sigma>)"
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
      and wv: "prefix w v"
    have xy_v: "pp_t_eqv Prop v x y"
      using pp_t_eqv_persistent[OF xy wv] .
    have seed_refl:
        "pp_t_eqv Prop v (seed v) (seed v)"
      using pp_t_eqv_reflexive[OF seed_typed] .
    show "pp_t_seeded_fundamental_at seed Prop v x =
        pp_t_seeded_fundamental_at seed Prop v y"
      using pp_t_eqv_congruence[
        OF x y seed_typed seed_typed xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_t_predicate_admissible_def)
qed

lemma pp_t_seeded_internal_constants_typed:
  "Elem (pp_t_seeded_internal_constants Pure seed c \<sigma>)
    (pp_t_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_t_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_t_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem (pp_t_classifier \<sigma> (Pure \<sigma>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[OF Pure_admissible] .
  have fun_classifier:
      "Elem
        (pp_t_classifier \<sigma>
          (pp_t_seeded_fundamental_at seed \<sigma>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[
      OF pp_t_seeded_fundamental_admissible] .
  have default:
      "Elem (pp_t_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_t_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

interpretation SeededTreeConstants:
  pp_t_constants "pp_t_seeded_internal_constants Pure seed"
  by standard (rule pp_t_seeded_internal_constants_typed)

lemma pp_t_seeded_eval_Pure[simp]:
  "pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
      (pp_Pure \<sigma>) =
    pp_t_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_t_seeded_eval_Fun[simp]:
  "pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
      (pp_Fun \<sigma>) =
    pp_t_classifier \<sigma>
      (pp_t_seeded_fundamental_at seed \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_t_seeded_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      Pure \<sigma> w
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho> M)
        (pp_t_domain \<sigma>)"
    using SeededTreeConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_t_classifier_holds[OF argument, of "Pure \<sigma>" w]
    by simp
qed

lemma pp_t_seeded_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_t_env_typed \<Gamma> \<rho>"
  shows "pp_t_holds
      (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_t_seeded_fundamental_at seed \<sigma> w
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho> M)
        (pp_t_domain \<sigma>)"
    using SeededTreeConstants.pp_t_eval_type[OF typed env]
    by (simp add: pp_t_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_t_classifier_holds[
      OF argument,
      of "pp_t_seeded_fundamental_at seed \<sigma>" w]
    by simp
qed

lemma pp_t_seeded_unique_fundamental_holds:
  "pp_t_holds
    (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "seed w"
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have r_env:
      "pp_t_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_t_env_typed_extend[OF base seed_typed] .
  have r_is_fundamental:
      "pp_t_holds
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_t_eqv Prop w ?r ?r"
      using pp_t_eqv_reflexive[OF seed_typed] .
    show ?thesis
      using pp_t_seeded_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
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
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      using pp_t_seeded_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_t_holds
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_t_eqv Prop w y ?r"
      by simp
    show "pp_t_holds
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
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
    using seed_typed r_is_fundamental uniqueness
    by (simp only: pp_t_eval_Conj_holds
        pp_t_eval_Forall_holds)
qed

lemma pp_t_seeded_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_t_holds
    (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
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
        "\<not> pp_t_seeded_fundamental_at seed \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_t_holds
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow>
          pp_t_seeded_fundamental_at seed \<sigma> w x"
      using pp_t_seeded_eval_fun_holds[
        OF var_type extended, of w] by simp
    show "pp_t_holds
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_t_eval_Neg_holds[
        of "pp_t_seeded_internal_constants Pure seed"
          "extend_env x \<rho>" "pp_fun \<sigma> (Var 0)" w]
        fun_iff fun_false
      by blast
  qed
qed

theorem pp_t_seeded_unique_fundamental_gvalid:
  "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding SeededTreeConstants.TreeHenkin.gvalid_def
    SeededTreeConstants.pp_t_den_def
  using pp_t_seeded_unique_fundamental_holds by blast

theorem pp_t_seeded_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding SeededTreeConstants.TreeHenkin.gvalid_def
    SeededTreeConstants.pp_t_den_def
  using pp_t_seeded_no_fundamentals_holds[OF assms]
  by blast

theorem pp_t_seeded_logical_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule SeededTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  have eval_pure:
      "pp_t_holds
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
          (pp_t_list_env env) (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
        Pure \<sigma> w
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (pp_t_list_env env) M)"
    using pp_t_seeded_eval_pure_holds[
      OF typed pp_t_empty_env_typed, where w=w] .
  have stock:
      "Pure \<sigma> w
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
          (pp_t_list_env env) M)"
    using logical_eval[OF typed logical] .
  show "pp_t_holds
      (SeededTreeConstants.pp_t_den
        (pp_pure \<sigma> M) env) w"
    unfolding SeededTreeConstants.pp_t_den_def
    using eval_pure stock by blast
qed

lemma pp_t_seeded_application_closure_holds_iff:
  "pp_t_holds
      (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_t_domain \<sigma>) \<longrightarrow>
        Pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> Pure \<sigma> w x
        \<longrightarrow>
        Pure \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_t_classifier_holds pp_t_app_closed extend_env.simps)

theorem pp_t_seeded_application_closure_gvalid:
  "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule SeededTreeConstants.TreeHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_t_dom \<Gamma>) env"
  show "pp_t_holds
      (SeededTreeConstants.pp_t_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding SeededTreeConstants.pp_t_den_def
      pp_t_seeded_application_closure_holds_iff
    using Pure_application by blast
qed

lemma pp_t_seeded_unary_recombination_holds_iff:
  "pp_t_holds
      (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (Pure (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_t_seeded_fundamental_at seed Prop w r)
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

lemma pp_t_seeded_fundamental_recombines:
  assumes X:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock: "Pure (Prop \<rightarrow>\<^sub>o Prop) w X"
    and r: "Elem r (pp_t_domain Prop)"
    and r_fundamental:
      "pp_t_seeded_fundamental_at seed Prop w r"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> r) v"
  shows "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
    pp_t_holds (X \<acute> q) w"
proof -
  have seeded: "Elem (seed w) (pp_t_domain Prop)"
    by (rule seed_typed)
  have r_seed: "pp_t_eqv Prop w r (seed w)"
    using r_fundamental by simp
  have seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds (X \<acute> seed w) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have r_seed_v: "pp_t_eqv Prop v r (seed w)"
      using pp_t_eqv_persistent[OF r_seed wv] .
    have applications:
        "pp_t_eqv Prop v (X \<acute> r) (X \<acute> seed w)"
      using pp_t_arrow_member_respects[
        OF X r seeded r_seed_v] .
    have r_true: "pp_t_holds (X \<acute> r) v"
      using necessary wv by blast
    show "pp_t_holds (X \<acute> seed w) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        r_true by simp
  qed
  show ?thesis
    using seed_recombines[of w] X X_stock seed_necessary
    unfolding pp_t_unary_recombines_at_def by blast
qed

theorem pp_t_seeded_unary_recombination_holds:
  "pp_t_holds
    (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
      pp_unary_recombination) w"
  unfolding pp_t_seeded_unary_recombination_holds_iff
  using pp_t_seeded_fundamental_recombines by blast

theorem pp_t_seeded_unary_recombination_gvalid:
  "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding SeededTreeConstants.TreeHenkin.gvalid_def
    SeededTreeConstants.pp_t_den_def
  using pp_t_seeded_unary_recombination_holds by blast

lemma pp_t_seeded_zeroary_recombination_holds:
  "pp_t_holds
    (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
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
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> Pure Prop w P"
      using pp_t_seeded_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_t_holds P w"
    proof -
      assume box: "pp_t_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_t_holds P w
            \<longleftrightarrow> pp_t_holds (pp_zf_truth True) w"
        using pp_t_prop_eqv_at[OF box, of w] by simp
      show "pp_t_holds P w"
        using at_w by simp
    qed
    show "pp_t_holds
        (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_seeded_zeroary_recombination_gvalid:
  "SeededTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding SeededTreeConstants.TreeHenkin.gvalid_def
    SeededTreeConstants.pp_t_den_def
  using pp_t_seeded_zeroary_recombination_holds by blast

theorem pp_t_seeded_recombination_background_gvalid:
  "SeededTreeConstants.TreeHenkin.gvalid_set
    pp_recombination_background_axioms"
  unfolding SeededTreeConstants.TreeHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_recombination_background_axioms"
  show "SeededTreeConstants.TreeHenkin.gvalid \<Gamma> A"
  proof -
    from A consider
      (purity) "A \<in> pp_purity_schema"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
      unfolding pp_recombination_background_axioms_def
        pp_background_axioms_def by blast
    then show ?thesis
    proof cases
      case purity
      then obtain \<sigma> M where typed: "[] \<turnstile> M : \<sigma>"
        and logical: "pp_logical_vocabulary M"
        and A: "A = pp_pure \<sigma> M"
        unfolding pp_purity_schema_def by blast
      show ?thesis
        unfolding A
        using pp_t_seeded_logical_purity_gvalid[
          OF typed logical] .
    next
      case application
      then obtain \<sigma> \<tau> where
          A: "A = pp_application_closure \<sigma> \<tau>"
        unfolding pp_application_closure_schema_def by blast
      show ?thesis
        unfolding A
        by (rule pp_t_seeded_application_closure_gvalid)
    next
      case unique
      show ?thesis
        unfolding unique
        by (rule pp_t_seeded_unique_fundamental_gvalid)
    next
      case no_other
      then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
        and A: "A = pp_no_fundamentals \<sigma>"
        unfolding pp_no_other_fundamentals_schema_def by blast
      show ?thesis
        unfolding A
        by (rule pp_t_seeded_no_fundamentals_gvalid[OF nonprop])
    next
      case zeroary
      show ?thesis
        unfolding zeroary
        by (rule pp_t_seeded_zeroary_recombination_gvalid)
    next
      case unary
      show ?thesis
        unfolding unary
        by (rule pp_t_seeded_unary_recombination_gvalid)
    qed
  qed
qed

lemma pp_t_seeded_target_PP_holds_iff:
  "pp_t_holds
      (pp_t_eval (pp_t_seeded_internal_constants Pure seed) \<rho>
        pp_target_PP) w
    \<longleftrightarrow>
    Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  let ?U = "Prop \<rightarrow>\<^sub>o Prop"
  let ?C = "pp_t_classifier ?U (Pure ?U)"
  have C:
      "Elem ?C (pp_t_domain (?U \<rightarrow>\<^sub>o Prop))"
    using pp_t_classifier_in_domain[OF Pure_admissible] .
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def pp_pure_def
    using pp_t_classifier_holds[
      OF C, of "Pure (?U \<rightarrow>\<^sub>o Prop)" w]
    by simp
qed

theorem pp_t_seeded_recombination_PP_gvalid_iff:
  "SeededTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms
    \<longleftrightarrow>
    (\<forall>w.
      Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop))))"
proof
  assume stock:
      "SeededTreeConstants.TreeHenkin.gvalid_set
        pp_recombination_PP_axioms"
  have target:
      "SeededTreeConstants.TreeHenkin.gvalid [] pp_target_PP"
    using stock
    unfolding SeededTreeConstants.TreeHenkin.gvalid_set_def
      pp_recombination_PP_axioms_def
    by blast
  show "\<forall>w.
      Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
  proof
    fix w
    have target_holds:
        "pp_t_holds
          (pp_t_eval (pp_t_seeded_internal_constants Pure seed)
            (pp_t_list_env []) pp_target_PP) w"
      using target
      unfolding SeededTreeConstants.TreeHenkin.gvalid_def
        SeededTreeConstants.pp_t_den_def
      by simp
    show "Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
      using target_holds
      unfolding pp_t_seeded_target_PP_holds_iff .
  qed
next
  assume target:
      "\<forall>w.
        Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
  show "SeededTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms"
    unfolding SeededTreeConstants.TreeHenkin.gvalid_set_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume A: "A \<in> pp_recombination_PP_axioms"
    then consider
      (target) "A = pp_target_PP"
    | (background) "A \<in> pp_recombination_background_axioms"
      unfolding pp_recombination_PP_axioms_def by blast
    then show "SeededTreeConstants.TreeHenkin.gvalid \<Gamma> A"
    proof cases
      case target_case: target
      show ?thesis
        unfolding target_case
          SeededTreeConstants.TreeHenkin.gvalid_def
          SeededTreeConstants.pp_t_den_def
        using target pp_t_seeded_target_PP_holds_iff
        by blast
    next
      case background
      show ?thesis
        using pp_t_seeded_recombination_background_gvalid
          background
        unfolding SeededTreeConstants.TreeHenkin.gvalid_set_def
        by blast
    qed
  qed
qed

corollary pp_t_seeded_recombination_PP_gvalid_iff_root:
  "SeededTreeConstants.TreeHenkin.gvalid_set
      pp_recombination_PP_axioms
    \<longleftrightarrow>
    Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
      (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  have all_iff_root:
      "(\<forall>w.
        Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop))))
      \<longleftrightarrow>
      Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
  proof
    assume all_worlds:
      "\<forall>w.
        Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
    show "Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
      using all_worlds by blast
  next
    assume root:
        "Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) []
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
    show "\<forall>w.
        Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
    proof
      fix w
      show "Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (Pure (Prop \<rightarrow>\<^sub>o Prop)))"
        using Pure_persistent[OF root, of w] by simp
    qed
  qed
  show ?thesis
    using pp_t_seeded_recombination_PP_gvalid_iff all_iff_root
    by blast
qed

end

section \<open>Instantiation by a countable cone-natural basis\<close>

context pp_t_stock_basis
begin

lemma pp_t_basis_stock_contains_eval:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_basis_stock D \<sigma> w (pp_t_eval C \<rho> M)"
proof -
  have const_free: "consts_of M = {}"
    using logical unfolding pp_logical_vocabulary_def .
  have change_constants:
      "pp_t_eval C \<rho> M =
        pp_t_eval pp_t_default_constants \<rho> M"
    using pp_t_eval_const_free[OF const_free] .
  have related:
      "pp_t_eqv \<sigma> w
        (pp_t_eval pp_t_default_constants \<rho> M)
        (pp_t_eval pp_t_default_constants pp_t_closed_env M)"
    using DefaultTreeConstants.pp_t_eval_respects[
      OF typed pp_t_empty_env_eqv] .
  have domain:
      "Elem (pp_t_eval C \<rho> M) (pp_t_domain \<sigma>)"
    unfolding change_constants
    using DefaultTreeConstants.pp_t_eval_type[
      OF typed pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have basis:
      "pp_t_closed_den M \<in> D \<sigma>"
    using logical_basis[OF typed logical] .
  have equivalence:
      "pp_t_eqv \<sigma> w
        (pp_t_eval C \<rho> M) (pp_t_closed_den M)"
    using related change_constants
    by (simp add: pp_t_closed_den_def)
  show ?thesis
    using domain basis equivalence
    by (rule pp_t_basis_stockI)
qed

definition pp_t_basis_root_seed :: ZF where
  "pp_t_basis_root_seed =
    (SOME r. Elem r (pp_t_domain Prop) \<and>
      pp_t_unary_recombines_at
        (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop)) r [])"

lemma pp_t_basis_root_seed_spec:
  "Elem pp_t_basis_root_seed (pp_t_domain Prop)
    \<and>
  pp_t_unary_recombines_at
    (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop))
    pp_t_basis_root_seed []"
proof -
  have exists:
      "\<exists>r. Elem r (pp_t_domain Prop) \<and>
        pp_t_unary_recombines_at
          (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop)) r []"
    using pp_t_generic_seed_recombines_basis_stock_at_root .
  show ?thesis
    unfolding pp_t_basis_root_seed_def
    using someI_ex[OF exists] .
qed

lemma pp_t_basis_root_seed_in_domain:
  "Elem pp_t_basis_root_seed (pp_t_domain Prop)"
  using pp_t_basis_root_seed_spec by blast

lemma pp_t_basis_root_seed_recombines:
  "pp_t_unary_recombines_at
    (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop))
    pp_t_basis_root_seed []"
  using pp_t_basis_root_seed_spec by blast

definition pp_t_basis_seed_at :: "bool list \<Rightarrow> ZF" where
  "pp_t_basis_seed_at w =
    pp_t_cone_lift w pp_t_basis_root_seed"

lemma pp_t_basis_seed_at_in_domain:
  "Elem (pp_t_basis_seed_at w) (pp_t_domain Prop)"
  unfolding pp_t_basis_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

lemma pp_t_basis_seed_at_recombines:
  "pp_t_unary_recombines_at
    (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop))
    (pp_t_basis_seed_at w) w"
  unfolding pp_t_basis_seed_at_def
  using pp_t_basis_root_recombination_transports_to_cone[
    OF pp_t_basis_root_seed_in_domain
      pp_t_basis_root_seed_recombines] .

sublocale BasisSeeded: pp_t_seeded_stock
  "pp_t_basis_stock D" pp_t_basis_seed_at
proof
  fix \<sigma>
  show "pp_t_predicate_admissible \<sigma>
      (pp_t_basis_stock D \<sigma>)"
    by (rule pp_t_basis_stock_admissible)
next
  fix \<sigma> w v x
  assume stock: "pp_t_basis_stock D \<sigma> w x"
    and future: "prefix w v"
  show "pp_t_basis_stock D \<sigma> v x"
    using pp_t_basis_stock_persistent[OF stock future] .
next
  fix w
  show "Elem (pp_t_basis_seed_at w) (pp_t_domain Prop)"
    by (rule pp_t_basis_seed_at_in_domain)
next
  fix w
  show "pp_t_unary_recombines_at
      (pp_t_basis_stock D (Prop \<rightarrow>\<^sub>o Prop))
      (pp_t_basis_seed_at w) w"
    by (rule pp_t_basis_seed_at_recombines)
next
  fix \<sigma> M \<rho> w
  assume typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  show "pp_t_basis_stock D \<sigma> w
      (pp_t_eval
        (pp_t_seeded_internal_constants
          (pp_t_basis_stock D) pp_t_basis_seed_at) \<rho> M)"
    using pp_t_basis_stock_contains_eval[OF typed logical] .
next
  fix \<sigma> \<tau> w f x
  assume f:
      "pp_t_basis_stock D (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
    and x: "pp_t_basis_stock D \<sigma> w x"
  show "pp_t_basis_stock D \<tau> w (f \<acute> x)"
    using pp_t_basis_stock_application_closed[OF f x] .
qed

lemmas pp_t_basis_recombination_background_gvalid =
  BasisSeeded.pp_t_seeded_recombination_background_gvalid

lemmas pp_t_basis_recombination_PP_gvalid_iff =
  BasisSeeded.pp_t_seeded_recombination_PP_gvalid_iff

lemmas pp_t_basis_recombination_PP_gvalid_iff_root =
  BasisSeeded.pp_t_seeded_recombination_PP_gvalid_iff_root

end

end
