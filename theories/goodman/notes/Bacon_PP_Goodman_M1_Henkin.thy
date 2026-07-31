theory Bacon_PP_Goodman_M1_Henkin
  imports
    Bacon_PP_Axiom_Soundness
    Bacon_PP_QSS_Recombination_Bridge
    Bacon_PP_Goodman_M1_Complete
begin

section \<open>The footnote-59 obstruction in an arbitrary CEV+ Henkin model\<close>

text \<open>
  This locale isolates the compositional semantic clauses used by Bacon's
  footnote-59 argument.  It extends the denotable-function-space interface,
  rather than the full-function-space semantics.  The additional assumptions
  say only how variables, application, abstraction, conjunction, identity,
  \<open>Pure\<close>, and \<open>Fun\<close> are interpreted, together with the standard
  type-closure and identity-congruence conditions needed by the diagonal.
\<close>

locale goodman_M1_henkin_model =
  henkin_action_model dom holds den
  for dom :: "otype \<Rightarrow> 'u \<Rightarrow> bool"
    and holds :: "'u \<Rightarrow> 'w \<Rightarrow> bool"
    and den :: "oterm \<Rightarrow> 'u list \<Rightarrow> 'u" +
  fixes app :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and eqv :: "otype \<Rightarrow> 'w \<Rightarrow> 'u \<Rightarrow> 'u \<Rightarrow> bool"
    and Pure :: "otype \<Rightarrow> 'w \<Rightarrow> 'u \<Rightarrow> bool"
    and Fun :: "'w \<Rightarrow> 'u \<Rightarrow> bool"
  assumes
    den_Var:
      "n < length env \<Longrightarrow> den (Var n) env = env ! n"
  and den_Const:
      "den (Const c \<sigma>) env = den (Const c \<sigma>) env'"
  and den_App:
      "den (App F A) env = app (den F env) (den A env)"
  and den_Lam_app:
      "dom \<sigma> x \<Longrightarrow>
        app (den (Lam \<sigma> A) env) x = den A (x # env)"
  and den_Conj:
      "holds (den (Conj A B) env) w \<longleftrightarrow>
        (holds (den A env) w \<and> holds (den B env) w)"
  and den_Eq:
      "holds (den (Eq \<sigma> A B) env) w \<longleftrightarrow>
        eqv \<sigma> w (den A env) (den B env)"
  and den_pure:
      "holds (den (pp_pure \<sigma> A) env) w \<longleftrightarrow>
        Pure \<sigma> w (den A env)"
  and den_fun:
      "holds (den (pp_fun Prop A) env) w \<longleftrightarrow>
        Fun w (den A env)"
  and app_type:
      "dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<Longrightarrow> dom \<sigma> x \<Longrightarrow>
        dom \<tau> (app f x)"
  and eqv_reflexive:
      "dom \<sigma> x \<Longrightarrow> eqv \<sigma> w x x"
  and eqv_transitive:
      "dom \<sigma> x \<Longrightarrow> dom \<sigma> y \<Longrightarrow> dom \<sigma> z \<Longrightarrow>
        eqv \<sigma> w x y \<Longrightarrow> eqv \<sigma> w y z \<Longrightarrow>
        eqv \<sigma> w x z"
  and app_respects_eqv:
      "dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<Longrightarrow>
        dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<Longrightarrow>
        dom \<sigma> x \<Longrightarrow> dom \<sigma> y \<Longrightarrow>
        eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g \<Longrightarrow>
        eqv \<sigma> w x y \<Longrightarrow>
        eqv \<tau> w (app f x) (app g y)"
  and prop_eqv_holds:
      "dom Prop p \<Longrightarrow> dom Prop q \<Longrightarrow>
        eqv Prop w p q \<Longrightarrow>
        (holds p w \<longleftrightarrow> holds q w)"
begin

lemma M1_fn59_liar_denotation:
  assumes p: "dom Prop p"
  shows
    "holds (app (den pp_M1_fn59_liar env) p) w
      \<longleftrightarrow>
      (\<forall>X. dom pp_unary_ty X \<longrightarrow>
        (\<forall>q. dom Prop q \<longrightarrow>
          (Pure pp_unary_ty w X
            \<and> Fun w q
            \<and> eqv Prop w p (app X q)
            \<longrightarrow> \<not> holds (app X p) w)))"
proof -
  have beta:
      "app (den pp_M1_fn59_liar env) p =
        den
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (pp_fun Prop (Var 0))
                    (Eq Prop (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))
          (p # env)"
    unfolding pp_M1_fn59_liar_def
    using p by (rule den_Lam_app)
  show ?thesis
    unfolding beta
    by (simp add: den_Forall den_Imp den_Conj den_Neg den_Eq
        den_pure den_fun den_App den_Var)
qed

lemma M1_fn59_QSS_denotation:
  "holds (den pp_QSS env) w
    \<longleftrightarrow>
    (\<forall>X. dom pp_unary_ty X \<longrightarrow>
      (\<forall>Y. dom pp_unary_ty Y \<longrightarrow>
        (\<forall>q. dom Prop q \<longrightarrow>
          (Pure pp_unary_ty w X
            \<and> Pure pp_unary_ty w Y
            \<and> Fun w q
            \<longrightarrow>
            (eqv Prop w (app X q) (app Y q)
              \<longrightarrow> eqv pp_unary_ty w X Y)))))"
  unfolding pp_QSS_def
  by (simp add: den_Forall den_Imp den_Conj den_Eq
      den_pure den_fun den_App den_Var)

lemma M1_unique_fundamental_denotation:
  "holds (den (pp_unique_fundamental Prop) env) w
    \<longleftrightarrow>
    (\<exists>r. dom Prop r
      \<and> Fun w r
      \<and> (\<forall>q. dom Prop q \<longrightarrow>
        Fun w q \<longrightarrow> eqv Prop w q r))"
  unfolding pp_unique_fundamental_def
  by (simp add: den_Exists den_Forall den_Imp den_Conj den_Eq
      den_fun den_Var)

theorem M1_fn59_diagonal_contradiction:
  defines "D \<equiv> den pp_M1_fn59_liar []"
  assumes D_pure: "Pure pp_unary_ty w D"
    and qss_holds: "holds (den pp_QSS []) w"
    and unique_holds:
      "holds (den (pp_unique_fundamental Prop) []) w"
  shows False
proof -
  have liar_type: "[] \<turnstile> pp_M1_fn59_liar : pp_unary_ty"
    by (rule typed_pp_M1_fn59_liar)
  have empty_env: "env_ok (map dom []) []"
    by simp
  have D_dom: "dom pp_unary_ty D"
    unfolding D_def
    using den_type[OF liar_type empty_env] .
  obtain r where r_dom: "dom Prop r"
    and r_fun: "Fun w r"
    and unique:
      "\<And>q. dom Prop q \<Longrightarrow> Fun w q \<Longrightarrow>
        eqv Prop w q r"
    using unique_holds M1_unique_fundamental_denotation by blast
  let ?d = "app D r"
  have d_dom: "dom Prop ?d"
    using D_dom r_dom unfolding pp_unary_ty_def
    by (rule app_type)
  have exact_diagonal:
      "holds (app (den pp_M1_fn59_liar []) ?d) w
        \<longleftrightarrow>
        (\<forall>X. dom pp_unary_ty X \<longrightarrow>
          (\<forall>q. dom Prop q \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Fun w q
              \<and> eqv Prop w ?d (app X q)
              \<longrightarrow> \<not> holds (app X ?d) w)))"
    by (rule M1_fn59_liar_denotation[OF d_dom])
  have diagonal:
      "holds (app D ?d) w
        \<longleftrightarrow>
        (\<forall>X. dom pp_unary_ty X \<longrightarrow>
          (\<forall>q. dom Prop q \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Fun w q
              \<and> eqv Prop w ?d (app X q)
              \<longrightarrow> \<not> holds (app X ?d) w)))"
    using exact_diagonal unfolding D_def .
  have qss:
      "\<forall>X. dom pp_unary_ty X \<longrightarrow>
        (\<forall>Y. dom pp_unary_ty Y \<longrightarrow>
          (\<forall>q. dom Prop q \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Pure pp_unary_ty w Y
              \<and> Fun w q
              \<longrightarrow>
              (eqv Prop w (app X q) (app Y q)
                \<longrightarrow> eqv pp_unary_ty w X Y))))"
    using qss_holds M1_fn59_QSS_denotation by blast
  have not_true:
      "holds (app D ?d) w \<Longrightarrow> \<not> holds (app D ?d) w"
  proof -
    assume true_Dd: "holds (app D ?d) w"
    have rhs:
        "\<forall>X. dom pp_unary_ty X \<longrightarrow>
          (\<forall>q. dom Prop q \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Fun w q
              \<and> eqv Prop w ?d (app X q)
              \<longrightarrow> \<not> holds (app X ?d) w))"
      using diagonal true_Dd by blast
    have dd: "eqv Prop w ?d (app D r)"
      by (rule eqv_reflexive[OF d_dom])
    show "\<not> holds (app D ?d) w"
      using rhs D_dom r_dom D_pure r_fun dd by blast
  qed
  have true_if_not:
      "\<not> holds (app D ?d) w \<Longrightarrow> holds (app D ?d) w"
  proof -
    assume false_Dd: "\<not> holds (app D ?d) w"
    have rhs:
        "\<forall>X. dom pp_unary_ty X \<longrightarrow>
          (\<forall>q. dom Prop q \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Fun w q
              \<and> eqv Prop w ?d (app X q)
              \<longrightarrow> \<not> holds (app X ?d) w))"
    proof (intro allI impI)
      fix X q
      assume X_dom: "dom pp_unary_ty X"
        and q_dom: "dom Prop q"
        and antecedent:
          "Pure pp_unary_ty w X
            \<and> Fun w q
            \<and> eqv Prop w ?d (app X q)"
      then have X_pure: "Pure pp_unary_ty w X"
        and q_fun: "Fun w q"
        and d_Xq: "eqv Prop w ?d (app X q)"
        by auto
      have qr: "eqv Prop w q r"
        using q_dom q_fun by (rule unique)
      have Xq_dom: "dom Prop (app X q)"
        using X_dom q_dom unfolding pp_unary_ty_def
        by (rule app_type)
      have Xr_dom: "dom Prop (app X r)"
        using X_dom r_dom unfolding pp_unary_ty_def
        by (rule app_type)
      have XX: "eqv pp_unary_ty w X X"
        by (rule eqv_reflexive[OF X_dom])
      have Xq_Xr: "eqv Prop w (app X q) (app X r)"
        using X_dom X_dom q_dom r_dom XX qr
        unfolding pp_unary_ty_def
        by (rule app_respects_eqv)
      have d_Xr: "eqv Prop w ?d (app X r)"
        using d_dom Xq_dom Xr_dom d_Xq Xq_Xr
        by (rule eqv_transitive)
      have D_X: "eqv pp_unary_ty w D X"
        using qss D_dom X_dom r_dom D_pure X_pure r_fun d_Xr
        by blast
      have dd: "eqv Prop w ?d ?d"
        by (rule eqv_reflexive[OF d_dom])
      have Dd_dom: "dom Prop (app D ?d)"
        using D_dom d_dom unfolding pp_unary_ty_def
        by (rule app_type)
      have Xd_dom: "dom Prop (app X ?d)"
        using X_dom d_dom unfolding pp_unary_ty_def
        by (rule app_type)
      have Dd_Xd: "eqv Prop w (app D ?d) (app X ?d)"
        using D_dom X_dom d_dom d_dom D_X dd
        unfolding pp_unary_ty_def
        by (rule app_respects_eqv)
      have truth_equiv:
          "holds (app D ?d) w \<longleftrightarrow> holds (app X ?d) w"
        using Dd_dom Xd_dom Dd_Xd by (rule prop_eqv_holds)
      show "\<not> holds (app X ?d) w"
        using false_Dd truth_equiv by blast
    qed
    show "holds (app D ?d) w"
      using diagonal rhs by blast
  qed
  show False
    using not_true true_if_not by blast
qed

theorem M1_fn59_PP_failure:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and background_valid:
      "gvalid_set (pp_M1_fn59_axioms - {pp_target_PP})"
    and qss_valid: "gvalid [] pp_QSS"
    and unique_valid:
      "gvalid [] (pp_unique_fundamental Prop)"
  shows "\<not> gvalid [] pp_target_PP"
proof
  assume PP_valid: "gvalid [] pp_target_PP"
  have PP_all: "\<And>\<Gamma>. gvalid \<Gamma> pp_target_PP"
  proof -
    fix \<Gamma>
    show "gvalid \<Gamma> pp_target_PP"
    proof (rule gvalidI)
      fix env w
      assume env: "env_ok (map dom \<Gamma>) env"
      have target_empty: "holds (den pp_target_PP []) w"
        using PP_valid unfolding gvalid_def by simp
      have pure_constant:
          "den (pp_Pure pp_unary_ty) env =
            den (pp_Pure pp_unary_ty) []"
        unfolding pp_Pure_def by (rule den_Const)
      show "holds (den pp_target_PP env) w"
        using target_empty pure_constant
        by (simp add: pp_target_PP_def pp_purity_of_pure_def
            pp_unary_ty_def den_pure)
    qed
  qed
  have axioms_valid: "gvalid_set pp_M1_fn59_axioms"
    unfolding gvalid_set_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume A: "A \<in> pp_M1_fn59_axioms"
    show "gvalid \<Gamma> A"
    proof (cases "A = pp_target_PP")
      case True
      then show ?thesis using PP_all by simp
    next
      case False
      then have "A \<in> pp_M1_fn59_axioms - {pp_target_PP}"
        using A by blast
      then show ?thesis
        using background_valid unfolding gvalid_set_def by blast
    qed
  qed
  have liar_pure_valid:
      "gvalid [] (pp_pure pp_unary_ty pp_M1_fn59_liar)"
    using base_sound zeta_sound axioms_valid pp_M1_fn59_liar_pure
    by (rule CEV_axiom_soundness)
  have liar_pure_holds:
      "holds (den (pp_pure pp_unary_ty pp_M1_fn59_liar) []) w"
    using liar_pure_valid unfolding gvalid_def by simp
  have D_pure:
      "Pure pp_unary_ty w (den pp_M1_fn59_liar [])"
    using liar_pure_holds by (simp add: den_pure)
  have qss_holds: "holds (den pp_QSS []) w"
    using qss_valid unfolding gvalid_def by simp
  have unique_holds:
      "holds (den (pp_unique_fundamental Prop) []) w"
    using unique_valid unfolding gvalid_def by simp
  show False
    using D_pure qss_holds unique_holds
    by (rule M1_fn59_diagonal_contradiction)
qed

theorem no_full_QLN_model_with_purity_of_fun:
  assumes base_sound:
      "\<And>\<Gamma>' B. \<Gamma>' \<turnstile>\<^sub>CEV B \<Longrightarrow> gvalid \<Gamma>' B"
    and zeta_sound:
      "\<And>\<Gamma>' \<sigma>s F G.
        \<Gamma>' \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
        \<Gamma>' \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
        gvalid (\<sigma>s @ \<Gamma>') (zeta_body \<sigma>s F G) \<Longrightarrow>
        gvalid \<Gamma>' (Eq (arrow_type \<sigma>s Prop) F G)"
    and axioms_valid:
      "gvalid_set
        (insert (pp_purity_of_fun Prop) pp_full_QLN_PP_axioms)"
  shows False
proof -
  let ?T = "insert (pp_purity_of_fun Prop) pp_full_QLN_PP_axioms"
  have M1_background_subset:
      "pp_M1_fn59_axioms - {pp_target_PP} \<subseteq> ?T"
    unfolding pp_M1_fn59_axioms_def pp_full_QLN_PP_axioms_def
      pp_full_QLN_background_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  have background_valid:
      "gvalid_set (pp_M1_fn59_axioms - {pp_target_PP})"
    using axioms_valid M1_background_subset
    unfolding gvalid_set_def by blast
  have repaired_subset:
      "pp_recombination_zeroary_exhaustion_axioms \<subseteq> ?T"
    unfolding pp_recombination_zeroary_exhaustion_axioms_def
      pp_recombination_PP_axioms_def
      pp_full_QLN_PP_axioms_def pp_full_QLN_background_axioms_def
      pp_exhaustion_axioms_def
    by blast
  have repaired_valid:
      "gvalid_set pp_recombination_zeroary_exhaustion_axioms"
    using axioms_valid repaired_subset
    unfolding gvalid_set_def by blast
  have qss_valid: "gvalid [] pp_QSS"
    using base_sound zeta_sound repaired_valid
      CEV_QSS_from_recombination_with_zeroary_exhaustion
    by (rule CEV_axiom_soundness)
  have unique_member:
      "pp_unique_fundamental Prop \<in> ?T"
    using pp_unique_fundamental_is_assumed_full_QLN by blast
  have unique_valid:
      "gvalid [] (pp_unique_fundamental Prop)"
    using axioms_valid unique_member
    unfolding gvalid_set_def by blast
  have PP_member: "pp_target_PP \<in> ?T"
    unfolding pp_full_QLN_PP_axioms_def by blast
  have PP_valid: "gvalid [] pp_target_PP"
    using axioms_valid PP_member
    unfolding gvalid_set_def by blast
  have "\<not> gvalid [] pp_target_PP"
    using base_sound zeta_sound background_valid qss_valid unique_valid
    by (rule M1_fn59_PP_failure)
  then show False using PP_valid by blast
qed

end

end
