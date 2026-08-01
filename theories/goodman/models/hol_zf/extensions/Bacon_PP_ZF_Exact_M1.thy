theory Bacon_PP_ZF_Exact_M1
  imports
    Bacon_PP_ZF_Exact_Recombination
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1_Henkin"
begin

section \<open>Goodman M1 over Bacon's exact appendix carriers\<close>

text \<open>
  This theory transfers the semantic part of Bacon's footnote-59 and
  footnote-60 arguments to the exact recursively restricted carriers.  It
  does not assume that the classifier of the closed-logical unary stock is
  itself closed-logical.  That membership statement is exactly the remaining
  Purity-of-Pure obligation.
\<close>

context pp_e_moving_internal_parameters
begin

sublocale ExactM1: goodman_M1_henkin_model
    pp_e_dom pp_e_holds MovingExactBaconConstants.pp_e_den
    "(\<lambda>f x. f \<acute> x)" pp_e_eqv
    "(\<lambda>\<sigma> w x.
      pp_e_holds (pp_e_classifier \<sigma> (Pure \<sigma>) \<acute> x) w)"
    "(\<lambda>w x. pp_e_holds
      (pp_e_classifier Prop (pp_e_moving_fundamental_at Prop) \<acute> x) w)"
proof
  fix n and env :: "ZF list"
  assume n: "n < length env"
  show "MovingExactBaconConstants.pp_e_den (Var n) env = env ! n"
    using n
    by (simp add: MovingExactBaconConstants.pp_e_den_def
        pp_e_list_env_def nth_default_nth)
next
  show "MovingExactBaconConstants.pp_e_den (Const c \<sigma>) env =
      MovingExactBaconConstants.pp_e_den (Const c \<sigma>) env'"
    for c \<sigma> env env'
    by (simp add: MovingExactBaconConstants.pp_e_den_def)
next
  show "MovingExactBaconConstants.pp_e_den (App F A) env =
      MovingExactBaconConstants.pp_e_den F env \<acute>
        MovingExactBaconConstants.pp_e_den A env"
    for F A env
    by (simp add: MovingExactBaconConstants.pp_e_den_def)
next
  fix \<sigma> x A env
  assume x: "pp_e_dom \<sigma> x"
  show "MovingExactBaconConstants.pp_e_den (Lam \<sigma> A) env \<acute> x =
      MovingExactBaconConstants.pp_e_den A (x # env)"
    using x
    by (simp add: MovingExactBaconConstants.pp_e_den_def
        pp_e_dom_def pp_e_list_env_Cons Lambda_app)
next
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den (Conj A B) env) w \<longleftrightarrow>
      pp_e_holds (MovingExactBaconConstants.pp_e_den A env) w \<and>
      pp_e_holds (MovingExactBaconConstants.pp_e_den B env) w"
    for A B env w
    by (simp add: MovingExactBaconConstants.pp_e_den_def)
next
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den (Eq \<sigma> A B) env) w \<longleftrightarrow>
      pp_e_eqv \<sigma> w
        (MovingExactBaconConstants.pp_e_den A env)
        (MovingExactBaconConstants.pp_e_den B env)"
    for \<sigma> A B env w
    by (simp add: MovingExactBaconConstants.pp_e_den_def)
next
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den (pp_pure \<sigma> A) env) w \<longleftrightarrow>
      pp_e_holds
        (pp_e_classifier \<sigma> (Pure \<sigma>) \<acute>
          MovingExactBaconConstants.pp_e_den A env) w"
    for \<sigma> A env w
    by (simp add: MovingExactBaconConstants.pp_e_den_def pp_pure_def)
next
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den (pp_fun Prop A) env) w \<longleftrightarrow>
      pp_e_holds
        (pp_e_classifier Prop (pp_e_moving_fundamental_at Prop) \<acute>
          MovingExactBaconConstants.pp_e_den A env) w"
    for A env w
    by (simp add: MovingExactBaconConstants.pp_e_den_def pp_fun_def)
next
  show "pp_e_dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<Longrightarrow>
      pp_e_dom \<sigma> x \<Longrightarrow> pp_e_dom \<tau> (f \<acute> x)"
    for \<sigma> \<tau> f x
    by (auto simp: pp_e_dom_def intro: pp_e_app_closed)
next
  show "pp_e_dom \<sigma> x \<Longrightarrow> pp_e_eqv \<sigma> w x x"
    for \<sigma> x w
    by (auto simp: pp_e_dom_def intro: pp_e_eqv_reflexive)
next
  show "pp_e_dom \<sigma> x \<Longrightarrow> pp_e_dom \<sigma> y \<Longrightarrow>
      pp_e_dom \<sigma> z \<Longrightarrow> pp_e_eqv \<sigma> w x y \<Longrightarrow>
      pp_e_eqv \<sigma> w y z \<Longrightarrow> pp_e_eqv \<sigma> w x z"
    for \<sigma> x y z w
    by (auto simp: pp_e_dom_def intro: pp_e_eqv_transitive)
next
  show "pp_e_dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<Longrightarrow>
      pp_e_dom (\<sigma> \<rightarrow>\<^sub>o \<tau>) g \<Longrightarrow>
      pp_e_dom \<sigma> x \<Longrightarrow> pp_e_dom \<sigma> y \<Longrightarrow>
      pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g \<Longrightarrow>
      pp_e_eqv \<sigma> w x y \<Longrightarrow>
      pp_e_eqv \<tau> w (f \<acute> x) (g \<acute> y)"
    for \<sigma> \<tau> f g x y w
    by (auto simp: pp_e_dom_def intro: pp_e_app_respects)
next
  show "pp_e_dom Prop p \<Longrightarrow> pp_e_dom Prop q \<Longrightarrow>
      pp_e_eqv Prop w p q \<Longrightarrow>
      (pp_e_holds p w \<longleftrightarrow> pp_e_holds q w)"
    for p q w
    by (auto simp: pp_e_dom_def intro: pp_e_prop_eqv_at)
qed

theorem pp_e_M1_fn59_diagonal_contradiction:
  defines "D \<equiv>
    MovingExactBaconConstants.pp_e_den pp_M1_fn59_liar []"
  assumes D_pure: "Pure pp_unary_ty w D"
    and qss:
      "pp_e_holds
        (MovingExactBaconConstants.pp_e_den pp_QSS []) w"
    and unique:
      "pp_e_holds
        (MovingExactBaconConstants.pp_e_den
          (pp_unique_fundamental Prop) []) w"
  shows False
proof -
  have D_domain:
      "Elem D (pp_e_domain pp_unary_ty)"
    unfolding D_def
    using MovingExactBaconConstants.pp_e_eval_type[
      OF typed_pp_M1_fn59_liar pp_e_empty_env_typed]
    by (simp add: MovingExactBaconConstants.pp_e_den_def pp_e_dom_def)
  have D_pure_semantic:
      "pp_e_holds
        (pp_e_classifier pp_unary_ty (Pure pp_unary_ty) \<acute> D) w"
    using pp_e_classifier_holds[OF D_domain, of "Pure pp_unary_ty" w]
      D_pure by blast
  show False
    using D_pure_semantic qss unique
    unfolding D_def
    by (rule ExactM1.M1_fn59_diagonal_contradiction)
qed

end

section \<open>The exact footnote-60 classifier\<close>

abbreviation pp_e_M1_unary_type :: otype where
  "pp_e_M1_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_e_M1_fn60_classifier :: ZF where
  "pp_e_M1_fn60_classifier \<equiv>
    pp_e_classifier pp_e_M1_unary_type
      (pp_e_closed_logical_stock pp_e_M1_unary_type)"

theorem pp_e_M1_fn60_classifier_in_exact_domain:
  "Elem pp_e_M1_fn60_classifier
    (pp_e_domain (pp_e_M1_unary_type \<rightarrow>\<^sub>o Prop))"
  by (rule pp_e_classifier_in_domain[
      OF pp_e_closed_logical_stock_admissible])

theorem pp_e_M1_fn60_classifier_exact_extension:
  assumes X: "Elem X (pp_e_domain pp_e_M1_unary_type)"
  shows "pp_e_holds (pp_e_M1_fn60_classifier \<acute> X) w
    \<longleftrightarrow>
    pp_e_closed_logical_stock pp_e_M1_unary_type w X"
  by (rule pp_e_classifier_holds[OF X])

theorem pp_e_M1_fn60_is_exact_Pure_interpretation:
  "pp_e_eval pp_e_generic_internal_constants \<rho>
      (pp_Pure pp_e_M1_unary_type)
    = pp_e_M1_fn60_classifier"
  by simp

theorem pp_e_M1_fn60_PP_iff_classifier_closed_logical_at_world:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        pp_target_PP) w
    \<longleftrightarrow>
    pp_e_closed_logical_stock
      (pp_e_M1_unary_type \<rightarrow>\<^sub>o Prop) w
      pp_e_M1_fn60_classifier"
  by (rule pp_e_generic_target_PP_holds_iff)

text \<open>
  The last theorem is an equivalence, not a nonmembership result.  The exact
  appendix semantics supplies the classifier and identifies its extension;
  proving or refuting its membership in the next pure stock is the PP problem.
\<close>

end
