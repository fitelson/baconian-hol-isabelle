theory Bacon_PP_ZF_Tree_Range_Classifier
  imports Bacon_PP_ZF_Tree_Seeded_Stock
begin

section \<open>An individual-indexed range classifier\<close>

abbreviation pp_t_unary_type :: otype where
  "pp_t_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

definition pp_range_classifier_builder :: oterm where
  "pp_range_classifier_builder =
    Lam (Ind \<rightarrow>\<^sub>o pp_t_unary_type)
      (Lam pp_t_unary_type
        (Exists Ind
          (Eq pp_t_unary_type
            (Var 1) (App (Var 2) (Var 0)))))"

definition pp_t_range_stock ::
    "ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_range_stock E w X \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_unary_type) \<and>
    (\<exists>n. Elem n (pp_t_domain Ind) \<and>
      pp_t_eqv pp_t_unary_type w X (E \<acute> n))"

lemma pp_range_classifier_builder_typed:
  "[] \<turnstile> pp_range_classifier_builder :
    (Ind \<rightarrow>\<^sub>o pp_t_unary_type)
      \<rightarrow>\<^sub>o pp_t_unary_type \<rightarrow>\<^sub>o Prop"
  unfolding pp_range_classifier_builder_def
  by (intro has_type.Lam has_type.Exists has_type.Eq
      has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma pp_range_classifier_builder_logical:
  "pp_logical_vocabulary pp_range_classifier_builder"
  unfolding pp_range_classifier_builder_def
    pp_logical_vocabulary_def by simp

lemma pp_t_range_stock_admissible:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
  shows "pp_t_predicate_admissible pp_t_unary_type
    (pp_t_range_stock E)"
proof (unfold pp_t_predicate_admissible_def, intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_unary_type)"
    and XY: "pp_t_eqv pp_t_unary_type w X Y"
    and future: "prefix w v"
  have XY_v: "pp_t_eqv pp_t_unary_type v X Y"
    using pp_t_eqv_persistent[OF XY future] .
  have YX_v: "pp_t_eqv pp_t_unary_type v Y X"
    using pp_t_eqv_symmetric[OF X Y XY_v] .
  show "pp_t_range_stock E v X = pp_t_range_stock E v Y"
  proof
    assume X_range: "pp_t_range_stock E v X"
    then obtain n where n: "Elem n (pp_t_domain Ind)"
      and Xn:
        "pp_t_eqv pp_t_unary_type v X (E \<acute> n)"
      unfolding pp_t_range_stock_def by blast
    have En:
        "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
      using pp_t_app_closed[OF E n] .
    have Yn:
        "pp_t_eqv pp_t_unary_type v Y (E \<acute> n)"
      using pp_t_eqv_transitive[OF Y X En YX_v Xn] .
    show "pp_t_range_stock E v Y"
      unfolding pp_t_range_stock_def using Y n Yn by blast
  next
    assume Y_range: "pp_t_range_stock E v Y"
    then obtain n where n: "Elem n (pp_t_domain Ind)"
      and Yn:
        "pp_t_eqv pp_t_unary_type v Y (E \<acute> n)"
      unfolding pp_t_range_stock_def by blast
    have En:
        "Elem (E \<acute> n) (pp_t_domain pp_t_unary_type)"
      using pp_t_app_closed[OF E n] .
    have Xn:
        "pp_t_eqv pp_t_unary_type v X (E \<acute> n)"
      using pp_t_eqv_transitive[OF X Y En XY_v Yn] .
    show "pp_t_range_stock E v X"
      unfolding pp_t_range_stock_def using X n Xn by blast
  qed
qed

lemma pp_t_range_classifier_builder_apply_holds:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and X: "Elem X (pp_t_domain pp_t_unary_type)"
  shows "pp_t_holds
      (((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
        \<acute> X) w
    \<longleftrightarrow>
    pp_t_range_stock E w X"
  unfolding pp_t_closed_den_def pp_range_classifier_builder_def
    pp_t_range_stock_def
  using E X
  by (simp add: Lambda_app pp_t_default_constants_def
      pp_t_closed_env_def extend_env.simps pp_t_app_closed)

lemma pp_t_range_classifier_builder_pointwise:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and X: "Elem X (pp_t_domain pp_t_unary_type)"
  shows "pp_t_eqv Prop w
    (((pp_t_closed_den pp_range_classifier_builder) \<acute> E) \<acute> X)
    ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E)) \<acute> X)"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume "prefix w v"
  have left:
      "pp_t_holds
        (((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
          \<acute> X) v
      \<longleftrightarrow> pp_t_range_stock E v X"
    by (rule pp_t_range_classifier_builder_apply_holds[OF E X])
  have right:
      "pp_t_holds
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> X) v
      \<longleftrightarrow> pp_t_range_stock E v X"
    by (rule pp_t_classifier_holds[OF X])
  show "pp_t_holds
      (((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
        \<acute> X) v =
    pp_t_holds
      ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        \<acute> X) v"
    using left right by blast
qed

lemma pp_t_eqv_arrowI:
  assumes step:
      "\<And>v x y. prefix w v \<Longrightarrow>
        Elem x (pp_t_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_t_domain \<sigma>) \<Longrightarrow>
        pp_t_eqv \<sigma> v x y \<Longrightarrow>
        pp_t_eqv \<tau> v (f \<acute> x) (g \<acute> y)"
  shows "pp_t_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
  using step by simp

theorem pp_t_range_classifier_builder_correct:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
  shows "pp_t_eqv
      (pp_t_unary_type \<rightarrow>\<^sub>o Prop) w
      ((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
      (pp_t_classifier pp_t_unary_type (pp_t_range_stock E))"
proof (rule pp_t_eqv_arrowI)
  fix v X Y
  assume future: "prefix w v"
    and X: "Elem X (pp_t_domain pp_t_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_unary_type)"
    and XY: "pp_t_eqv pp_t_unary_type v X Y"
  have classifier:
      "Elem (pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        (pp_t_domain (pp_t_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain[
      OF pp_t_range_stock_admissible[OF E]])
  have pointwise:
      "pp_t_eqv Prop v
        (((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
          \<acute> X)
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> X)"
    by (rule pp_t_range_classifier_builder_pointwise[OF E X])
  have respects:
      "pp_t_eqv Prop v
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> X)
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> Y)"
    using pp_t_arrow_member_respects[
      OF classifier X Y XY] .
  show "pp_t_eqv Prop v
      (((pp_t_closed_den pp_range_classifier_builder) \<acute> E)
        \<acute> X)
      ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        \<acute> Y)"
    using pp_t_prop_eqv_transitive[OF pointwise respects] .
qed

section \<open>The range-complete basis criterion\<close>

context pp_t_stock_basis
begin

lemma pp_t_range_basis_classifier_pointwise:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and complete:
      "\<And>v X. pp_t_basis_stock D pp_t_unary_type v X
        \<longleftrightarrow> pp_t_range_stock E v X"
    and X: "Elem X (pp_t_domain pp_t_unary_type)"
  shows "pp_t_eqv Prop w
    ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E)) \<acute> X)
    ((pp_t_classifier pp_t_unary_type
      (pp_t_basis_stock D pp_t_unary_type)) \<acute> X)"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume "prefix w v"
  have range:
      "pp_t_holds
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> X) v
      \<longleftrightarrow> pp_t_range_stock E v X"
    by (rule pp_t_classifier_holds[OF X])
  have basis:
      "pp_t_holds
        ((pp_t_classifier pp_t_unary_type
          (pp_t_basis_stock D pp_t_unary_type)) \<acute> X) v
      \<longleftrightarrow>
        pp_t_basis_stock D pp_t_unary_type v X"
    by (rule pp_t_classifier_holds[OF X])
  show "pp_t_holds
      ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        \<acute> X) v =
    pp_t_holds
      ((pp_t_classifier pp_t_unary_type
        (pp_t_basis_stock D pp_t_unary_type)) \<acute> X) v"
    using range basis complete[of v X] by blast
qed

lemma pp_t_range_basis_classifiers_eqv:
  assumes E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    and complete:
      "\<And>v X. pp_t_basis_stock D pp_t_unary_type v X
        \<longleftrightarrow> pp_t_range_stock E v X"
  shows "pp_t_eqv (pp_t_unary_type \<rightarrow>\<^sub>o Prop) w
    (pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
    (pp_t_classifier pp_t_unary_type
      (pp_t_basis_stock D pp_t_unary_type))"
proof (rule pp_t_eqv_arrowI)
  fix v X Y
  assume future: "prefix w v"
    and X: "Elem X (pp_t_domain pp_t_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_unary_type)"
    and XY: "pp_t_eqv pp_t_unary_type v X Y"
  have range_classifier:
      "Elem (pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        (pp_t_domain (pp_t_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain[
      OF pp_t_range_stock_admissible[OF E]])
  have respects:
      "pp_t_eqv Prop v
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> X)
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> Y)"
    using pp_t_arrow_member_respects[
      OF range_classifier X Y XY] .
  have pointwise:
      "pp_t_eqv Prop v
        ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
          \<acute> Y)
        ((pp_t_classifier pp_t_unary_type
          (pp_t_basis_stock D pp_t_unary_type)) \<acute> Y)"
    by (rule pp_t_range_basis_classifier_pointwise[
      OF E complete Y])
  show "pp_t_eqv Prop v
      ((pp_t_classifier pp_t_unary_type (pp_t_range_stock E))
        \<acute> X)
      ((pp_t_classifier pp_t_unary_type
        (pp_t_basis_stock D pp_t_unary_type)) \<acute> Y)"
    using pp_t_prop_eqv_transitive[OF respects pointwise] .
qed

theorem pp_t_range_complete_basis_self_classifies:
  assumes E_stock:
      "pp_t_basis_stock D
        (Ind \<rightarrow>\<^sub>o pp_t_unary_type) [] E"
    and range_complete:
      "\<And>w X. pp_t_basis_stock D pp_t_unary_type w X
        \<longleftrightarrow> pp_t_range_stock E w X"
  shows "pp_t_basis_stock D
    (pp_t_unary_type \<rightarrow>\<^sub>o Prop) []
    (pp_t_classifier pp_t_unary_type
      (pp_t_basis_stock D pp_t_unary_type))"
proof -
  let ?B = "pp_t_closed_den pp_range_classifier_builder"
  let ?F = "?B \<acute> E"
  let ?CR = "pp_t_classifier pp_t_unary_type (pp_t_range_stock E)"
  let ?CB = "pp_t_classifier pp_t_unary_type
    (pp_t_basis_stock D pp_t_unary_type)"
  have E:
      "Elem E
        (pp_t_domain (Ind \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_basis_stock_typed[OF E_stock] .
  have builder_stock:
      "pp_t_basis_stock D
        ((Ind \<rightarrow>\<^sub>o pp_t_unary_type)
          \<rightarrow>\<^sub>o pp_t_unary_type \<rightarrow>\<^sub>o Prop)
        [] ?B"
    using pp_t_basis_stock_contains_logical_den[
      OF pp_range_classifier_builder_typed
        pp_range_classifier_builder_logical] .
  have F_stock:
      "pp_t_basis_stock D
        (pp_t_unary_type \<rightarrow>\<^sub>o Prop) [] ?F"
    using pp_t_basis_stock_application_closed[
      OF builder_stock E_stock] .
  have F:
      "Elem ?F
        (pp_t_domain (pp_t_unary_type \<rightarrow>\<^sub>o Prop))"
    using pp_t_basis_stock_typed[OF F_stock] .
  have CB:
      "Elem ?CB
        (pp_t_domain (pp_t_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain[
      OF pp_t_basis_stock_admissible])
  have CR:
      "Elem ?CR
        (pp_t_domain (pp_t_unary_type \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_classifier_in_domain[
      OF pp_t_range_stock_admissible[OF E]])
  have F_CR:
      "pp_t_eqv (pp_t_unary_type \<rightarrow>\<^sub>o Prop) []
        ?F ?CR"
    by (rule pp_t_range_classifier_builder_correct[OF E])
  have CR_CB:
      "pp_t_eqv (pp_t_unary_type \<rightarrow>\<^sub>o Prop) []
        ?CR ?CB"
    by (rule pp_t_range_basis_classifiers_eqv[
      OF E range_complete])
  have F_CB:
      "pp_t_eqv (pp_t_unary_type \<rightarrow>\<^sub>o Prop) []
        ?F ?CB"
    using pp_t_eqv_transitive[
      OF F CR CB F_CR CR_CB] .
  have CB_F:
      "pp_t_eqv (pp_t_unary_type \<rightarrow>\<^sub>o Prop) []
        ?CB ?F"
    using pp_t_eqv_symmetric[OF F CB F_CB] .
  have stock_iff:
      "pp_t_basis_stock D
          (pp_t_unary_type \<rightarrow>\<^sub>o Prop) [] ?CB
      \<longleftrightarrow>
      pp_t_basis_stock D
          (pp_t_unary_type \<rightarrow>\<^sub>o Prop) [] ?F"
    using pp_t_basis_stock_admissible[
      of "pp_t_unary_type \<rightarrow>\<^sub>o Prop"]
      CB F CB_F
    unfolding pp_t_predicate_admissible_def
    by simp
  show ?thesis
    using stock_iff F_stock by blast
qed

end

end
