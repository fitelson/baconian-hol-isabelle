theory Bacon_PP_ZF_Tree_Boolean_Probe_Successor
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Canonical_Cases.Bacon_PP_ZF_Tree_Boolean_Probe_Canonical_Cases
begin

section \<open>Boolean closure after adjoining the stabilized probe\<close>

datatype pp_t_probe_successor_expr =
    PPProbeSuccessorOld pp_t_probe_boolean_expr
  | PPProbeSuccessorGenerator
  | PPProbeSuccessorNeg pp_t_probe_successor_expr
  | PPProbeSuccessorConj
      pp_t_probe_successor_expr pp_t_probe_successor_expr

instantiation pp_t_probe_successor_expr :: countable
begin

instance
  by countable_datatype

end

fun pp_t_probe_successor_expr_valid ::
    "pp_t_probe_successor_expr \<Rightarrow> bool"
where
  "pp_t_probe_successor_expr_valid
      (PPProbeSuccessorOld E) =
    pp_t_probe_boolean_expr_valid E"
| "pp_t_probe_successor_expr_valid
      PPProbeSuccessorGenerator = True"
| "pp_t_probe_successor_expr_valid
      (PPProbeSuccessorNeg E) =
    pp_t_probe_successor_expr_valid E"
| "pp_t_probe_successor_expr_valid
      (PPProbeSuccessorConj E F) =
    (pp_t_probe_successor_expr_valid E
      \<and> pp_t_probe_successor_expr_valid F)"

fun pp_t_probe_successor_expr_den ::
    "pp_t_probe_successor_expr \<Rightarrow> ZF"
where
  "pp_t_probe_successor_expr_den (PPProbeSuccessorOld E) =
    pp_t_probe_boolean_expr_den E"
| "pp_t_probe_successor_expr_den PPProbeSuccessorGenerator =
    pp_t_probe_boolean_family_probe"
| "pp_t_probe_successor_expr_den (PPProbeSuccessorNeg E) =
    pp_t_closed_den pp_t_unary_output_negator
      \<acute> pp_t_probe_successor_expr_den E"
| "pp_t_probe_successor_expr_den
      (PPProbeSuccessorConj E F) =
    (pp_t_unary_output_conjunction_den
      \<acute> pp_t_probe_successor_expr_den E)
      \<acute> pp_t_probe_successor_expr_den F"

lemma pp_t_probe_successor_expr_den_in_domain:
  assumes valid: "pp_t_probe_successor_expr_valid E"
  shows "Elem (pp_t_probe_successor_expr_den E)
    (pp_t_domain pp_t_boolean_probe_unary_type)"
  using valid
proof (induction E)
  case (PPProbeSuccessorOld E)
  then show ?case
    using pp_t_probe_boolean_expr_den_in_domain by simp
next
  case PPProbeSuccessorGenerator
  show ?case
    using pp_t_probe_boolean_family_probe_in_domain by simp
next
  case (PPProbeSuccessorNeg E)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    using PPProbeSuccessorNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule PPProbeSuccessorNeg.IH[OF E_valid])
  have negator:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  show ?case
    using pp_t_app_closed[OF negator E_domain] by simp
next
  case (PPProbeSuccessorConj E F)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    and F_valid: "pp_t_probe_successor_expr_valid F"
    using PPProbeSuccessorConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule PPProbeSuccessorConj.IH(1)[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_successor_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule PPProbeSuccessorConj.IH(2)[OF F_valid])
  have first:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain])
  show ?case
    using pp_t_app_closed[OF first F_domain] by simp
qed

lemma pp_t_probe_successor_expr_den_cone_natural:
  assumes valid: "pp_t_probe_successor_expr_valid E"
  shows "pp_t_cone_rel pp_t_boolean_probe_unary_type s
    (pp_t_probe_successor_expr_den E)
    (pp_t_probe_successor_expr_den E)"
  using valid
proof (induction E)
  case (PPProbeSuccessorOld E)
  then show ?case
    using pp_t_probe_boolean_expr_den_cone_natural by simp
next
  case PPProbeSuccessorGenerator
  show ?case
    using pp_t_probe_boolean_family_probe_cone_natural by simp
next
  case (PPProbeSuccessorNeg E)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    using PPProbeSuccessorNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF E_valid])
  have negator_domain:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have negator_cone:
      "pp_t_cone_rel pp_t_boolean_probe_transformer_type s
        (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_closed_den pp_t_unary_output_negator)"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_unary_output_negator_typed
          pp_t_unary_output_negator_logical])
  have applied:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s
        (pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_successor_expr_den E)"
    using negator_cone negator_domain E_domain
      PPProbeSuccessorNeg.IH[OF E_valid]
    by auto
  show ?case using applied by simp
next
  case (PPProbeSuccessorConj E F)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    and F_valid: "pp_t_probe_successor_expr_valid F"
    using PPProbeSuccessorConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_successor_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF F_valid])
  have conjunction_cone:
      "pp_t_cone_rel pp_t_boolean_probe_builder_type s
        pp_t_unary_output_conjunction_den
        pp_t_unary_output_conjunction_den"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_unary_output_conjunction_typed
          pp_t_unary_output_conjunction_logical])
  have first_domain:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain])
  have first_cone:
      "pp_t_cone_rel pp_t_boolean_probe_transformer_type s
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)"
    using conjunction_cone
      pp_t_unary_output_conjunction_den_in_domain E_domain
      PPProbeSuccessorConj.IH(1)[OF E_valid]
    by auto
  have applied:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_successor_expr_den E)
          \<acute> pp_t_probe_successor_expr_den F)
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_successor_expr_den E)
          \<acute> pp_t_probe_successor_expr_den F)"
    using first_cone first_domain F_domain
      PPProbeSuccessorConj.IH(2)[OF F_valid]
    by auto
  show ?case using applied by simp
qed

lemma pp_t_probe_successor_expr_den_aut_fixed:
  assumes valid: "pp_t_probe_successor_expr_valid E"
  shows "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_probe_successor_expr_den E)
    =
    pp_t_probe_successor_expr_den E"
  using valid
proof (induction E)
  case (PPProbeSuccessorOld E)
  then show ?case
    using pp_t_probe_boolean_expr_den_aut_fixed by simp
next
  case PPProbeSuccessorGenerator
  show ?case
    using pp_t_probe_boolean_family_probe_aut_fixed by simp
next
  case (PPProbeSuccessorNeg E)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    using PPProbeSuccessorNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF E_valid])
  have negator:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have negator_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          (pp_t_closed_den pp_t_unary_output_negator)
        =
        pp_t_closed_den pp_t_unary_output_negator"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_unary_output_negator_typed
        pp_t_unary_output_negator_logical])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_closed_den pp_t_unary_output_negator
            \<acute> pp_t_probe_successor_expr_den E)
        =
        pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_successor_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF negator E_domain negator_fixed
        PPProbeSuccessorNeg.IH[OF E_valid]])
  show ?case using fixed by simp
next
  case (PPProbeSuccessorConj E F)
  have E_valid: "pp_t_probe_successor_expr_valid E"
    and F_valid: "pp_t_probe_successor_expr_valid F"
    using PPProbeSuccessorConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_successor_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF F_valid])
  have conjunction:
      "Elem pp_t_unary_output_conjunction_den
        (pp_t_domain pp_t_boolean_probe_builder_type)"
    by (rule pp_t_unary_output_conjunction_den_in_domain)
  have conjunction_fixed:
      "pp_t_aut pp_t_boolean_probe_builder_type
          pp_t_unary_output_conjunction_den
        =
        pp_t_unary_output_conjunction_den"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_unary_output_conjunction_typed
        pp_t_unary_output_conjunction_logical])
  have first_domain:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[OF conjunction E_domain])
  have first_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_successor_expr_den E)
        =
        pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF conjunction E_domain conjunction_fixed
        PPProbeSuccessorConj.IH(1)[OF E_valid]])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          ((pp_t_unary_output_conjunction_den
              \<acute> pp_t_probe_successor_expr_den E)
            \<acute> pp_t_probe_successor_expr_den F)
        =
        (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_successor_expr_den E)
          \<acute> pp_t_probe_successor_expr_den F"
    by (rule pp_t_aut_fixed_application[
      OF first_domain F_domain first_fixed
        PPProbeSuccessorConj.IH(2)[OF F_valid]])
  show ?case using fixed by simp
qed

definition pp_t_probe_successor_representatives :: "ZF set" where
  "pp_t_probe_successor_representatives =
    pp_t_probe_successor_expr_den `
      {E. pp_t_probe_successor_expr_valid E}"

lemma pp_t_probe_successor_representatives_countable:
  "countable pp_t_probe_successor_representatives"
  unfolding pp_t_probe_successor_representatives_def by simp

lemma pp_t_probe_successor_representative_in_domain:
  assumes d: "d \<in> pp_t_probe_successor_representatives"
  shows "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
  using d pp_t_probe_successor_expr_den_in_domain
  unfolding pp_t_probe_successor_representatives_def by blast

lemma pp_t_probe_successor_representative_cone_natural:
  assumes d: "d \<in> pp_t_probe_successor_representatives"
  shows "pp_t_cone_rel pp_t_boolean_probe_unary_type s d d"
  using d pp_t_probe_successor_expr_den_cone_natural
  unfolding pp_t_probe_successor_representatives_def by blast

lemma pp_t_probe_successor_representative_aut_fixed:
  assumes d: "d \<in> pp_t_probe_successor_representatives"
  shows "pp_t_aut pp_t_boolean_probe_unary_type d = d"
  using d pp_t_probe_successor_expr_den_aut_fixed
  unfolding pp_t_probe_successor_representatives_def by blast

lemma pp_t_probe_successor_representative_equivariant:
  assumes d: "d \<in> pp_t_probe_successor_representatives"
  shows "pp_b_equivariant (pp_b_operator_of d)"
  by (rule pp_t_cone_rel_operator_implies_equivariant)
    (rule
      pp_t_probe_successor_representative_cone_natural[OF d])

definition pp_t_probe_successor_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_stock w X \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
    \<and>
    (\<exists>d \<in> pp_t_probe_successor_representatives.
      pp_t_eqv pp_t_boolean_probe_unary_type w X d)"

lemma pp_t_probe_successor_stock_admissible:
  "pp_t_predicate_admissible pp_t_boolean_probe_unary_type
    pp_t_probe_successor_stock"
proof (unfold pp_t_predicate_admissible_def, intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and XY: "pp_t_eqv pp_t_boolean_probe_unary_type w X Y"
    and wv: "prefix w v"
  have XYv:
      "pp_t_eqv pp_t_boolean_probe_unary_type v X Y"
    by (rule pp_t_eqv_persistent[OF XY wv])
  have YXv:
      "pp_t_eqv pp_t_boolean_probe_unary_type v Y X"
    by (rule pp_t_eqv_symmetric[OF X Y XYv])
  show "pp_t_probe_successor_stock v X =
      pp_t_probe_successor_stock v Y"
  proof
    assume stock: "pp_t_probe_successor_stock v X"
    then obtain d where
        d: "d \<in> pp_t_probe_successor_representatives"
      and Xd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v X d"
      unfolding pp_t_probe_successor_stock_def by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_successor_representative_in_domain[OF d])
    have Yd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v Y d"
      by (rule pp_t_eqv_transitive[
        OF Y X d_domain YXv Xd])
    show "pp_t_probe_successor_stock v Y"
      unfolding pp_t_probe_successor_stock_def
      using Y d Yd by blast
  next
    assume stock: "pp_t_probe_successor_stock v Y"
    then obtain d where
        d: "d \<in> pp_t_probe_successor_representatives"
      and Yd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v Y d"
      unfolding pp_t_probe_successor_stock_def by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_successor_representative_in_domain[OF d])
    have Xd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v X d"
      by (rule pp_t_eqv_transitive[
        OF X Y d_domain XYv Yd])
    show "pp_t_probe_successor_stock v X"
      unfolding pp_t_probe_successor_stock_def
      using X d Xd by blast
  qed
qed

lemma pp_t_probe_successor_stock_cone_iff:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s X Y"
  shows "pp_t_probe_successor_stock (s @ u) X
    \<longleftrightarrow> pp_t_probe_successor_stock u Y"
proof -
  have representative:
      "\<And>d.
        d \<in> pp_t_probe_successor_representatives
        \<Longrightarrow>
        (pp_t_eqv pp_t_boolean_probe_unary_type (s @ u) X d
        \<longleftrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type u Y d)"
  proof -
    fix d
    assume d: "d \<in> pp_t_probe_successor_representatives"
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_successor_representative_in_domain[OF d])
    have d_cone:
        "pp_t_cone_rel pp_t_boolean_probe_unary_type s d d"
      by (rule
        pp_t_probe_successor_representative_cone_natural[OF d])
    show "pp_t_eqv pp_t_boolean_probe_unary_type (s @ u) X d
        \<longleftrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type u Y d"
      using UnconditionalCone.pp_t_cone_rel_eqv_iff[
        OF X Y d_domain d_domain XY d_cone, of u] .
  qed
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using X Y representative by blast
qed

lemma pp_t_probe_boolean_stock_subset_successor_stock:
  assumes stock: "pp_t_probe_boolean_stock w X"
  shows "pp_t_probe_successor_stock w X"
proof -
  obtain E where valid: "pp_t_probe_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_boolean_expr_den E)"
    using stock by (rule pp_t_probe_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_boolean_stock_def by blast
  have successor_valid:
      "pp_t_probe_successor_expr_valid
        (PPProbeSuccessorOld E)"
    using valid by simp
  have representative:
      "pp_t_probe_boolean_expr_den E
        \<in> pp_t_probe_successor_representatives"
  proof -
    have member:
        "PPProbeSuccessorOld E
          \<in> {F. pp_t_probe_successor_expr_valid F}"
      using successor_valid by simp
    have image:
        "pp_t_probe_successor_expr_den (PPProbeSuccessorOld E)
          \<in> pp_t_probe_successor_expr_den `
            {F. pp_t_probe_successor_expr_valid F}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_successor_representatives_def by simp
  qed
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using X representative represented by blast
qed

lemma pp_t_probe_boolean_family_probe_in_successor_stock:
  "pp_t_probe_successor_stock w
    pp_t_probe_boolean_family_probe"
proof -
  have representative:
      "pp_t_probe_boolean_family_probe
        \<in> pp_t_probe_successor_representatives"
  proof -
    have member:
        "PPProbeSuccessorGenerator
          \<in> {E. pp_t_probe_successor_expr_valid E}"
      by simp
    have image:
        "pp_t_probe_successor_expr_den PPProbeSuccessorGenerator
          \<in> pp_t_probe_successor_expr_den `
            {E. pp_t_probe_successor_expr_valid E}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_successor_representatives_def by simp
  qed
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using pp_t_probe_boolean_family_probe_in_domain representative
      pp_t_eqv_reflexive[
        OF pp_t_probe_boolean_family_probe_in_domain]
    by blast
qed

lemma pp_t_probe_successor_stock_represented:
  assumes stock: "pp_t_probe_successor_stock w X"
  obtains E where
    "pp_t_probe_successor_expr_valid E"
    "pp_t_eqv pp_t_boolean_probe_unary_type w X
      (pp_t_probe_successor_expr_den E)"
  using stock
  unfolding pp_t_probe_successor_stock_def
    pp_t_probe_successor_representatives_def
  by (blast intro: that)

lemma pp_t_probe_successor_stock_output_negation_closed:
  assumes stock: "pp_t_probe_successor_stock w X"
  shows "pp_t_probe_successor_stock w
    (pp_t_closed_den pp_t_unary_output_negator \<acute> X)"
proof -
  obtain E where valid: "pp_t_probe_successor_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_successor_expr_den E)"
    using stock by (rule pp_t_probe_successor_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_successor_stock_def by blast
  have d:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF valid])
  have N:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have result:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_closed_den pp_t_unary_output_negator \<acute> X)
        (pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_successor_expr_den E)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[OF N] X d represented])
  have result_domain:
      "Elem
        (pp_t_closed_den pp_t_unary_output_negator \<acute> X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF N X])
  have representative:
      "pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_successor_expr_den E
        \<in> pp_t_probe_successor_representatives"
  proof -
    have member:
        "PPProbeSuccessorNeg E
          \<in> {F. pp_t_probe_successor_expr_valid F}"
      using valid by simp
    have image:
        "pp_t_probe_successor_expr_den (PPProbeSuccessorNeg E)
          \<in> pp_t_probe_successor_expr_den `
            {F. pp_t_probe_successor_expr_valid F}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_successor_representatives_def by simp
  qed
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using result_domain representative result by blast
qed

lemma pp_t_probe_successor_stock_output_conjunction_closed:
  assumes X_stock: "pp_t_probe_successor_stock w X"
    and Y_stock: "pp_t_probe_successor_stock w Y"
  shows "pp_t_probe_successor_stock w
    ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)"
proof -
  obtain E where E_valid: "pp_t_probe_successor_expr_valid E"
    and X_E:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_successor_expr_den E)"
    using X_stock by (rule pp_t_probe_successor_stock_represented)
  obtain F where F_valid: "pp_t_probe_successor_expr_valid F"
    and Y_F:
      "pp_t_eqv pp_t_boolean_probe_unary_type w Y
        (pp_t_probe_successor_expr_den F)"
    using Y_stock by (rule pp_t_probe_successor_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using X_stock unfolding pp_t_probe_successor_stock_def by blast
  have Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    using Y_stock unfolding pp_t_probe_successor_stock_def by blast
  have d:
      "Elem (pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF E_valid])
  have e:
      "Elem (pp_t_probe_successor_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_expr_den_in_domain[OF F_valid])
  have K:
      "Elem pp_t_unary_output_conjunction_den
        (pp_t_domain pp_t_boolean_probe_builder_type)"
    by (rule pp_t_unary_output_conjunction_den_in_domain)
  have first:
      "pp_t_eqv pp_t_boolean_probe_transformer_type w
        (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[OF K] X d X_E])
  have KX:
      "Elem (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[OF K X])
  have Kd:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[OF K d])
  have result:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
        ((pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
          \<acute> pp_t_probe_successor_expr_den F)"
    by (rule pp_t_app_respects[OF first Y e Y_F])
  have result_domain:
      "Elem
        ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF KX Y])
  have representative:
      "(pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_successor_expr_den E)
          \<acute> pp_t_probe_successor_expr_den F
        \<in> pp_t_probe_successor_representatives"
  proof -
    have member:
        "PPProbeSuccessorConj E F
          \<in> {G. pp_t_probe_successor_expr_valid G}"
      using E_valid F_valid by simp
    have image:
        "pp_t_probe_successor_expr_den
            (PPProbeSuccessorConj E F)
          \<in> pp_t_probe_successor_expr_den `
            {G. pp_t_probe_successor_expr_valid G}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_successor_representatives_def by simp
  qed
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using result_domain representative result by blast
qed

section \<open>The only possible new family value\<close>

theorem pp_t_probe_successor_family_membership_reduction_at_root:
  assumes p: "Elem p (pp_t_domain Prop)"
    and stock:
      "pp_t_probe_successor_stock []
        (pp_t_symmetrized_singleton_family_at p)"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    pp_t_symmetrized_singleton_family_at p
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  let ?Fp = "pp_t_symmetrized_singleton_family_at p"
  have Fp:
      "Elem ?Fp (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
  obtain d where
      d: "d \<in> pp_t_probe_successor_representatives"
    and Fd:
      "pp_t_eqv pp_t_boolean_probe_unary_type [] ?Fp d"
    using stock unfolding pp_t_probe_successor_stock_def by blast
  have d_domain:
      "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_representative_in_domain[OF d])
  have equality: "?Fp = d"
    by (rule pp_t_root_eqv_imp_eq[OF Fp d_domain Fd])
  have family_cone:
      "\<And>s. pp_t_cone_rel pp_t_boolean_probe_unary_type s
        ?Fp ?Fp"
    using
      pp_t_probe_successor_representative_cone_natural[OF d]
    unfolding equality .
  have stable:
      "pp_t_family_same_value_on_relative_views
        pp_t_symmetrized_singleton_family_builder [] p"
    unfolding pp_t_family_same_value_on_relative_views_def
      pp_t_cone_view_empty[OF p]
  proof
    fix s
    show "pp_t_symmetrized_singleton_family_at
          (pp_t_cone_view s p)
        =
        pp_t_symmetrized_singleton_family_at p"
      by (rule
        pp_t_logical_family_cone_natural_forces_same_value[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_singleton_family_builder_logical
            p family_cone])
  qed
  have parameter:
      "p =
        pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
    by (rule
      pp_t_symmetrized_family_stable_parameter_is_word_character[
        OF p stable])
  have family_eq:
      "?Fp =
        pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))"
    by (rule arg_cong[OF parameter])
  have d_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type d = d"
    by (rule pp_t_probe_successor_representative_aut_fixed[OF d])
  have character_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_symmetrized_singleton_family_at
            (pp_t_word_character_prop
              (pp_t_holds p [])
              (pp_t_holds p [True] \<noteq> pp_t_holds p [])
              (pp_t_holds p [False] \<noteq> pp_t_holds p [])))
        =
        pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))"
    using d_fixed equality family_eq by simp
  have reduced:
      "pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p [])))
      \<or>
      pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity"
    by (rule
      pp_t_fixed_canonical_character_family_reduction[
        OF character_fixed])
  show ?thesis
    using reduced family_eq by simp
qed

lemma pp_t_even_length_parity_view:
  "pp_t_cone_view s pp_t_even_length_parity
    =
    (if pp_t_word_character True True s
     then pp_t_complement pp_t_even_length_parity
     else pp_t_even_length_parity)"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_cone_view s pp_t_even_length_parity)
      (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  show "Elem
      (if pp_t_word_character True True s
       then pp_t_complement pp_t_even_length_parity
       else pp_t_even_length_parity)
      (pp_t_domain Prop)"
    using pp_t_even_length_parity_in_domain
      pp_t_complement_in_domain by simp
  fix u
  show "pp_t_holds
        (pp_t_cone_view s pp_t_even_length_parity) u
      =
      pp_t_holds
        (if pp_t_word_character True True s
         then pp_t_complement pp_t_even_length_parity
         else pp_t_even_length_parity) u"
    using pp_t_word_character_append[
      of True True s u]
    by (simp add: pp_t_even_length_parity_def)
qed

lemma pp_t_symmetrized_singleton_even_length_family_cone_natural:
  "pp_t_cone_rel pp_t_boolean_probe_unary_type s
    (pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity)
    (pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity)"
proof -
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have related:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s
        ?L
        (pp_t_symmetrized_singleton_family_at
          (pp_t_cone_view s pp_t_even_length_parity))"
    by (rule pp_t_logical_family_at_cone_related[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical
        pp_t_even_length_parity_in_domain])
  have view_value:
      "pp_t_symmetrized_singleton_family_at
          (pp_t_cone_view s pp_t_even_length_parity)
        =
        ?L"
  proof (cases "pp_t_word_character True True s")
    case False
    then show ?thesis
      using pp_t_even_length_parity_view[of s] by simp
  next
    case True
    then show ?thesis
      using pp_t_even_length_parity_view[of s]
        pp_t_symmetrized_singleton_family_at_complement[
          OF pp_t_even_length_parity_in_domain]
      by simp
  qed
  show ?thesis
    using related view_value by simp
qed

lemma pp_t_even_length_family_holds_iff_view_family:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity \<acute> p) w
    \<longleftrightarrow>
    pp_t_symmetrized_singleton_family_at
        (pp_t_cone_view w p)
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  let ?q = "pp_t_cone_view w p"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have inputs: "pp_t_cone_rel Prop w p ?q"
    by simp
  have outputs:
      "pp_t_cone_rel Prop w (?L \<acute> p) (?L \<acute> ?q)"
    using
      pp_t_symmetrized_singleton_even_length_family_cone_natural
      p q inputs
    unfolding pp_t_cone_rel.simps(3)
    by blast
  have view_truth:
      "pp_t_holds (?L \<acute> p) w
        =
        pp_t_holds (?L \<acute> ?q) []"
  proof -
    have all:
        "\<forall>u. pp_t_holds (?L \<acute> p) (w @ u)
          =
          pp_t_holds (?L \<acute> ?q) u"
      using outputs unfolding pp_t_cone_rel.simps .
    show ?thesis
      using all[rule_format, of "[]"] by simp
  qed
  have root_truth:
      "pp_t_holds (?L \<acute> ?q) []
      \<longleftrightarrow>
      ?q = pp_t_even_length_parity
        \<or>
      ?q = pp_t_complement pp_t_even_length_parity"
  proof -
    have complement:
        "Elem (pp_t_complement pp_t_even_length_parity)
          (pp_t_domain Prop)"
      by (rule pp_t_complement_in_domain)
    show ?thesis
      using pp_t_symmetrized_singleton_family_at_apply_holds[
          OF pp_t_even_length_parity_in_domain q, of "[]"]
        pp_t_root_eqv_iff_eq[
          OF q pp_t_even_length_parity_in_domain]
        pp_t_root_eqv_iff_eq[OF q complement]
      by blast
  qed
  have family_value:
      "(?q = pp_t_even_length_parity
          \<or>
        ?q = pp_t_complement pp_t_even_length_parity)
      \<longleftrightarrow>
      pp_t_symmetrized_singleton_family_at ?q = ?L"
  proof
    assume pair:
        "?q = pp_t_even_length_parity
          \<or>
        ?q = pp_t_complement pp_t_even_length_parity"
    from pair show
        "pp_t_symmetrized_singleton_family_at ?q = ?L"
    proof
      assume "?q = pp_t_even_length_parity"
      then show ?thesis by simp
    next
      assume
          "?q = pp_t_complement pp_t_even_length_parity"
      then show ?thesis
        using pp_t_symmetrized_singleton_family_at_complement[
          OF pp_t_even_length_parity_in_domain]
        by simp
    qed
  next
    assume equality:
        "pp_t_symmetrized_singleton_family_at ?q = ?L"
    show "?q = pp_t_even_length_parity
        \<or>
        ?q = pp_t_complement pp_t_even_length_parity"
      by (rule
        pp_t_symmetrized_family_values_equal_imp_parameter_pair[
          OF pp_t_even_length_parity_in_domain q equality])
  qed
  show ?thesis
    using view_truth root_truth family_value by blast
qed

theorem pp_t_probe_successor_family_membership_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_probe_successor_stock w
      (pp_t_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_probe_boolean_stock w
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    (pp_t_probe_successor_stock []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) w)"
proof -
  let ?q = "pp_t_cone_view w p"
  let ?Fp = "pp_t_symmetrized_singleton_family_at p"
  let ?Fq = "pp_t_symmetrized_singleton_family_at ?q"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have Fp:
      "Elem ?Fp (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
  have Fq:
      "Elem ?Fq (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF q])
  have family_cone:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type w ?Fp ?Fq"
    by (rule pp_t_logical_family_at_cone_related[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical p])
  show ?thesis
  proof
    assume stock: "pp_t_probe_successor_stock w ?Fp"
    have q_stock: "pp_t_probe_successor_stock [] ?Fq"
      using pp_t_probe_successor_stock_cone_iff[
        OF Fp Fq family_cone, of "[]"] stock
      by simp
    have reduced:
        "pp_t_probe_boolean_stock [] ?Fq \<or> ?Fq = ?L"
      by (rule
        pp_t_probe_successor_family_membership_reduction_at_root[
          OF q q_stock])
    from reduced show "pp_t_probe_boolean_stock w ?Fp
        \<or>
        (pp_t_probe_successor_stock [] ?L
          \<and> pp_t_holds (?L \<acute> p) w)"
    proof
      assume old_root: "pp_t_probe_boolean_stock [] ?Fq"
      have old:
          "pp_t_probe_boolean_stock w ?Fp"
        using pp_t_probe_boolean_stock_cone_iff[
          OF Fp Fq family_cone, of "[]"] old_root
        by simp
      then show ?thesis by blast
    next
      assume q_length: "?Fq = ?L"
      have L_stock: "pp_t_probe_successor_stock [] ?L"
        using q_stock q_length by simp
      have L_holds: "pp_t_holds (?L \<acute> p) w"
        using pp_t_even_length_family_holds_iff_view_family[
          OF p, of w] q_length
        by simp
      show ?thesis using L_stock L_holds by blast
    qed
  next
    assume right:
        "pp_t_probe_boolean_stock w ?Fp
        \<or>
        (pp_t_probe_successor_stock [] ?L
          \<and> pp_t_holds (?L \<acute> p) w)"
    from right show "pp_t_probe_successor_stock w ?Fp"
    proof
      assume old: "pp_t_probe_boolean_stock w ?Fp"
      show ?thesis
        by (rule
          pp_t_probe_boolean_stock_subset_successor_stock[OF old])
    next
      assume new:
          "pp_t_probe_successor_stock [] ?L
            \<and> pp_t_holds (?L \<acute> p) w"
      then have L_stock: "pp_t_probe_successor_stock [] ?L"
        and L_holds: "pp_t_holds (?L \<acute> p) w"
        by blast+
      have q_length: "?Fq = ?L"
        using pp_t_even_length_family_holds_iff_view_family[
          OF p, of w] L_holds
        by simp
      have q_stock: "pp_t_probe_successor_stock [] ?Fq"
        using L_stock q_length by simp
      show ?thesis
        using pp_t_probe_successor_stock_cone_iff[
          OF Fp Fq family_cone, of "[]"] q_stock
        by simp
    qed
  qed
qed

section \<open>Closure of the successor classifier cycle\<close>

definition pp_t_probe_successor_family_probe :: ZF where
  "pp_t_probe_successor_family_probe =
    pp_t_family_probe_for_stock
      pp_t_probe_successor_stock
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_probe_successor_family_probe_in_domain:
  "Elem pp_t_probe_successor_family_probe
    (pp_t_domain pp_t_boolean_probe_unary_type)"
  unfolding pp_t_probe_successor_family_probe_def
  by (rule pp_t_family_probe_for_stock_in_domain[
    OF pp_t_symmetrized_singleton_family_builder_typed
      pp_t_probe_successor_stock_admissible])

lemma pp_t_probe_successor_family_probe_holds_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_probe_successor_family_probe \<acute> p) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_probe_boolean_family_probe \<acute> p) w
    \<or>
    (pp_t_probe_successor_stock []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) w)"
proof -
  have successor:
      "pp_t_holds
          (pp_t_probe_successor_family_probe \<acute> p) w
      \<longleftrightarrow>
      pp_t_probe_successor_stock w
        (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_probe_successor_family_probe_def
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_successor_stock_admissible p])
  have prior:
      "pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> p) w
      \<longleftrightarrow>
      pp_t_probe_boolean_stock w
        (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_probe_boolean_family_probe_def
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_boolean_stock_admissible p])
  show ?thesis
    using successor prior
      pp_t_probe_successor_family_membership_iff[OF p, of w]
    by blast
qed

lemma pp_t_unary_output_conjunction_apply_holds:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
        \<acute> p) w
    \<longleftrightarrow>
    pp_t_holds (X \<acute> p) w \<and> pp_t_holds (Y \<acute> p) w"
  unfolding pp_t_unary_output_conjunction_def
    pp_t_closed_den_def
  using X Y p
  by (simp add: Lambda_app)

definition pp_t_unary_output_disjunction ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_unary_output_disjunction X Y =
    pp_t_unary_complement
      ((pp_t_unary_output_conjunction_den
          \<acute> pp_t_unary_complement X)
        \<acute> pp_t_unary_complement Y)"

lemma pp_t_unary_output_disjunction_in_domain:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
  shows "Elem (pp_t_unary_output_disjunction X Y)
    (pp_t_domain pp_t_boolean_probe_unary_type)"
proof -
  have nX:
      "Elem (pp_t_unary_complement X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF X])
  have nY:
      "Elem (pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF Y])
  have first:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_unary_complement X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain nX])
  have conjunction:
      "Elem
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF first nY])
  show ?thesis
    unfolding pp_t_unary_output_disjunction_def
    by (rule pp_t_unary_complement_in_domain[OF conjunction])
qed

lemma pp_t_unary_output_disjunction_apply_holds:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_unary_output_disjunction X Y \<acute> p) w
    \<longleftrightarrow>
    pp_t_holds (X \<acute> p) w \<or> pp_t_holds (Y \<acute> p) w"
proof -
  have nX:
      "Elem (pp_t_unary_complement X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF X])
  have nY:
      "Elem (pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF Y])
  have first:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_unary_complement X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain nX])
  have conjunction:
      "Elem
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF first nY])
  have conjunction_holds:
      "pp_t_holds
        (((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y) \<acute> p) w
      \<longleftrightarrow>
      pp_t_holds (pp_t_unary_complement X \<acute> p) w
        \<and>
      pp_t_holds (pp_t_unary_complement Y \<acute> p) w"
    by (rule pp_t_unary_output_conjunction_apply_holds[
      OF nX nY p])
  have nX_holds:
      "pp_t_holds (pp_t_unary_complement X \<acute> p) w
        =
        (\<not> pp_t_holds (X \<acute> p) w)"
    unfolding pp_t_unary_complement_apply[OF p]
    by simp
  have nY_holds:
      "pp_t_holds (pp_t_unary_complement Y \<acute> p) w
        =
        (\<not> pp_t_holds (Y \<acute> p) w)"
    unfolding pp_t_unary_complement_apply[OF p]
    by simp
  have outer_holds:
      "pp_t_holds
        (pp_t_unary_output_disjunction X Y \<acute> p) w
      =
      (\<not>
        pp_t_holds
          (((pp_t_unary_output_conjunction_den
              \<acute> pp_t_unary_complement X)
            \<acute> pp_t_unary_complement Y) \<acute> p) w)"
    unfolding pp_t_unary_output_disjunction_def
      pp_t_unary_complement_apply[OF p]
    by simp
  show ?thesis
    using conjunction_holds nX_holds nY_holds outer_holds
    by blast
qed

lemma pp_t_probe_successor_stock_persistent:
  assumes stock: "pp_t_probe_successor_stock w X"
    and future: "prefix w v"
  shows "pp_t_probe_successor_stock v X"
proof -
  obtain d where X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and d: "d \<in> pp_t_probe_successor_representatives"
    and Xd:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X d"
    using stock unfolding pp_t_probe_successor_stock_def by blast
  have Xd_v:
      "pp_t_eqv pp_t_boolean_probe_unary_type v X d"
    by (rule pp_t_eqv_persistent[OF Xd future])
  show ?thesis
    unfolding pp_t_probe_successor_stock_def
    using X d Xd_v by blast
qed

lemma pp_t_probe_successor_stock_unary_complement_closed:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and stock: "pp_t_probe_successor_stock w X"
  shows "pp_t_probe_successor_stock w
    (pp_t_unary_complement X)"
proof -
  have negated:
      "pp_t_probe_successor_stock w
        (pp_t_closed_den pp_t_unary_output_negator \<acute> X)"
    by (rule
      pp_t_probe_successor_stock_output_negation_closed[OF stock])
  show ?thesis
    using negated pp_t_unary_output_negator_apply[OF X]
    by simp
qed

lemma pp_t_probe_successor_disjunction_in_stock:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and X_stock: "pp_t_probe_successor_stock w X"
    and Y_stock: "pp_t_probe_successor_stock w Y"
  shows "pp_t_probe_successor_stock w
    (pp_t_unary_output_disjunction X Y)"
proof -
  have nX:
      "Elem (pp_t_unary_complement X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF X])
  have nY:
      "Elem (pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_complement_in_domain[OF Y])
  have nX_stock:
      "pp_t_probe_successor_stock w (pp_t_unary_complement X)"
    by (rule
      pp_t_probe_successor_stock_unary_complement_closed[
        OF X X_stock])
  have nY_stock:
      "pp_t_probe_successor_stock w (pp_t_unary_complement Y)"
    by (rule
      pp_t_probe_successor_stock_unary_complement_closed[
        OF Y Y_stock])
  have conjunction_stock:
      "pp_t_probe_successor_stock w
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y)"
    by (rule
      pp_t_probe_successor_stock_output_conjunction_closed[
        OF nX_stock nY_stock])
  have conjunction_domain:
      "Elem
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
  proof -
    have first:
        "Elem
          (pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          (pp_t_domain pp_t_boolean_probe_transformer_type)"
      by (rule pp_t_app_closed[
        OF pp_t_unary_output_conjunction_den_in_domain nX])
    show ?thesis by (rule pp_t_app_closed[OF first nY])
  qed
  show ?thesis
    unfolding pp_t_unary_output_disjunction_def
    by (rule
      pp_t_probe_successor_stock_unary_complement_closed[
        OF conjunction_domain conjunction_stock])
qed

lemma pp_t_probe_successor_family_probe_eq_prior_if_no_length:
  assumes no_length:
      "\<not> pp_t_probe_successor_stock []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
  shows "pp_t_probe_successor_family_probe
    = pp_t_probe_boolean_family_probe"
proof (rule pp_t_unary_function_ext)
  show "Elem pp_t_probe_successor_family_probe
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_family_probe_in_domain)
  show "Elem pp_t_probe_boolean_family_probe
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_family_probe_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_probe_successor_family_probe \<acute> p
      = pp_t_probe_boolean_family_probe \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_probe_successor_family_probe \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_probe_successor_family_probe_in_domain p])
    show "Elem (pp_t_probe_boolean_family_probe \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_probe_boolean_family_probe_in_domain p])
    fix w
    show "pp_t_holds
          (pp_t_probe_successor_family_probe \<acute> p) w
        =
        pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> p) w"
      using pp_t_probe_successor_family_probe_holds_iff[
        OF p, of w] no_length
      by blast
  qed
qed

lemma pp_t_probe_successor_family_probe_eq_disjunction_if_length:
  assumes length:
      "pp_t_probe_successor_stock []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
  shows "pp_t_probe_successor_family_probe
    =
    pp_t_unary_output_disjunction
      pp_t_probe_boolean_family_probe
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)"
proof (rule pp_t_unary_function_ext)
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  show "Elem pp_t_probe_successor_family_probe
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_family_probe_in_domain)
  show "Elem
      (pp_t_unary_output_disjunction
        pp_t_probe_boolean_family_probe ?L)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_output_disjunction_in_domain[
      OF pp_t_probe_boolean_family_probe_in_domain
        pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_even_length_parity_in_domain]])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_probe_successor_family_probe \<acute> p
      =
      pp_t_unary_output_disjunction
        pp_t_probe_boolean_family_probe ?L \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem (pp_t_probe_successor_family_probe \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_probe_successor_family_probe_in_domain p])
    show "Elem
        (pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_unary_output_disjunction_in_domain[
          OF pp_t_probe_boolean_family_probe_in_domain
            pp_t_symmetrized_singleton_family_at_in_domain[
              OF pp_t_even_length_parity_in_domain]]
          p])
    fix w
    show "pp_t_holds
          (pp_t_probe_successor_family_probe \<acute> p) w
        =
        pp_t_holds
          (pp_t_unary_output_disjunction
            pp_t_probe_boolean_family_probe ?L \<acute> p) w"
      using pp_t_probe_successor_family_probe_holds_iff[
          OF p, of w]
        pp_t_unary_output_disjunction_apply_holds[
          OF pp_t_probe_boolean_family_probe_in_domain
            pp_t_symmetrized_singleton_family_at_in_domain[
              OF pp_t_even_length_parity_in_domain]
            p,
          of w]
        length
      by blast
  qed
qed

theorem pp_t_probe_successor_family_probe_in_stock_at_root:
  "pp_t_probe_successor_stock []
    pp_t_probe_successor_family_probe"
proof (cases
    "pp_t_probe_successor_stock []
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)")
  case False
  have equality:
      "pp_t_probe_successor_family_probe
        = pp_t_probe_boolean_family_probe"
    by (rule
      pp_t_probe_successor_family_probe_eq_prior_if_no_length[
        OF False])
  show ?thesis
    unfolding equality
    by (rule pp_t_probe_boolean_family_probe_in_successor_stock)
next
  case True
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have Q_stock:
      "pp_t_probe_successor_stock []
        pp_t_probe_boolean_family_probe"
    by (rule pp_t_probe_boolean_family_probe_in_successor_stock)
  have disjunction_stock:
      "pp_t_probe_successor_stock []
        (pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L)"
    by (rule pp_t_probe_successor_disjunction_in_stock[
      OF pp_t_probe_boolean_family_probe_in_domain
        pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_even_length_parity_in_domain]
        Q_stock True])
  have equality:
      "pp_t_probe_successor_family_probe
        =
        pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L"
    by (rule
      pp_t_probe_successor_family_probe_eq_disjunction_if_length[
        OF True])
  show ?thesis
    using disjunction_stock unfolding equality .
qed

theorem pp_t_probe_successor_family_probe_in_stock:
  "pp_t_probe_successor_stock w
    pp_t_probe_successor_family_probe"
  by (rule pp_t_probe_successor_stock_persistent[
    OF pp_t_probe_successor_family_probe_in_stock_at_root])
    simp

theorem pp_t_probe_successor_stock_classifier_fixed_point_on_domain:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
  shows "pp_t_family_probe_stock_enlargement
        pp_t_probe_successor_stock
        pp_t_symmetrized_singleton_family_builder w X
      =
      pp_t_probe_successor_stock w X"
proof
    assume enlarged:
        "pp_t_family_probe_stock_enlargement
          pp_t_probe_successor_stock
          pp_t_symmetrized_singleton_family_builder w X"
    from enlarged consider
        (old) "pp_t_probe_successor_stock w X"
      | (new)
          "pp_t_eqv pp_t_boolean_probe_unary_type w
            pp_t_probe_successor_family_probe X"
      unfolding pp_t_family_probe_stock_enlargement_def
        pp_t_probe_successor_family_probe_def
      by blast
    then show "pp_t_probe_successor_stock w X"
    proof cases
      case old
      then show ?thesis .
    next
      case new
      have probe:
          "Elem pp_t_probe_successor_family_probe
            (pp_t_domain pp_t_boolean_probe_unary_type)"
        by (rule pp_t_probe_successor_family_probe_in_domain)
      have same:
          "pp_t_probe_successor_stock w
              pp_t_probe_successor_family_probe
            =
            pp_t_probe_successor_stock w X"
        using pp_t_probe_successor_stock_admissible
          probe X new
        unfolding pp_t_predicate_admissible_def
        by (metis prefix_order.refl)
      show ?thesis
        using same pp_t_probe_successor_family_probe_in_stock
        by blast
    qed
  next
    assume stock: "pp_t_probe_successor_stock w X"
    show "pp_t_family_probe_stock_enlargement
        pp_t_probe_successor_stock
        pp_t_symmetrized_singleton_family_builder w X"
      unfolding pp_t_family_probe_stock_enlargement_def
      using stock by blast
qed

theorem pp_t_probe_successor_family_probe_stabilizes:
  "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement
        pp_t_probe_successor_stock
        pp_t_symmetrized_singleton_family_builder)
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_probe_successor_family_probe"
proof -
  have collisions:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type w
          pp_t_probe_successor_family_probe
          (pp_t_closed_den
            pp_t_symmetrized_singleton_family_builder \<acute> p)
        \<longrightarrow>
        pp_t_probe_successor_stock w
          (pp_t_closed_den
            pp_t_symmetrized_singleton_family_builder \<acute> p)"
  proof (intro allI impI)
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_boolean_probe_unary_type w
          pp_t_probe_successor_family_probe
          (pp_t_closed_den
            pp_t_symmetrized_singleton_family_builder \<acute> p)"
    have Bp_domain:
        "Elem
          (pp_t_closed_den
            pp_t_symmetrized_singleton_family_builder \<acute> p)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_closed_den_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed] p])
    have same:
        "pp_t_probe_successor_stock w
            pp_t_probe_successor_family_probe
          =
          pp_t_probe_successor_stock w
            (pp_t_closed_den
              pp_t_symmetrized_singleton_family_builder \<acute> p)"
      using pp_t_probe_successor_stock_admissible
        pp_t_probe_successor_family_probe_in_domain
        Bp_domain collision
      unfolding pp_t_predicate_admissible_def
      by (metis prefix_order.refl)
    show "pp_t_probe_successor_stock w
        (pp_t_closed_den
          pp_t_symmetrized_singleton_family_builder \<acute> p)"
      using same pp_t_probe_successor_family_probe_in_stock
      by blast
  qed
  have stable:
      "pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement
            pp_t_probe_successor_stock
            pp_t_symmetrized_singleton_family_builder)
          pp_t_symmetrized_singleton_family_builder
        =
        pp_t_family_probe_for_stock
          pp_t_probe_successor_stock
          pp_t_symmetrized_singleton_family_builder"
    using collisions
      pp_t_family_probe_stabilizes_iff_collisions_absorbed[
        OF pp_t_symmetrized_singleton_family_builder_typed
          pp_t_probe_successor_stock_admissible]
    unfolding pp_t_probe_successor_family_probe_def
    by blast
  show ?thesis
    using stable
    unfolding pp_t_probe_successor_family_probe_def .
qed

section \<open>A Recombination seed for the stabilized successor stock\<close>

lemma pp_t_probe_successor_stock_root_represented:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and stock: "pp_t_probe_successor_stock [] X"
  obtains d where
    "d \<in> pp_t_probe_successor_representatives"
    "pp_t_eqv pp_t_boolean_probe_unary_type [] X d"
  using stock
  unfolding pp_t_probe_successor_stock_def
  by (blast intro: that)

theorem pp_t_probe_successor_stock_root_seed_exists:
  "\<exists>r. Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_successor_stock r []"
proof (rule
    pp_t_countably_represented_unary_stock_root_seed_exists[
      where D=pp_t_probe_successor_representatives])
  show "countable pp_t_probe_successor_representatives"
    by (rule pp_t_probe_successor_representatives_countable)
  show "\<And>d.
      d \<in> pp_t_probe_successor_representatives
      \<Longrightarrow>
      Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_successor_representative_in_domain)
  show "\<And>d.
      d \<in> pp_t_probe_successor_representatives
      \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    by (rule pp_t_probe_successor_representative_equivariant)
  show "\<And>X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<Longrightarrow> pp_t_probe_successor_stock [] X
      \<Longrightarrow>
      \<exists>d \<in> pp_t_probe_successor_representatives.
        pp_t_eqv pp_t_boolean_probe_unary_type [] X d"
    using pp_t_probe_successor_stock_root_represented
    by blast
qed

definition pp_t_probe_successor_stock_root_seed :: ZF where
  "pp_t_probe_successor_stock_root_seed =
    (SOME r. Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_probe_successor_stock r [])"

lemma pp_t_probe_successor_stock_root_seed_spec:
  "Elem pp_t_probe_successor_stock_root_seed
      (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_successor_stock
      pp_t_probe_successor_stock_root_seed []"
  unfolding pp_t_probe_successor_stock_root_seed_def
  using someI_ex[
    OF pp_t_probe_successor_stock_root_seed_exists] .

definition pp_t_probe_successor_stock_seed_at ::
    "bool list \<Rightarrow> ZF"
where
  "pp_t_probe_successor_stock_seed_at w =
    pp_t_cone_lift w pp_t_probe_successor_stock_root_seed"

lemma pp_t_probe_successor_stock_seed_at_in_domain:
  "Elem (pp_t_probe_successor_stock_seed_at w)
    (pp_t_domain Prop)"
  unfolding pp_t_probe_successor_stock_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem
    pp_t_probe_successor_stock_seed_recombines_at_every_world:
  "pp_t_unary_recombines_at
    pp_t_probe_successor_stock
    (pp_t_probe_successor_stock_seed_at w) w"
  unfolding pp_t_probe_successor_stock_seed_at_def
  by (rule
    pp_t_unary_stock_root_recombination_transports_to_cone[
      OF
        pp_t_probe_successor_stock_root_seed_spec[THEN conjunct1]
        pp_t_probe_successor_stock_root_seed_spec[THEN conjunct2]
        pp_t_probe_successor_stock_cone_iff])

end
