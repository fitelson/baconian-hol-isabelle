theory Bacon_PP_ZF_Tree_Modal_Boolean_Probe
  imports
    Higher_Order_Metaphysics_PP_ZF_Classifier_Stabilization.Bacon_PP_ZF_Tree_Classifier_Stabilization
begin

section \<open>Modal-Boolean closure of the stabilized unary stock\<close>

definition pp_t_unary_output_necessitation :: oterm where
  "pp_t_unary_output_necessitation =
    Lam pp_t_boolean_probe_unary_type
      (Lam Prop
        (\<box>\<^sub>o (App (Var 1) (Var 0))))"

lemma pp_t_unary_output_necessitation_typed:
  "[] \<turnstile> pp_t_unary_output_necessitation :
    pp_t_boolean_probe_transformer_type"
  unfolding pp_t_unary_output_necessitation_def
  apply (rule has_type.Lam)
  apply (rule has_type.Lam)
  apply (rule typed_ObjBox)
  apply (rule has_type.App)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Var)
  apply simp
  done

lemma pp_t_unary_output_necessitation_logical:
  "pp_logical_vocabulary pp_t_unary_output_necessitation"
  by (simp add: pp_t_unary_output_necessitation_def
      pp_logical_vocabulary_def ObjBox_def ObjTrue_def)

abbreviation pp_t_unary_output_necessitation_den :: ZF where
  "pp_t_unary_output_necessitation_den \<equiv>
    pp_t_closed_den pp_t_unary_output_necessitation"

lemma pp_t_unary_output_necessitation_den_in_domain:
  "Elem pp_t_unary_output_necessitation_den
    (pp_t_domain pp_t_boolean_probe_transformer_type)"
  by (rule pp_t_closed_den_in_domain)
    (rule pp_t_unary_output_necessitation_typed)

datatype pp_t_probe_modal_boolean_expr =
    PPProbeModalBooleanOld pp_t_probe_successor_expr
  | PPProbeModalBooleanNec pp_t_probe_modal_boolean_expr
  | PPProbeModalBooleanNeg pp_t_probe_modal_boolean_expr
  | PPProbeModalBooleanConj
      pp_t_probe_modal_boolean_expr pp_t_probe_modal_boolean_expr

instantiation pp_t_probe_modal_boolean_expr :: countable
begin

instance
  by countable_datatype

end

fun pp_t_probe_modal_boolean_expr_valid ::
    "pp_t_probe_modal_boolean_expr \<Rightarrow> bool"
where
  "pp_t_probe_modal_boolean_expr_valid
      (PPProbeModalBooleanOld E) =
    pp_t_probe_successor_expr_valid E"
| "pp_t_probe_modal_boolean_expr_valid
      (PPProbeModalBooleanNec E) =
    pp_t_probe_modal_boolean_expr_valid E"
| "pp_t_probe_modal_boolean_expr_valid
      (PPProbeModalBooleanNeg E) =
    pp_t_probe_modal_boolean_expr_valid E"
| "pp_t_probe_modal_boolean_expr_valid
      (PPProbeModalBooleanConj E F) =
    (pp_t_probe_modal_boolean_expr_valid E
      \<and> pp_t_probe_modal_boolean_expr_valid F)"

fun pp_t_probe_modal_boolean_expr_den ::
    "pp_t_probe_modal_boolean_expr \<Rightarrow> ZF"
where
  "pp_t_probe_modal_boolean_expr_den
      (PPProbeModalBooleanOld E) =
    pp_t_probe_successor_expr_den E"
| "pp_t_probe_modal_boolean_expr_den
      (PPProbeModalBooleanNec E) =
    pp_t_unary_output_necessitation_den
      \<acute> pp_t_probe_modal_boolean_expr_den E"
| "pp_t_probe_modal_boolean_expr_den
      (PPProbeModalBooleanNeg E) =
    pp_t_closed_den pp_t_unary_output_negator
      \<acute> pp_t_probe_modal_boolean_expr_den E"
| "pp_t_probe_modal_boolean_expr_den
      (PPProbeModalBooleanConj E F) =
    (pp_t_unary_output_conjunction_den
      \<acute> pp_t_probe_modal_boolean_expr_den E)
      \<acute> pp_t_probe_modal_boolean_expr_den F"

lemma pp_t_probe_modal_boolean_expr_den_in_domain:
  assumes valid: "pp_t_probe_modal_boolean_expr_valid E"
  shows "Elem (pp_t_probe_modal_boolean_expr_den E)
    (pp_t_domain pp_t_boolean_probe_unary_type)"
  using valid
proof (induction E)
  case (PPProbeModalBooleanOld E)
  then show ?case
    using pp_t_probe_successor_expr_den_in_domain by simp
next
  case (PPProbeModalBooleanNec E)
  then show ?case
    using pp_t_app_closed[
      OF pp_t_unary_output_necessitation_den_in_domain]
    by simp
next
  case (PPProbeModalBooleanNeg E)
  then show ?case
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[
        OF pp_t_unary_output_negator_typed]]
    by simp
next
  case (PPProbeModalBooleanConj E F)
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    using PPProbeModalBooleanConj by simp
  have F_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    using PPProbeModalBooleanConj by simp
  have first:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain])
  show ?case
    using pp_t_app_closed[OF first F_domain] by simp
qed

lemma pp_t_probe_modal_boolean_expr_den_cone_natural:
  assumes valid: "pp_t_probe_modal_boolean_expr_valid E"
  shows "pp_t_cone_rel pp_t_boolean_probe_unary_type s
    (pp_t_probe_modal_boolean_expr_den E)
    (pp_t_probe_modal_boolean_expr_den E)"
  using valid
proof (induction E)
  case (PPProbeModalBooleanOld E)
  then show ?case
    using pp_t_probe_successor_expr_den_cone_natural by simp
next
  case (PPProbeModalBooleanNec E)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    using PPProbeModalBooleanNec.prems by simp
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have operator_cone:
      "pp_t_cone_rel pp_t_boolean_probe_transformer_type s
        pp_t_unary_output_necessitation_den
        pp_t_unary_output_necessitation_den"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_unary_output_necessitation_typed
          pp_t_unary_output_necessitation_logical])
  show ?case
    using operator_cone
      pp_t_unary_output_necessitation_den_in_domain E_domain
      PPProbeModalBooleanNec.IH[OF E_valid]
    by auto
next
  case (PPProbeModalBooleanNeg E)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    using PPProbeModalBooleanNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have operator_domain:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have operator_cone:
      "pp_t_cone_rel pp_t_boolean_probe_transformer_type s
        (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_closed_den pp_t_unary_output_negator)"
    by (rule
      UnconditionalCone.pp_t_closed_logical_den_cone_related[
        OF pp_t_unary_output_negator_typed
          pp_t_unary_output_negator_logical])
  show ?case
    using operator_cone operator_domain E_domain
      PPProbeModalBooleanNeg.IH[OF E_valid]
    by auto
next
  case (PPProbeModalBooleanConj E F)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    and F_valid: "pp_t_probe_modal_boolean_expr_valid F"
    using PPProbeModalBooleanConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF F_valid])
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
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain])
  have first_cone:
      "pp_t_cone_rel pp_t_boolean_probe_transformer_type s
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)"
    using conjunction_cone
      pp_t_unary_output_conjunction_den_in_domain E_domain
      PPProbeModalBooleanConj.IH(1)[OF E_valid]
    by auto
  show ?case
    using first_cone first_domain F_domain
      PPProbeModalBooleanConj.IH(2)[OF F_valid]
    by auto
qed

lemma pp_t_probe_modal_boolean_expr_den_aut_fixed:
  assumes valid: "pp_t_probe_modal_boolean_expr_valid E"
  shows "pp_t_aut pp_t_boolean_probe_unary_type
      (pp_t_probe_modal_boolean_expr_den E)
    =
    pp_t_probe_modal_boolean_expr_den E"
  using valid
proof (induction E)
  case (PPProbeModalBooleanOld E)
  then show ?case
    using pp_t_probe_successor_expr_den_aut_fixed by simp
next
  case (PPProbeModalBooleanNec E)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    using PPProbeModalBooleanNec.prems by simp
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have operator_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          pp_t_unary_output_necessitation_den
        =
        pp_t_unary_output_necessitation_den"
    by (rule pp_t_closed_logical_den_aut_fixed[
      OF pp_t_unary_output_necessitation_typed
        pp_t_unary_output_necessitation_logical])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_unary_output_necessitation_den
            \<acute> pp_t_probe_modal_boolean_expr_den E)
        =
        pp_t_unary_output_necessitation_den
          \<acute> pp_t_probe_modal_boolean_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF pp_t_unary_output_necessitation_den_in_domain E_domain
        operator_fixed PPProbeModalBooleanNec.IH[OF E_valid]])
  show ?case using fixed by simp
next
  case (PPProbeModalBooleanNeg E)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    using PPProbeModalBooleanNeg.prems by simp
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have operator_domain:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have operator_fixed:
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
            \<acute> pp_t_probe_modal_boolean_expr_den E)
        =
        pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_modal_boolean_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF operator_domain E_domain operator_fixed
        PPProbeModalBooleanNeg.IH[OF E_valid]])
  show ?case using fixed by simp
next
  case (PPProbeModalBooleanConj E F)
  have E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    and F_valid: "pp_t_probe_modal_boolean_expr_valid F"
    using PPProbeModalBooleanConj.prems by simp_all
  have E_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have F_domain:
      "Elem (pp_t_probe_modal_boolean_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF F_valid])
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
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain])
  have first_fixed:
      "pp_t_aut pp_t_boolean_probe_transformer_type
          (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_modal_boolean_expr_den E)
        =
        pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E"
    by (rule pp_t_aut_fixed_application[
      OF pp_t_unary_output_conjunction_den_in_domain E_domain
        conjunction_fixed
        PPProbeModalBooleanConj.IH(1)[OF E_valid]])
  have fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          ((pp_t_unary_output_conjunction_den
              \<acute> pp_t_probe_modal_boolean_expr_den E)
            \<acute> pp_t_probe_modal_boolean_expr_den F)
        =
        (pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_modal_boolean_expr_den E)
          \<acute> pp_t_probe_modal_boolean_expr_den F"
    by (rule pp_t_aut_fixed_application[
      OF first_domain F_domain first_fixed
        PPProbeModalBooleanConj.IH(2)[OF F_valid]])
  show ?case using fixed by simp
qed

definition pp_t_probe_modal_boolean_representatives :: "ZF set" where
  "pp_t_probe_modal_boolean_representatives =
    pp_t_probe_modal_boolean_expr_den `
      {E. pp_t_probe_modal_boolean_expr_valid E}"

lemma pp_t_probe_modal_boolean_representatives_countable:
  "countable pp_t_probe_modal_boolean_representatives"
  unfolding pp_t_probe_modal_boolean_representatives_def by simp

lemma pp_t_probe_modal_boolean_representative_in_domain:
  assumes d: "d \<in> pp_t_probe_modal_boolean_representatives"
  shows "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
  using d pp_t_probe_modal_boolean_expr_den_in_domain
  unfolding pp_t_probe_modal_boolean_representatives_def
  by blast

lemma pp_t_probe_modal_boolean_representative_cone_natural:
  assumes d: "d \<in> pp_t_probe_modal_boolean_representatives"
  shows "pp_t_cone_rel pp_t_boolean_probe_unary_type s d d"
  using d pp_t_probe_modal_boolean_expr_den_cone_natural
  unfolding pp_t_probe_modal_boolean_representatives_def
  by blast

lemma pp_t_probe_modal_boolean_representative_aut_fixed:
  assumes d: "d \<in> pp_t_probe_modal_boolean_representatives"
  shows "pp_t_aut pp_t_boolean_probe_unary_type d = d"
  using d pp_t_probe_modal_boolean_expr_den_aut_fixed
  unfolding pp_t_probe_modal_boolean_representatives_def
  by blast

lemma pp_t_probe_modal_boolean_representative_equivariant:
  assumes d: "d \<in> pp_t_probe_modal_boolean_representatives"
  shows "pp_b_equivariant (pp_b_operator_of d)"
  by (rule pp_t_cone_rel_operator_implies_equivariant)
    (rule
      pp_t_probe_modal_boolean_representative_cone_natural[OF d])

definition pp_t_probe_modal_boolean_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_modal_boolean_stock w X \<longleftrightarrow>
    Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
    \<and>
    (\<exists>d \<in> pp_t_probe_modal_boolean_representatives.
      pp_t_eqv pp_t_boolean_probe_unary_type w X d)"

lemma pp_t_probe_modal_boolean_stock_admissible:
  "pp_t_predicate_admissible pp_t_boolean_probe_unary_type
    pp_t_probe_modal_boolean_stock"
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
  show "pp_t_probe_modal_boolean_stock v X =
      pp_t_probe_modal_boolean_stock v Y"
  proof
    assume stock: "pp_t_probe_modal_boolean_stock v X"
    then obtain d where
        d: "d \<in> pp_t_probe_modal_boolean_representatives"
      and Xd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v X d"
      unfolding pp_t_probe_modal_boolean_stock_def by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_modal_boolean_representative_in_domain[OF d])
    have Yd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v Y d"
      by (rule pp_t_eqv_transitive[
        OF Y X d_domain YXv Xd])
    show "pp_t_probe_modal_boolean_stock v Y"
      unfolding pp_t_probe_modal_boolean_stock_def
      using Y d Yd by blast
  next
    assume stock: "pp_t_probe_modal_boolean_stock v Y"
    then obtain d where
        d: "d \<in> pp_t_probe_modal_boolean_representatives"
      and Yd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v Y d"
      unfolding pp_t_probe_modal_boolean_stock_def by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_modal_boolean_representative_in_domain[OF d])
    have Xd:
        "pp_t_eqv pp_t_boolean_probe_unary_type v X d"
      by (rule pp_t_eqv_transitive[
        OF X Y d_domain XYv Yd])
    show "pp_t_probe_modal_boolean_stock v X"
      unfolding pp_t_probe_modal_boolean_stock_def
      using X d Xd by blast
  qed
qed

lemma pp_t_probe_modal_boolean_stock_cone_iff:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and XY:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type s X Y"
  shows "pp_t_probe_modal_boolean_stock (s @ u) X
    \<longleftrightarrow> pp_t_probe_modal_boolean_stock u Y"
proof -
  have representative:
      "\<And>d.
        d \<in> pp_t_probe_modal_boolean_representatives
        \<Longrightarrow>
        (pp_t_eqv pp_t_boolean_probe_unary_type (s @ u) X d
        \<longleftrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type u Y d)"
  proof -
    fix d
    assume d: "d \<in> pp_t_probe_modal_boolean_representatives"
    have d_domain:
        "Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule
        pp_t_probe_modal_boolean_representative_in_domain[OF d])
    have d_cone:
        "pp_t_cone_rel pp_t_boolean_probe_unary_type s d d"
      by (rule
        pp_t_probe_modal_boolean_representative_cone_natural[OF d])
    show "pp_t_eqv pp_t_boolean_probe_unary_type (s @ u) X d
        \<longleftrightarrow>
        pp_t_eqv pp_t_boolean_probe_unary_type u Y d"
      using UnconditionalCone.pp_t_cone_rel_eqv_iff[
        OF X Y d_domain d_domain XY d_cone, of u] .
  qed
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using X Y representative by blast
qed

lemma pp_t_probe_successor_stock_subset_modal_boolean_stock:
  assumes stock: "pp_t_probe_successor_stock w X"
  shows "pp_t_probe_modal_boolean_stock w X"
proof -
  obtain E where
      valid: "pp_t_probe_successor_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_successor_expr_den E)"
    using stock by (rule pp_t_probe_successor_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_successor_stock_def by blast
  have representative:
      "pp_t_probe_successor_expr_den E
        \<in> pp_t_probe_modal_boolean_representatives"
  proof -
    have member:
        "PPProbeModalBooleanOld E
          \<in> {F. pp_t_probe_modal_boolean_expr_valid F}"
      using valid by simp
    have image:
        "pp_t_probe_modal_boolean_expr_den
            (PPProbeModalBooleanOld E)
          \<in> pp_t_probe_modal_boolean_expr_den `
            {F. pp_t_probe_modal_boolean_expr_valid F}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_modal_boolean_representatives_def
      by simp
  qed
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using X representative represented by blast
qed

lemma pp_t_probe_modal_boolean_stock_represented:
  assumes stock: "pp_t_probe_modal_boolean_stock w X"
  obtains E where
    "pp_t_probe_modal_boolean_expr_valid E"
    "pp_t_eqv pp_t_boolean_probe_unary_type w X
      (pp_t_probe_modal_boolean_expr_den E)"
  using stock
  unfolding pp_t_probe_modal_boolean_stock_def
    pp_t_probe_modal_boolean_representatives_def
  by (blast intro: that)

lemma pp_t_probe_modal_boolean_stock_necessitation_closed:
  assumes stock: "pp_t_probe_modal_boolean_stock w X"
  shows "pp_t_probe_modal_boolean_stock w
    (pp_t_unary_output_necessitation_den \<acute> X)"
proof -
  obtain E where valid: "pp_t_probe_modal_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_modal_boolean_expr_den E)"
    using stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have d:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF valid])
  have result:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_unary_output_necessitation_den \<acute> X)
        (pp_t_unary_output_necessitation_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_unary_output_necessitation_den_in_domain]
        X d represented])
  have result_domain:
      "Elem (pp_t_unary_output_necessitation_den \<acute> X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_necessitation_den_in_domain X])
  have representative:
      "pp_t_unary_output_necessitation_den
          \<acute> pp_t_probe_modal_boolean_expr_den E
        \<in> pp_t_probe_modal_boolean_representatives"
  proof -
    have member:
        "PPProbeModalBooleanNec E
          \<in> {F. pp_t_probe_modal_boolean_expr_valid F}"
      using valid by simp
    have image:
        "pp_t_probe_modal_boolean_expr_den
            (PPProbeModalBooleanNec E)
          \<in> pp_t_probe_modal_boolean_expr_den `
            {F. pp_t_probe_modal_boolean_expr_valid F}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_modal_boolean_representatives_def
      by simp
  qed
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using result_domain representative result by blast
qed

lemma pp_t_probe_modal_boolean_stock_negation_closed:
  assumes stock: "pp_t_probe_modal_boolean_stock w X"
  shows "pp_t_probe_modal_boolean_stock w
    (pp_t_closed_den pp_t_unary_output_negator \<acute> X)"
proof -
  obtain E where valid: "pp_t_probe_modal_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_modal_boolean_expr_den E)"
    using stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have d:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF valid])
  have N:
      "Elem (pp_t_closed_den pp_t_unary_output_negator)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_unary_output_negator_typed)
  have result:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_closed_den pp_t_unary_output_negator \<acute> X)
        (pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_modal_boolean_expr_den E)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[OF N] X d represented])
  have result_domain:
      "Elem (pp_t_closed_den pp_t_unary_output_negator \<acute> X)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF N X])
  have representative:
      "pp_t_closed_den pp_t_unary_output_negator
          \<acute> pp_t_probe_modal_boolean_expr_den E
        \<in> pp_t_probe_modal_boolean_representatives"
  proof -
    have member:
        "PPProbeModalBooleanNeg E
          \<in> {F. pp_t_probe_modal_boolean_expr_valid F}"
      using valid by simp
    have image:
        "pp_t_probe_modal_boolean_expr_den
            (PPProbeModalBooleanNeg E)
          \<in> pp_t_probe_modal_boolean_expr_den `
            {F. pp_t_probe_modal_boolean_expr_valid F}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_modal_boolean_representatives_def
      by simp
  qed
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using result_domain representative result by blast
qed

lemma pp_t_probe_modal_boolean_stock_conjunction_closed:
  assumes X_stock: "pp_t_probe_modal_boolean_stock w X"
    and Y_stock: "pp_t_probe_modal_boolean_stock w Y"
  shows "pp_t_probe_modal_boolean_stock w
    ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)"
proof -
  obtain E where E_valid: "pp_t_probe_modal_boolean_expr_valid E"
    and X_represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w X
        (pp_t_probe_modal_boolean_expr_den E)"
    using X_stock by (rule pp_t_probe_modal_boolean_stock_represented)
  obtain F where F_valid: "pp_t_probe_modal_boolean_expr_valid F"
    and Y_represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type w Y
        (pp_t_probe_modal_boolean_expr_den F)"
    using Y_stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using X_stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    using Y_stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have dE:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF E_valid])
  have dF:
      "Elem (pp_t_probe_modal_boolean_expr_den F)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF F_valid])
  have first:
      "pp_t_eqv pp_t_boolean_probe_transformer_type w
        (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)"
    by (rule pp_t_app_respects[
      OF pp_t_eqv_reflexive[
          OF pp_t_unary_output_conjunction_den_in_domain]
        X dE X_represented])
  have first_X:
      "Elem (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain X])
  have first_E:
      "Elem
        (pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[
      OF pp_t_unary_output_conjunction_den_in_domain dE])
  have result:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_probe_modal_boolean_expr_den E)
          \<acute> pp_t_probe_modal_boolean_expr_den F)"
    by (rule pp_t_app_respects[
      OF first Y dF Y_represented])
  have result_domain:
      "Elem ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF first_X Y])
  have representative:
      "(pp_t_unary_output_conjunction_den
          \<acute> pp_t_probe_modal_boolean_expr_den E)
        \<acute> pp_t_probe_modal_boolean_expr_den F
      \<in> pp_t_probe_modal_boolean_representatives"
  proof -
    have member:
        "PPProbeModalBooleanConj E F
          \<in> {G. pp_t_probe_modal_boolean_expr_valid G}"
      using E_valid F_valid by simp
    have image:
        "pp_t_probe_modal_boolean_expr_den
            (PPProbeModalBooleanConj E F)
          \<in> pp_t_probe_modal_boolean_expr_den `
            {G. pp_t_probe_modal_boolean_expr_valid G}"
      by (rule imageI[OF member])
    show ?thesis
      using image
      unfolding pp_t_probe_modal_boolean_representatives_def
      by simp
  qed
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using result_domain representative result by blast
qed

lemma pp_t_probe_modal_boolean_stock_persistent:
  assumes stock: "pp_t_probe_modal_boolean_stock [] X"
  shows "pp_t_probe_modal_boolean_stock w X"
proof -
  obtain E where valid: "pp_t_probe_modal_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        X (pp_t_probe_modal_boolean_expr_den E)"
    using stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have representative:
      "pp_t_probe_modal_boolean_expr_den E
        \<in> pp_t_probe_modal_boolean_representatives"
    unfolding pp_t_probe_modal_boolean_representatives_def
    using valid by blast
  have represented_w:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        X (pp_t_probe_modal_boolean_expr_den E)"
    by (rule pp_t_eqv_persistent[OF represented])
      simp
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using X representative represented_w by blast
qed

lemma pp_t_probe_modal_boolean_stock_root_member_cone_natural:
  assumes stock: "pp_t_probe_modal_boolean_stock [] X"
  shows "pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
proof -
  obtain E where valid: "pp_t_probe_modal_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        X (pp_t_probe_modal_boolean_expr_den E)"
    using stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have d:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF valid])
  have equality: "X = pp_t_probe_modal_boolean_expr_den E"
    by (rule pp_t_root_eqv_imp_eq[OF X d represented])
  show ?thesis
    unfolding equality
    by (rule pp_t_probe_modal_boolean_expr_den_cone_natural[OF valid])
qed

lemma pp_t_probe_modal_boolean_stock_root_member_aut_fixed:
  assumes stock: "pp_t_probe_modal_boolean_stock [] X"
  shows "pp_t_aut pp_t_boolean_probe_unary_type X = X"
proof -
  obtain E where valid: "pp_t_probe_modal_boolean_expr_valid E"
    and represented:
      "pp_t_eqv pp_t_boolean_probe_unary_type []
        X (pp_t_probe_modal_boolean_expr_den E)"
    using stock by (rule pp_t_probe_modal_boolean_stock_represented)
  have X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock unfolding pp_t_probe_modal_boolean_stock_def by blast
  have d:
      "Elem (pp_t_probe_modal_boolean_expr_den E)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_expr_den_in_domain[OF valid])
  have equality: "X = pp_t_probe_modal_boolean_expr_den E"
    by (rule pp_t_root_eqv_imp_eq[OF X d represented])
  show ?thesis
    unfolding equality
    by (rule pp_t_probe_modal_boolean_expr_den_aut_fixed[OF valid])
qed

lemma pp_t_probe_modal_boolean_stock_unary_complement_closed:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and stock: "pp_t_probe_modal_boolean_stock w X"
  shows "pp_t_probe_modal_boolean_stock w
    (pp_t_unary_complement X)"
proof -
  have negated:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_closed_den pp_t_unary_output_negator \<acute> X)"
    by (rule pp_t_probe_modal_boolean_stock_negation_closed[OF stock])
  show ?thesis
    using negated pp_t_unary_output_negator_apply[OF X]
    by simp
qed

lemma pp_t_probe_modal_boolean_stock_disjunction_closed:
  assumes X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and X_stock: "pp_t_probe_modal_boolean_stock w X"
    and Y_stock: "pp_t_probe_modal_boolean_stock w Y"
  shows "pp_t_probe_modal_boolean_stock w
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
      "pp_t_probe_modal_boolean_stock w
        (pp_t_unary_complement X)"
    by (rule pp_t_probe_modal_boolean_stock_unary_complement_closed[
      OF X X_stock])
  have nY_stock:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_unary_complement Y)"
    by (rule pp_t_probe_modal_boolean_stock_unary_complement_closed[
      OF Y Y_stock])
  have conjunction_stock:
      "pp_t_probe_modal_boolean_stock w
        ((pp_t_unary_output_conjunction_den
            \<acute> pp_t_unary_complement X)
          \<acute> pp_t_unary_complement Y)"
    by (rule pp_t_probe_modal_boolean_stock_conjunction_closed[
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
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF conjunction_domain conjunction_stock])
qed

definition pp_t_probe_modal_boolean_family_probe :: ZF where
  "pp_t_probe_modal_boolean_family_probe =
    pp_t_family_probe_for_stock
      pp_t_probe_modal_boolean_stock
      pp_t_symmetrized_singleton_family_builder"

lemma pp_t_probe_modal_boolean_family_probe_in_domain:
  "Elem pp_t_probe_modal_boolean_family_probe
    (pp_t_domain pp_t_boolean_probe_unary_type)"
  unfolding pp_t_probe_modal_boolean_family_probe_def
  by (rule pp_t_family_probe_for_stock_in_domain[
    OF pp_t_symmetrized_singleton_family_builder_typed
      pp_t_probe_modal_boolean_stock_admissible])

lemma pp_t_probe_modal_boolean_family_probe_in_stock_at_root:
  "pp_t_probe_modal_boolean_stock []
    pp_t_probe_modal_boolean_family_probe"
  unfolding pp_t_probe_modal_boolean_family_probe_def
proof (rule
    pp_t_invariant_boolean_stock_absorbs_family_probe_at_root)
  show "pp_t_predicate_admissible
      pp_t_boolean_probe_unary_type
      pp_t_probe_modal_boolean_stock"
    by (rule pp_t_probe_modal_boolean_stock_admissible)
  fix X
  assume old: "pp_t_probe_boolean_stock [] X"
  show "pp_t_probe_modal_boolean_stock [] X"
    by (rule pp_t_probe_successor_stock_subset_modal_boolean_stock)
      (rule pp_t_probe_boolean_stock_subset_successor_stock[OF old])
next
  fix X s
  assume stock: "pp_t_probe_modal_boolean_stock [] X"
  show "pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    by (rule
      pp_t_probe_modal_boolean_stock_root_member_cone_natural[OF stock])
next
  fix X
  assume stock: "pp_t_probe_modal_boolean_stock [] X"
  show "pp_t_aut pp_t_boolean_probe_unary_type X = X"
    by (rule
      pp_t_probe_modal_boolean_stock_root_member_aut_fixed[OF stock])
next
  fix w X Y
  assume X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and XY: "pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y"
  show "pp_t_probe_modal_boolean_stock w X
      \<longleftrightarrow>
      pp_t_probe_modal_boolean_stock [] Y"
    using pp_t_probe_modal_boolean_stock_cone_iff[
      OF X Y XY, of "[]"]
    by simp
next
  show "pp_t_probe_modal_boolean_stock []
      pp_t_probe_boolean_family_probe"
    by (rule pp_t_probe_successor_stock_subset_modal_boolean_stock)
      (rule pp_t_probe_boolean_family_probe_in_successor_stock)
next
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and X_stock: "pp_t_probe_modal_boolean_stock [] X"
    and Y_stock: "pp_t_probe_modal_boolean_stock [] Y"
  show "pp_t_probe_modal_boolean_stock []
      (pp_t_unary_output_disjunction X Y)"
    by (rule pp_t_probe_modal_boolean_stock_disjunction_closed[
      OF X Y X_stock Y_stock])
qed

lemma pp_t_probe_modal_boolean_family_probe_in_stock:
  "pp_t_probe_modal_boolean_stock w
    pp_t_probe_modal_boolean_family_probe"
  by (rule pp_t_probe_modal_boolean_stock_persistent[
    OF pp_t_probe_modal_boolean_family_probe_in_stock_at_root])

lemma pp_t_probe_modal_boolean_complemented_probe_eq:
  "pp_t_family_probe_for_stock
      pp_t_probe_modal_boolean_stock
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_probe_modal_boolean_family_probe"
  unfolding pp_t_probe_modal_boolean_family_probe_def
  by (rule pp_t_negation_closed_stock_complemented_probe_eq[
    OF pp_t_probe_modal_boolean_stock_admissible
      pp_t_probe_modal_boolean_stock_unary_complement_closed])

lemma pp_t_probe_modal_boolean_complemented_probe_in_stock:
  "pp_t_probe_modal_boolean_stock w
    (pp_t_family_probe_for_stock
      pp_t_probe_modal_boolean_stock
      pp_t_complemented_symmetrized_singleton_family_builder)"
  unfolding pp_t_probe_modal_boolean_complemented_probe_eq
  by (rule pp_t_probe_modal_boolean_family_probe_in_stock)

theorem
  pp_t_probe_modal_boolean_complemented_classifier_fixed_point:
  "(\<forall>w X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement
          pp_t_probe_modal_boolean_stock
          pp_t_complemented_symmetrized_singleton_family_builder
          w X
        \<longleftrightarrow>
        pp_t_probe_modal_boolean_stock w X))
    \<and>
    pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement
          pp_t_probe_modal_boolean_stock
          pp_t_complemented_symmetrized_singleton_family_builder)
        pp_t_complemented_symmetrized_singleton_family_builder
      =
      pp_t_family_probe_for_stock
        pp_t_probe_modal_boolean_stock
        pp_t_complemented_symmetrized_singleton_family_builder"
  by (rule pp_t_family_probe_in_stock_implies_fixed_point[
    OF
      pp_t_complemented_symmetrized_singleton_family_builder_typed
      pp_t_probe_modal_boolean_stock_admissible
      pp_t_probe_modal_boolean_complemented_probe_in_stock])

theorem pp_t_probe_modal_boolean_stock_classifier_fixed_point:
  "(\<forall>w X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement
          pp_t_probe_modal_boolean_stock
          pp_t_symmetrized_singleton_family_builder w X
        \<longleftrightarrow>
        pp_t_probe_modal_boolean_stock w X))
    \<and>
    pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement
          pp_t_probe_modal_boolean_stock
          pp_t_symmetrized_singleton_family_builder)
        pp_t_symmetrized_singleton_family_builder
      =
      pp_t_family_probe_for_stock
        pp_t_probe_modal_boolean_stock
        pp_t_symmetrized_singleton_family_builder"
proof (rule pp_t_invariant_boolean_stock_classifier_fixed_point)
  show "pp_t_predicate_admissible
      pp_t_boolean_probe_unary_type
      pp_t_probe_modal_boolean_stock"
    by (rule pp_t_probe_modal_boolean_stock_admissible)
  fix X
  assume old: "pp_t_probe_boolean_stock [] X"
  show "pp_t_probe_modal_boolean_stock [] X"
    by (rule pp_t_probe_successor_stock_subset_modal_boolean_stock)
      (rule pp_t_probe_boolean_stock_subset_successor_stock[OF old])
next
  fix X s
  assume stock: "pp_t_probe_modal_boolean_stock [] X"
  show "pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    by (rule
      pp_t_probe_modal_boolean_stock_root_member_cone_natural[OF stock])
next
  fix X
  assume stock: "pp_t_probe_modal_boolean_stock [] X"
  show "pp_t_aut pp_t_boolean_probe_unary_type X = X"
    by (rule
      pp_t_probe_modal_boolean_stock_root_member_aut_fixed[OF stock])
next
  fix w X Y
  assume X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and XY: "pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y"
  show "pp_t_probe_modal_boolean_stock w X
      \<longleftrightarrow>
      pp_t_probe_modal_boolean_stock [] Y"
    using pp_t_probe_modal_boolean_stock_cone_iff[
      OF X Y XY, of "[]"]
    by simp
next
  show "pp_t_probe_modal_boolean_stock []
      pp_t_probe_boolean_family_probe"
    by (rule pp_t_probe_successor_stock_subset_modal_boolean_stock)
      (rule pp_t_probe_boolean_family_probe_in_successor_stock)
next
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and X_stock: "pp_t_probe_modal_boolean_stock [] X"
    and Y_stock: "pp_t_probe_modal_boolean_stock [] Y"
  show "pp_t_probe_modal_boolean_stock []
      (pp_t_unary_output_disjunction X Y)"
    by (rule pp_t_probe_modal_boolean_stock_disjunction_closed[
      OF X Y X_stock Y_stock])
next
  fix w X
  assume stock: "pp_t_probe_modal_boolean_stock [] X"
  show "pp_t_probe_modal_boolean_stock w X"
    by (rule pp_t_probe_modal_boolean_stock_persistent[OF stock])
qed

section \<open>A Recombination seed for the modal-Boolean stock\<close>

lemma pp_t_probe_modal_boolean_stock_root_represented:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and stock: "pp_t_probe_modal_boolean_stock [] X"
  obtains d where
    "d \<in> pp_t_probe_modal_boolean_representatives"
    "pp_t_eqv pp_t_boolean_probe_unary_type [] X d"
  using stock
  unfolding pp_t_probe_modal_boolean_stock_def
  by (blast intro: that)

theorem pp_t_probe_modal_boolean_stock_root_seed_exists:
  "\<exists>r. Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock r []"
proof (rule
    pp_t_countably_represented_unary_stock_root_seed_exists[
      where D=pp_t_probe_modal_boolean_representatives])
  show "countable pp_t_probe_modal_boolean_representatives"
    by (rule pp_t_probe_modal_boolean_representatives_countable)
  show "\<And>d.
      d \<in> pp_t_probe_modal_boolean_representatives
      \<Longrightarrow>
      Elem d (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_modal_boolean_representative_in_domain)
  show "\<And>d.
      d \<in> pp_t_probe_modal_boolean_representatives
      \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    by (rule pp_t_probe_modal_boolean_representative_equivariant)
  show "\<And>X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<Longrightarrow> pp_t_probe_modal_boolean_stock [] X
      \<Longrightarrow>
      \<exists>d \<in> pp_t_probe_modal_boolean_representatives.
        pp_t_eqv pp_t_boolean_probe_unary_type [] X d"
    using pp_t_probe_modal_boolean_stock_root_represented
    by blast
qed

definition pp_t_probe_modal_boolean_stock_root_seed :: ZF where
  "pp_t_probe_modal_boolean_stock_root_seed =
    (SOME r. Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock r [])"

lemma pp_t_probe_modal_boolean_stock_root_seed_spec:
  "Elem pp_t_probe_modal_boolean_stock_root_seed
      (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock
      pp_t_probe_modal_boolean_stock_root_seed []"
  unfolding pp_t_probe_modal_boolean_stock_root_seed_def
  using someI_ex[
    OF pp_t_probe_modal_boolean_stock_root_seed_exists] .

definition pp_t_probe_modal_boolean_stock_seed_at ::
    "bool list \<Rightarrow> ZF"
where
  "pp_t_probe_modal_boolean_stock_seed_at w =
    pp_t_cone_lift w pp_t_probe_modal_boolean_stock_root_seed"

lemma pp_t_probe_modal_boolean_stock_seed_at_in_domain:
  "Elem (pp_t_probe_modal_boolean_stock_seed_at w)
    (pp_t_domain Prop)"
  unfolding pp_t_probe_modal_boolean_stock_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem pp_t_probe_modal_boolean_stock_seed_recombines_at_every_world:
  "pp_t_unary_recombines_at
    pp_t_probe_modal_boolean_stock
    (pp_t_probe_modal_boolean_stock_seed_at w) w"
  unfolding pp_t_probe_modal_boolean_stock_seed_at_def
  by (rule
    pp_t_unary_stock_root_recombination_transports_to_cone[
      OF
        pp_t_probe_modal_boolean_stock_root_seed_spec[THEN conjunct1]
        pp_t_probe_modal_boolean_stock_root_seed_spec[THEN conjunct2]
        pp_t_probe_modal_boolean_stock_cone_iff])

end
