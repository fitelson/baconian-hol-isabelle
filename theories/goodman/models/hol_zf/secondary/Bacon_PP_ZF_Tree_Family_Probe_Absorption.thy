theory Bacon_PP_ZF_Tree_Family_Probe_Absorption
  imports Bacon_PP_ZF_Tree_One_Classifier_Contexts
begin

section \<open>One-step absorption for diagonally reflexive families\<close>

definition pp_t_family_probe_for_stock ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> ZF"
where
  "pp_t_family_probe_for_stock S B =
    pp_t_closed_den (pp_t_family_probe_builder B)
      \<acute> pp_t_classifier pp_t_one_context_unary_type S"

lemma pp_t_family_probe_for_stock_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows "Elem (pp_t_family_probe_for_stock S B)
    (pp_t_domain pp_t_one_context_unary_type)"
proof -
  have classifier:
      "Elem (pp_t_classifier pp_t_one_context_unary_type S)
        (pp_t_domain pp_t_one_context_classifier_type)"
    using pp_t_classifier_in_domain[OF S_admissible] .
  show ?thesis
    unfolding pp_t_family_probe_for_stock_def
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[
        OF pp_t_family_probe_builder_typed[OF B_typed]]
        classifier] .
qed

lemma pp_t_family_probe_for_stock_apply:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_family_probe_for_stock S B \<acute> p =
    pp_t_classifier pp_t_one_context_unary_type S
      \<acute> (pp_t_closed_den B \<acute> p)"
  unfolding pp_t_family_probe_for_stock_def
    pp_t_family_probe_builder_def pp_t_closed_den_def
  using p pp_t_classifier_in_domain[OF S_admissible]
    pp_t_closed_den_in_domain[OF B_typed]
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_family_probe_for_stock_apply_holds:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_family_probe_for_stock S B \<acute> p) w
    \<longleftrightarrow> S w (pp_t_closed_den B \<acute> p)"
proof -
  have B_den:
      "Elem (pp_t_closed_den B)
        (pp_t_domain
          (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[OF B_typed] .
  have Bp:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_app_closed[OF B_den p] .
  show ?thesis
    unfolding pp_t_family_probe_for_stock_apply[
      OF B_typed S_admissible p]
    using pp_t_classifier_holds[OF Bp, of S w] .
qed

definition pp_t_family_probe_stock_enlargement ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      oterm \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_family_probe_stock_enlargement S B w X \<longleftrightarrow>
    S w X
    \<or> pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_family_probe_for_stock S B) X"

lemma pp_t_eqv_class_predicate_admissible:
  assumes z: "Elem z (pp_t_domain \<sigma>)"
  shows "pp_t_predicate_admissible \<sigma>
    (\<lambda>w X. pp_t_eqv \<sigma> w z X)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain \<sigma>)"
    and Y: "Elem Y (pp_t_domain \<sigma>)"
    and XY: "pp_t_eqv \<sigma> w X Y"
    and wv: "prefix w v"
  have XY_v: "pp_t_eqv \<sigma> v X Y"
    using pp_t_eqv_persistent[OF XY wv] .
  have refl: "pp_t_eqv \<sigma> v z z"
    using pp_t_eqv_reflexive[OF z] .
  show "pp_t_eqv \<sigma> v z X = pp_t_eqv \<sigma> v z Y"
    using pp_t_eqv_congruence[
      OF z z X Y refl XY_v] .
qed

lemma pp_t_family_probe_stock_enlargement_admissible:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows "pp_t_predicate_admissible
    pp_t_one_context_unary_type
    (pp_t_family_probe_stock_enlargement S B)"
proof -
  have probe:
      "Elem (pp_t_family_probe_for_stock S B)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed S_admissible] .
  have added:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type
        (\<lambda>w X. pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S B) X)"
    by (rule pp_t_eqv_class_predicate_admissible[OF probe])
  show ?thesis
    using S_admissible added
    unfolding pp_t_predicate_admissible_def
      pp_t_family_probe_stock_enlargement_def
    by blast
qed

lemma pp_t_family_probe_collision_absorbed:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and diagonal:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds ((pp_t_closed_den B \<acute> p) \<acute> p) w"
    and p: "Elem p (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S B)
        (pp_t_closed_den B \<acute> p)"
  shows "S w (pp_t_closed_den B \<acute> p)"
proof -
  have probe:
      "Elem (pp_t_family_probe_for_stock S B)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed S_admissible] .
  have Bp:
      "Elem (pp_t_closed_den B \<acute> p)
        (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_app_closed[
      OF pp_t_closed_den_in_domain[OF B_typed] p] .
  have pp: "pp_t_eqv Prop w p p"
    using pp_t_eqv_reflexive[OF p] .
  have applications:
      "pp_t_eqv Prop w
        (pp_t_family_probe_for_stock S B \<acute> p)
        ((pp_t_closed_den B \<acute> p) \<acute> p)"
    using collision p pp by auto
  have probe_true:
      "pp_t_holds
        (pp_t_family_probe_for_stock S B \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      diagonal[OF p, of w]
    by simp
  show ?thesis
    using pp_t_family_probe_for_stock_apply_holds[
      OF B_typed S_admissible p, of w]
      probe_true by blast
qed

theorem pp_t_diagonally_reflexive_family_probe_stabilizes:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and diagonal:
      "\<And>p w. Elem p (pp_t_domain Prop) \<Longrightarrow>
        pp_t_holds ((pp_t_closed_den B \<acute> p) \<acute> p) w"
  shows "pp_t_family_probe_for_stock
      (pp_t_family_probe_stock_enlargement S B) B
    = pp_t_family_probe_for_stock S B"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed
        pp_t_family_probe_stock_enlargement_admissible[
          OF B_typed S_admissible]] .
  show "Elem (pp_t_family_probe_for_stock S B)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_family_probe_for_stock_in_domain[
      OF B_typed S_admissible] .
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B \<acute> p
      = pp_t_family_probe_for_stock S B \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement S B) B \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF B_typed
            pp_t_family_probe_stock_enlargement_admissible[
              OF B_typed S_admissible]]
          p] .
    show "Elem (pp_t_family_probe_for_stock S B \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF B_typed S_admissible] p] .
    fix w
    have enlarged:
        "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_family_probe_stock_enlargement S B) B
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_family_probe_stock_enlargement S B w
          (pp_t_closed_den B \<acute> p)"
      using pp_t_family_probe_for_stock_apply_holds[
        OF B_typed
          pp_t_family_probe_stock_enlargement_admissible[
            OF B_typed S_admissible]
          p,
        of w] .
    have old:
        "pp_t_holds (pp_t_family_probe_for_stock S B \<acute> p) w
        \<longleftrightarrow> S w (pp_t_closed_den B \<acute> p)"
      using pp_t_family_probe_for_stock_apply_holds[
        OF B_typed S_admissible p, of w] .
    show "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_family_probe_stock_enlargement S B) B
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds (pp_t_family_probe_for_stock S B \<acute> p) w"
      using enlarged old
        pp_t_family_probe_collision_absorbed[
          OF B_typed S_admissible diagonal p, of w]
      unfolding pp_t_family_probe_stock_enlargement_def
      by blast
  qed
qed

theorem pp_t_family_probe_stabilizes_iff_collisions_absorbed:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows
    "pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B
      = pp_t_family_probe_for_stock S B
    \<longleftrightarrow>
    (\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S B)
        (pp_t_closed_den B \<acute> p)
      \<longrightarrow>
      S w (pp_t_closed_den B \<acute> p))"
proof
  assume stable:
      "pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement S B) B
        = pp_t_family_probe_for_stock S B"
  show "\<forall>p w.
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_family_probe_for_stock S B)
        (pp_t_closed_den B \<acute> p)
      \<longrightarrow>
      S w (pp_t_closed_den B \<acute> p)"
  proof (intro allI impI)
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S B)
          (pp_t_closed_den B \<acute> p)"
    have enlarged_member:
        "pp_t_family_probe_stock_enlargement S B w
          (pp_t_closed_den B \<acute> p)"
      unfolding pp_t_family_probe_stock_enlargement_def
      using collision by blast
    have reevaluated_true:
        "pp_t_holds
          (pp_t_family_probe_for_stock
            (pp_t_family_probe_stock_enlargement S B) B
            \<acute> p) w"
      using pp_t_family_probe_for_stock_apply_holds[
        OF B_typed
          pp_t_family_probe_stock_enlargement_admissible[
            OF B_typed S_admissible]
          p,
        of w]
        enlarged_member by blast
    have old_true:
        "pp_t_holds (pp_t_family_probe_for_stock S B \<acute> p) w"
      using reevaluated_true unfolding stable .
    show "S w (pp_t_closed_den B \<acute> p)"
      using pp_t_family_probe_for_stock_apply_holds[
        OF B_typed S_admissible p, of w]
        old_true by blast
  qed
next
  assume absorbed:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S B)
          (pp_t_closed_den B \<acute> p)
        \<longrightarrow>
        S w (pp_t_closed_den B \<acute> p)"
  show "pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B
      = pp_t_family_probe_for_stock S B"
  proof (rule pp_t_unary_function_ext)
    show "Elem
        (pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement S B) B)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_family_probe_for_stock_in_domain[
        OF B_typed
          pp_t_family_probe_stock_enlargement_admissible[
            OF B_typed S_admissible]] .
    show "Elem (pp_t_family_probe_for_stock S B)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_family_probe_for_stock_in_domain[
        OF B_typed S_admissible] .
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "pp_t_family_probe_for_stock
          (pp_t_family_probe_stock_enlargement S B) B \<acute> p
        = pp_t_family_probe_for_stock S B \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          (pp_t_family_probe_for_stock
            (pp_t_family_probe_stock_enlargement S B) B \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_family_probe_for_stock_in_domain[
            OF B_typed
              pp_t_family_probe_stock_enlargement_admissible[
                OF B_typed S_admissible]]
            p] .
      show "Elem (pp_t_family_probe_for_stock S B \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_family_probe_for_stock_in_domain[
            OF B_typed S_admissible] p] .
      fix w
      have enlarged:
          "pp_t_holds
            (pp_t_family_probe_for_stock
              (pp_t_family_probe_stock_enlargement S B) B
              \<acute> p) w
          \<longleftrightarrow>
          pp_t_family_probe_stock_enlargement S B w
            (pp_t_closed_den B \<acute> p)"
        using pp_t_family_probe_for_stock_apply_holds[
          OF B_typed
            pp_t_family_probe_stock_enlargement_admissible[
              OF B_typed S_admissible]
            p,
          of w] .
      have old:
          "pp_t_holds
            (pp_t_family_probe_for_stock S B \<acute> p) w
          \<longleftrightarrow> S w (pp_t_closed_den B \<acute> p)"
        using pp_t_family_probe_for_stock_apply_holds[
          OF B_typed S_admissible p, of w] .
      show "pp_t_holds
            (pp_t_family_probe_for_stock
              (pp_t_family_probe_stock_enlargement S B) B
              \<acute> p) w
          \<longleftrightarrow>
          pp_t_holds (pp_t_family_probe_for_stock S B \<acute> p) w"
        using enlarged old absorbed[rule_format, OF p, of w]
        unfolding pp_t_family_probe_stock_enlargement_def
        by blast
    qed
  qed
qed

section \<open>Countably represented unary stocks\<close>

theorem pp_t_countably_represented_unary_stock_root_seed_exists:
  assumes countable: "countable D"
    and D_domain:
      "\<And>d. d \<in> D \<Longrightarrow>
        Elem d (pp_t_domain pp_t_one_context_unary_type)"
    and D_equivariant:
      "\<And>d. d \<in> D \<Longrightarrow>
        pp_b_equivariant (pp_b_operator_of d)"
    and represented:
      "\<And>X. Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S [] X
        \<Longrightarrow> \<exists>d \<in> D.
          pp_t_eqv pp_t_one_context_unary_type [] X d"
  shows "\<exists>r. Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at S r []"
proof -
  let ?T = "pp_b_operator_of ` D"
  have T_countable: "countable ?T"
    using countable by (rule countable_image)
  have T_equivariant:
      "\<And>F. F \<in> ?T \<Longrightarrow> pp_b_equivariant F"
    using D_equivariant by blast
  obtain R where generic:
      "\<forall>F \<in> ?T. pp_b_root_unary_recombination F R"
    using pp_b_generic_witness_for_countable_stock[
      OF T_countable T_equivariant] by blast
  let ?r = "pp_zf_of_b R"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have pointwise:
      "\<And>X q.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S [] X
        \<Longrightarrow> (\<forall>w. pp_t_holds (X \<acute> ?r) w)
        \<Longrightarrow> Elem q (pp_t_domain Prop)
        \<Longrightarrow> pp_t_holds (X \<acute> q) []"
  proof -
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_one_context_unary_type)"
      and X_stock: "S [] X"
      and necessary: "\<forall>w. pp_t_holds (X \<acute> ?r) w"
      and q: "Elem q (pp_t_domain Prop)"
    obtain d where d: "d \<in> D"
      and Xd:
        "pp_t_eqv pp_t_one_context_unary_type [] X d"
      using represented[OF X X_stock] by blast
    have d_domain:
        "Elem d (pp_t_domain pp_t_one_context_unary_type)"
      by (rule D_domain[OF d])
    have d_necessary: "\<forall>w. pp_t_holds (d \<acute> ?r) w"
    proof
      fix w
      have Xd_w:
          "pp_t_eqv pp_t_one_context_unary_type w X d"
        using pp_t_eqv_persistent[OF Xd, of w] by simp
      have rr: "pp_t_eqv Prop w ?r ?r"
        using pp_t_eqv_reflexive[OF r] .
      have applications:
          "pp_t_eqv Prop w (X \<acute> ?r) (d \<acute> ?r)"
        using Xd_w r rr by auto
      show "pp_t_holds (d \<acute> ?r) w"
        using pp_t_prop_eqv_at[OF applications, of w]
          necessary[rule_format, of w]
        by simp
    qed
    have d_operator: "pp_b_operator_of d \<in> ?T"
      using d by blast
    have d_universal:
        "\<forall>a. Elem a (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (d \<acute> a) []"
      using pp_b_recombination_transfers_to_zf[
        OF generic[rule_format, OF d_operator] d_necessary] .
    have Xd_q:
        "pp_t_eqv Prop [] (X \<acute> q) (d \<acute> q)"
      using Xd q pp_t_eqv_reflexive[OF q] by auto
    have transfer:
        "pp_t_holds (X \<acute> q) []
          \<longleftrightarrow> pp_t_holds (d \<acute> q) []"
      using pp_t_prop_eqv_at[OF Xd_q, of "[]"] by simp
    have dq: "pp_t_holds (d \<acute> q) []"
      using d_universal q by blast
    show "pp_t_holds (X \<acute> q) []"
      using transfer dq by blast
  qed
  have recombines:
      "pp_t_unary_recombines_at S ?r []"
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
  show ?thesis
    using r recombines by blast
qed

theorem pp_t_unary_stock_root_recombination_transports_to_cone:
  assumes r: "Elem r (pp_t_domain Prop)"
    and root: "pp_t_unary_recombines_at S r []"
    and cone_stock:
      "\<And>s u X Y.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_one_context_unary_type s X Y
        \<Longrightarrow>
        (S (s @ u) X \<longleftrightarrow> S u Y)"
  shows "pp_t_unary_recombines_at S (pp_t_cone_lift w r) w"
proof -
  have pointwise:
      "\<And>Y q.
        Elem Y (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S w Y
        \<Longrightarrow>
        (\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (Y \<acute> pp_t_cone_lift w r) v)
        \<Longrightarrow> Elem q (pp_t_domain Prop)
        \<Longrightarrow> pp_t_holds (Y \<acute> q) w"
  proof -
    fix Y q
    assume Y:
        "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
      and Y_stock: "S w Y"
      and necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (Y \<acute> pp_t_cone_lift w r) v"
      and q: "Elem q (pp_t_domain Prop)"
    let ?Z =
      "pp_t_cone_restrict pp_t_one_context_unary_type w Y"
    let ?p = "pp_t_cone_restrict Prop w q"
    have Z:
        "Elem ?Z (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_cone_restrict_in_domain[OF Y] .
    have p: "Elem ?p (pp_t_domain Prop)"
      using pp_t_cone_restrict_in_domain[OF q] .
    have YZ:
        "pp_t_cone_rel pp_t_one_context_unary_type w Y ?Z"
      using pp_t_cone_restrict_related[OF Y] .
    have lift_r:
        "pp_t_cone_rel Prop w (pp_t_cone_lift w r) r"
      using pp_t_cone_extend_related[OF r, of w] by simp
    have qp: "pp_t_cone_rel Prop w q ?p"
      using pp_t_cone_restrict_related[OF q] .
    have Z_stock: "S [] ?Z"
      using cone_stock[OF Y Z YZ, of "[]"]
        Y_stock by simp
    have Z_necessary: "\<forall>u. pp_t_holds (?Z \<acute> r) u"
    proof
      fix u
      have outputs:
          "pp_t_cone_rel Prop w
            (Y \<acute> pp_t_cone_lift w r) (?Z \<acute> r)"
        using YZ pp_t_cone_lift_in_domain r lift_r by auto
      have left:
          "pp_t_holds
            (Y \<acute> pp_t_cone_lift w r) (w @ u)"
        using necessary by simp
      show "pp_t_holds (?Z \<acute> r) u"
        using outputs left by auto
    qed
    have Z_universal:
        "\<forall>a. Elem a (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (?Z \<acute> a) []"
      using root Z Z_stock Z_necessary
      unfolding pp_t_unary_recombines_at_def by blast
    have Zp: "pp_t_holds (?Z \<acute> ?p) []"
      using Z_universal p by blast
    have outputs:
        "pp_t_cone_rel Prop w (Y \<acute> q) (?Z \<acute> ?p)"
      using YZ q p qp by auto
    have all_outputs:
        "\<forall>u. pp_t_holds (Y \<acute> q) (w @ u)
          \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) u"
      using outputs by simp
    have at_root:
        "pp_t_holds (Y \<acute> q) (w @ [])
          \<longleftrightarrow> pp_t_holds (?Z \<acute> ?p) []"
      using all_outputs[rule_format, of "[]"] .
    show "pp_t_holds (Y \<acute> q) w"
      using at_root Zp by simp
  qed
  show ?thesis
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
qed

end
