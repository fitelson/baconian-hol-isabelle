theory Bacon_PP_ZF_Tree_Boundary_Operator_Probe
  imports
    Higher_Order_Metaphysics_PP_ZF_Modal_Boundary_Stock.Bacon_PP_ZF_Tree_Modal_Boundary_Stock
begin

section \<open>A logical definition of the boundary condition\<close>

definition pp_t_fundamental_boundary_builder :: oterm
where
  "pp_t_fundamental_boundary_builder =
    Lam Prop
      (Lam Prop
        (Conj
          (Neg (Eq Prop (Var 0) (Var 1)))
          (\<diamond>\<^sub>o (Eq Prop (Var 0) (Var 1)))))"

lemma pp_t_fundamental_boundary_builder_typed:
  "[] \<turnstile> pp_t_fundamental_boundary_builder :
    Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound)
    (simp add: pp_t_fundamental_boundary_builder_def
      ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)

lemma pp_t_fundamental_boundary_builder_logical:
  "pp_logical_vocabulary pp_t_fundamental_boundary_builder"
  by (simp add: pp_t_fundamental_boundary_builder_def
      pp_logical_vocabulary_def
      ObjDiamond_def ObjBox_def ObjTrue_def)

lemma pp_t_fundamental_boundary_builder_in_domain:
  "Elem (pp_t_closed_den pp_t_fundamental_boundary_builder)
    (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop))"
  by (rule pp_t_closed_den_in_domain)
    (rule pp_t_fundamental_boundary_builder_typed)

theorem pp_t_fundamental_boundary_builder_apply_holds:
  assumes R: "Elem R (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_closed_den pp_t_fundamental_boundary_builder \<acute> R)
        \<acute> p) w
      \<longleftrightarrow>
    pp_t_fundamental_boundary R w p"
proof -
  have beta:
      "((pp_t_closed_den pp_t_fundamental_boundary_builder \<acute> R)
          \<acute> p)
        =
      pp_t_eval pp_t_default_constants
        (extend_env p (extend_env R pp_t_closed_env))
        (Conj
          (Neg (Eq Prop (Var 0) (Var 1)))
          (\<diamond>\<^sub>o (Eq Prop (Var 0) (Var 1))))"
    unfolding pp_t_closed_den_def
      pp_t_fundamental_boundary_builder_def
    using R p by (simp add: Lambda_app)
  show ?thesis
    unfolding beta pp_t_fundamental_boundary_def
    using p
    by (simp add: pp_t_eval_ObjDiamond_holds; blast)
qed

definition pp_t_fundamental_boundary_precomposition_builder :: oterm
where
  "pp_t_fundamental_boundary_precomposition_builder =
    Lam Prop
      (Lam pp_t_one_context_unary_type
        (Lam Prop
          (App
            (App
              (shift (shift (shift
                pp_t_fundamental_boundary_builder)))
              (Var 2))
            (App (Var 1) (Var 0)))))"

lemma pp_t_fundamental_boundary_precomposition_builder_typed:
  "[] \<turnstile> pp_t_fundamental_boundary_precomposition_builder :
    Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (rule infer_type_sound)
    (simp add:
      pp_t_fundamental_boundary_precomposition_builder_def
      pp_t_fundamental_boundary_builder_def
      ObjDiamond_def ObjBox_def ObjTrue_def lookup_def shift_def)

lemma pp_t_fundamental_boundary_precomposition_builder_logical:
  "pp_logical_vocabulary
    pp_t_fundamental_boundary_precomposition_builder"
  by (simp add:
      pp_t_fundamental_boundary_precomposition_builder_def
      pp_t_fundamental_boundary_builder_def
      pp_logical_vocabulary_def
      ObjDiamond_def ObjBox_def ObjTrue_def shift_def)

lemma pp_t_fundamental_boundary_precomposition_apply:
  assumes R: "Elem R (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(((pp_t_closed_den
        pp_t_fundamental_boundary_precomposition_builder \<acute> R)
      \<acute> F) \<acute> p)
      =
    (pp_t_closed_den pp_t_fundamental_boundary_builder \<acute> R)
      \<acute> (F \<acute> p)"
  unfolding
    pp_t_fundamental_boundary_precomposition_builder_def
    pp_t_closed_den_def
  using R F p
  by (simp add: Lambda_app pp_t_eval_shift)

theorem pp_t_fundamental_boundary_precomposition_apply_holds:
  assumes R: "Elem R (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((((pp_t_closed_den
          pp_t_fundamental_boundary_precomposition_builder \<acute> R)
        \<acute> F) \<acute> p)) w
      \<longleftrightarrow>
    pp_t_fundamental_boundary R w (F \<acute> p)"
  unfolding
    pp_t_fundamental_boundary_precomposition_apply[OF R F p]
  by (rule pp_t_fundamental_boundary_builder_apply_holds[
    OF R pp_t_app_closed[OF F p]])

section \<open>The operator-indexed probe over the moving boundary\<close>

definition pp_t_moving_boundary_operator_probe ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> ZF"
where
  "pp_t_moving_boundary_operator_probe R =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_moving_boundary_singleton_stock R)
      pp_t_operator_indexed_singleton_family_builder"

lemma pp_t_moving_boundary_operator_probe_in_domain:
  "Elem (pp_t_moving_boundary_operator_probe R)
    (pp_t_domain
      (pp_t_one_context_unary_type
        \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_moving_boundary_operator_probe_def
  by (rule pp_t_indexed_family_probe_for_stock_in_domain[
    OF pp_t_operator_indexed_singleton_terms_typed(1)
      pp_t_moving_boundary_singleton_stock_admissible])

theorem pp_t_moving_boundary_operator_probe_apply_holds:
  assumes R: "Elem (R w) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_moving_boundary_operator_probe R \<acute> F) \<acute> p) w
      \<longleftrightarrow>
    pp_t_fundamental_boundary (R w) w (F \<acute> p)"
proof -
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have probe:
      "pp_t_holds
        ((pp_t_moving_boundary_operator_probe R \<acute> F) \<acute> p) w
        \<longleftrightarrow>
      pp_t_moving_boundary_singleton_stock R w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    unfolding pp_t_moving_boundary_operator_probe_def
    by (rule pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_moving_boundary_singleton_stock_admissible F p])
  have family:
      "((pp_t_closed_den
          pp_t_operator_indexed_singleton_family_builder \<acute> F) \<acute> p)
        =
      pp_t_singleton_family_at (F \<acute> p)"
    by (rule pp_t_operator_indexed_singleton_family_value[OF F p])
  have boundary:
      "pp_t_moving_boundary_singleton_stock R w
          (pp_t_singleton_family_at (F \<acute> p))
        \<longleftrightarrow>
      pp_t_fundamental_boundary (R w) w (F \<acute> p)"
    unfolding pp_t_moving_boundary_singleton_stock_def
    by (rule pp_t_singleton_family_in_boundary_stock_iff[
      OF R Fp])
  show ?thesis
    using probe boundary
    unfolding family by blast
qed

definition pp_t_fundamental_family_coherent_from ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_fundamental_family_coherent_from R w
    \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> pp_t_eqv Prop v (R v) (R w))"

lemma pp_t_coherent_boundary_probe_pointwise:
  assumes R_domain: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and coherent: "pp_t_fundamental_family_coherent_from R w"
    and wv: "prefix w v"
    and p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_eqv Prop v p q"
    and vu: "prefix v u"
  shows
    "pp_t_holds
        ((pp_t_moving_boundary_operator_probe R \<acute> F) \<acute> p) u
      =
     pp_t_holds
        (((pp_t_closed_den
            pp_t_fundamental_boundary_precomposition_builder \<acute> R w)
          \<acute> F) \<acute> q) u"
proof -
  have Fp_Fq_v: "pp_t_eqv Prop v (F \<acute> p) (F \<acute> q)"
    by (rule pp_t_arrow_member_respects[OF F p q pq])
  have wu: "prefix w u"
    by (rule prefix_order.trans[OF wv vu])
  have Ru_Rw:
      "pp_t_eqv Prop u (R u) (R w)"
    using coherent wu
    unfolding pp_t_fundamental_family_coherent_from_def
    by blast
  have Fp_Fq_u: "pp_t_eqv Prop u (F \<acute> p) (F \<acute> q)"
    by (rule pp_t_eqv_persistent[OF Fp_Fq_v vu])
  have boundary_function:
      "Elem (pp_t_closed_den
          pp_t_fundamental_boundary_builder)
        (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_fundamental_boundary_builder_in_domain)
  have first_arguments:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) u
        (pp_t_closed_den
          pp_t_fundamental_boundary_builder \<acute> R u)
        (pp_t_closed_den
          pp_t_fundamental_boundary_builder \<acute> R w)"
    by (rule pp_t_arrow_member_respects[
      OF boundary_function R_domain R_domain Ru_Rw])
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have Fq: "Elem (F \<acute> q) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F q])
  have boundary_outputs:
      "pp_t_eqv Prop u
        ((pp_t_closed_den
            pp_t_fundamental_boundary_builder \<acute> R u)
          \<acute> (F \<acute> p))
        ((pp_t_closed_den
            pp_t_fundamental_boundary_builder \<acute> R w)
          \<acute> (F \<acute> q))"
    by (rule pp_t_app_respects[
      OF first_arguments Fp Fq Fp_Fq_u])
  have output_truth:
      "pp_t_holds
          ((pp_t_closed_den
              pp_t_fundamental_boundary_builder \<acute> R u)
            \<acute> (F \<acute> p)) u
        \<longleftrightarrow>
       pp_t_holds
          ((pp_t_closed_den
              pp_t_fundamental_boundary_builder \<acute> R w)
            \<acute> (F \<acute> q)) u"
    by (rule pp_t_prop_eqv_at[OF boundary_outputs], simp)
  have boundary_iff:
      "pp_t_fundamental_boundary (R u) u (F \<acute> p)
        \<longleftrightarrow>
       pp_t_fundamental_boundary (R w) u (F \<acute> q)"
    using output_truth
      pp_t_fundamental_boundary_builder_apply_holds[
        OF R_domain[of u] Fp, of u]
      pp_t_fundamental_boundary_builder_apply_holds[
        OF R_domain[of w] Fq, of u]
    by blast
  have left_truth:
      "pp_t_holds
          ((pp_t_moving_boundary_operator_probe R \<acute> F) \<acute> p) u
        \<longleftrightarrow>
       pp_t_fundamental_boundary (R u) u (F \<acute> p)"
    by (rule pp_t_moving_boundary_operator_probe_apply_holds[
      OF R_domain F p])
  have right_truth:
      "pp_t_holds
          (((pp_t_closed_den
              pp_t_fundamental_boundary_precomposition_builder \<acute> R w)
            \<acute> F) \<acute> q) u
        \<longleftrightarrow>
       pp_t_fundamental_boundary (R w) u (F \<acute> q)"
    by (rule
      pp_t_fundamental_boundary_precomposition_apply_holds[
        OF R_domain F q])
  show ?thesis
    using left_truth boundary_iff right_truth by blast
qed

theorem pp_t_coherent_boundary_probe_is_logically_precomposed:
  assumes R_domain: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and coherent: "pp_t_fundamental_family_coherent_from R w"
  shows
    "pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_moving_boundary_operator_probe R \<acute> F)
      ((pp_t_closed_den
          pp_t_fundamental_boundary_precomposition_builder \<acute> R w)
        \<acute> F)"
  unfolding pp_t_eqv.simps
proof (intro allI impI allI allI impI impI impI allI impI)
  fix v p q u
  assume wv: "prefix w v"
    and p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq_unfolded:
      "\<forall>z. prefix v z \<longrightarrow>
        pp_t_holds p z = pp_t_holds q z"
    and vu: "prefix v u"
  have pq: "pp_t_eqv Prop v p q"
    using pq_unfolded by simp
  show "pp_t_holds
      ((pp_t_moving_boundary_operator_probe R \<acute> F) \<acute> p) u =
    pp_t_holds
      (((pp_t_closed_den
          pp_t_fundamental_boundary_precomposition_builder \<acute> R w)
        \<acute> F) \<acute> q) u"
    by (rule pp_t_coherent_boundary_probe_pointwise[
      OF R_domain F coherent wv p q pq vu])
qed

section \<open>Why transported Recombination seeds are not coherent\<close>

theorem pp_t_cone_lift_family_coherent_from_root_imp_settled:
  assumes R: "Elem R (pp_t_domain Prop)"
    and coherent:
      "pp_t_fundamental_family_coherent_from
        (\<lambda>w. pp_t_cone_lift w R) []"
  shows
    "pp_t_eqv Prop [] R (pp_zf_truth True)
      \<or> pp_t_eqv Prop [] R (pp_zf_truth False)"
proof -
  have fixed_truth_value:
      "\<And>v. pp_t_holds R v = pp_t_holds R []"
  proof -
    fix v :: "bool list"
    have root_v: "prefix [] v"
      by simp
    have lifts:
        "pp_t_eqv Prop v
          (pp_t_cone_lift v R)
          (pp_t_cone_lift [] R)"
      using coherent root_v
      unfolding pp_t_fundamental_family_coherent_from_def
      by blast
    have at_v:
        "pp_t_holds (pp_t_cone_lift v R) v
          =
         pp_t_holds (pp_t_cone_lift [] R) v"
      using pp_t_prop_eqv_at[OF lifts, of v] by simp
    show "pp_t_holds R v = pp_t_holds R []"
      using at_v
      by (simp add: pp_t_cone_lift_holds)
  qed
  show ?thesis
  proof (cases "pp_t_holds R []")
    case True
    have "pp_t_eqv Prop [] R (pp_zf_truth True)"
      unfolding pp_t_eqv.simps
      using fixed_truth_value True by simp
    then show ?thesis by blast
  next
    case False
    have "pp_t_eqv Prop [] R (pp_zf_truth False)"
      unfolding pp_t_eqv.simps
      using fixed_truth_value False by simp
    then show ?thesis by blast
  qed
qed

lemma pp_t_closed_logical_unary_in_modal_boolean_stock:
  assumes typed:
      "[] \<turnstile> M : pp_t_one_context_unary_type"
    and logical: "pp_logical_vocabulary M"
  shows "pp_t_probe_modal_boolean_stock w (pp_t_closed_den M)"
proof -
  let ?E =
    "PPProbeModalBooleanOld
      (PPProbeSuccessorOld (PPProbeBooleanLogical M))"
  have valid: "pp_t_probe_modal_boolean_expr_valid ?E"
    using typed logical by simp
  have representative:
      "pp_t_closed_den M
        \<in> pp_t_probe_modal_boolean_representatives"
  proof -
    have "?E \<in> {E. pp_t_probe_modal_boolean_expr_valid E}"
      using valid by simp
    then have
      "pp_t_probe_modal_boolean_expr_den ?E
        \<in> pp_t_probe_modal_boolean_expr_den `
          {E. pp_t_probe_modal_boolean_expr_valid E}"
      by blast
    then show ?thesis
      unfolding pp_t_probe_modal_boolean_representatives_def
      by simp
  qed
  have domain:
      "Elem (pp_t_closed_den M)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain[OF typed])
  have reflexive:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_closed_den M) (pp_t_closed_den M)"
    by (rule pp_t_eqv_reflexive[OF domain])
  show ?thesis
    unfolding pp_t_probe_modal_boolean_stock_def
    using domain representative reflexive by blast
qed

lemma pp_t_modal_boolean_stock_contains_identity:
  "pp_t_probe_modal_boolean_stock w (pp_t_closed_den prop_id)"
  by (rule pp_t_closed_logical_unary_in_modal_boolean_stock)
    (rule typed_prop_id, simp add: prop_id_def
      pp_logical_vocabulary_def)

lemma pp_t_closed_negation_typed:
  "[] \<turnstile> pp_negation_operator : pp_t_one_context_unary_type"
  by (rule infer_type_sound)
    (simp add: pp_negation_operator_def pp_unary_ty_def lookup_def)

lemma pp_t_modal_boolean_stock_contains_negation:
  "pp_t_probe_modal_boolean_stock w
    (pp_t_closed_den pp_negation_operator)"
  by (rule pp_t_closed_logical_unary_in_modal_boolean_stock)
    (rule pp_t_closed_negation_typed,
     simp add: pp_negation_operator_def
      pp_logical_vocabulary_def)

lemma pp_t_closed_identity_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_closed_den prop_id \<acute> p = p"
  unfolding pp_t_closed_den_def prop_id_def
  using p by (simp add: Lambda_app)

lemma pp_t_closed_negation_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      (pp_t_closed_den pp_negation_operator \<acute> p) w
      \<longleftrightarrow>
    \<not> pp_t_holds p w"
  unfolding pp_t_closed_den_def pp_negation_operator_def
  using p by (simp add: Lambda_app)

lemma pp_t_identity_negation_recombination_seed_unsettled:
  assumes r: "Elem r (pp_t_domain Prop)"
    and recombines: "pp_t_unary_recombines_at Pure r w"
    and identity_pure: "Pure w (pp_t_closed_den prop_id)"
    and negation_pure:
      "Pure w (pp_t_closed_den pp_negation_operator)"
  shows
    "\<not> pp_t_eqv Prop w r (pp_zf_truth True)
      \<and> \<not> pp_t_eqv Prop w r (pp_zf_truth False)"
proof (intro conjI)
  show "\<not> pp_t_eqv Prop w r (pp_zf_truth True)"
  proof
    assume r_true:
        "pp_t_eqv Prop w r (pp_zf_truth True)"
    have necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (pp_t_closed_den prop_id \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have r_at_v: "pp_t_holds r v"
        using r_true pp_t_prop_eqv_truth_iff wv by blast
      show "pp_t_holds (pp_t_closed_den prop_id \<acute> r) v"
        unfolding pp_t_closed_identity_apply[OF r]
        by (rule r_at_v)
    qed
    have identity_domain:
        "Elem (pp_t_closed_den prop_id)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule typed_prop_id)
    have universal:
        "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds (pp_t_closed_den prop_id \<acute> q) w"
      using recombines identity_domain
        identity_pure necessary
      unfolding pp_t_unary_recombines_at_def
      by blast
    have false_true:
        "pp_t_holds
          (pp_t_closed_den prop_id \<acute> pp_zf_truth False) w"
      using universal pp_t_truth_in_domain by blast
    show False
      using false_true
      unfolding pp_t_closed_identity_apply[
        OF pp_t_truth_in_domain[of False]]
      by simp
  qed
  show "\<not> pp_t_eqv Prop w r (pp_zf_truth False)"
  proof
    assume r_false:
        "pp_t_eqv Prop w r (pp_zf_truth False)"
    have necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds
            (pp_t_closed_den pp_negation_operator \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have not_r_at_v: "\<not> pp_t_holds r v"
        using r_false wv by simp
      show "pp_t_holds
          (pp_t_closed_den pp_negation_operator \<acute> r) v"
        using pp_t_closed_negation_holds[OF r, of v]
          not_r_at_v by simp
    qed
    have negation_domain:
        "Elem (pp_t_closed_den pp_negation_operator)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_closed_den_in_domain)
        (rule pp_t_closed_negation_typed)
    have universal:
        "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          pp_t_holds
            (pp_t_closed_den pp_negation_operator \<acute> q) w"
      using recombines negation_domain
        negation_pure necessary
      unfolding pp_t_unary_recombines_at_def
      by blast
    have negation_truth:
        "pp_t_holds
          (pp_t_closed_den pp_negation_operator
            \<acute> pp_zf_truth True) w"
      using universal pp_t_truth_in_domain by blast
    show False
      using negation_truth
        pp_t_closed_negation_holds[
          OF pp_t_truth_in_domain[of True], of w]
      by simp
  qed
qed

lemma pp_t_modal_boolean_root_seed_unsettled:
  "\<not> pp_t_eqv Prop []
      pp_t_probe_modal_boolean_stock_root_seed (pp_zf_truth True)
    \<and>
   \<not> pp_t_eqv Prop []
      pp_t_probe_modal_boolean_stock_root_seed (pp_zf_truth False)"
  by (rule pp_t_identity_negation_recombination_seed_unsettled[
    OF
      pp_t_probe_modal_boolean_stock_root_seed_spec[THEN conjunct1]
      pp_t_probe_modal_boolean_stock_root_seed_spec[THEN conjunct2]
      pp_t_modal_boolean_stock_contains_identity
      pp_t_modal_boolean_stock_contains_negation])

theorem pp_t_modal_boolean_transported_seed_not_coherent:
  "\<not> pp_t_fundamental_family_coherent_from
    pp_t_probe_modal_boolean_stock_seed_at []"
proof
  assume coherent:
      "pp_t_fundamental_family_coherent_from
        pp_t_probe_modal_boolean_stock_seed_at []"
  have cone_coherent:
      "pp_t_fundamental_family_coherent_from
        (\<lambda>w.
          pp_t_cone_lift w
            pp_t_probe_modal_boolean_stock_root_seed) []"
    using coherent
    unfolding pp_t_probe_modal_boolean_stock_seed_at_def
    by simp
  have settled:
      "pp_t_eqv Prop []
          pp_t_probe_modal_boolean_stock_root_seed (pp_zf_truth True)
        \<or>
       pp_t_eqv Prop []
          pp_t_probe_modal_boolean_stock_root_seed (pp_zf_truth False)"
    by (rule
      pp_t_cone_lift_family_coherent_from_root_imp_settled[
        OF
          pp_t_probe_modal_boolean_stock_root_seed_spec[THEN conjunct1]
          cone_coherent])
  show False
    using pp_t_modal_boolean_root_seed_unsettled settled by blast
qed

section \<open>The exact residual probe over the combined stock\<close>

definition pp_t_modal_boundary_operator_probe :: ZF
where
  "pp_t_modal_boundary_operator_probe =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      pp_t_modal_boundary_stock
      pp_t_operator_indexed_singleton_family_builder"

lemma pp_t_modal_boundary_operator_probe_in_domain:
  "Elem pp_t_modal_boundary_operator_probe
    (pp_t_domain
      (pp_t_one_context_unary_type
        \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_modal_boundary_operator_probe_def
  by (rule pp_t_indexed_family_probe_for_stock_in_domain[
    OF pp_t_operator_indexed_singleton_terms_typed(1)
      pp_t_modal_boundary_stock_admissible])

theorem pp_t_modal_boundary_operator_probe_apply_holds:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_modal_boundary_operator_probe \<acute> F) \<acute> p) w
      \<longleftrightarrow>
    (pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))
      \<or>
     pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_stock_seed_at w) w (F \<acute> p))"
proof -
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have probe:
      "pp_t_holds
        ((pp_t_modal_boundary_operator_probe \<acute> F) \<acute> p) w
        \<longleftrightarrow>
      pp_t_modal_boundary_stock w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    unfolding pp_t_modal_boundary_operator_probe_def
    by (rule pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_modal_boundary_stock_admissible F p])
  have family:
      "((pp_t_closed_den
          pp_t_operator_indexed_singleton_family_builder \<acute> F) \<acute> p)
        =
      pp_t_singleton_family_at (F \<acute> p)"
    by (rule pp_t_operator_indexed_singleton_family_value[OF F p])
  have boundary:
      "pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_stock_seed_at w
          (pp_t_singleton_family_at (F \<acute> p))
        \<longleftrightarrow>
      pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_stock_seed_at w) w (F \<acute> p)"
    unfolding pp_t_moving_boundary_singleton_stock_def
    by (rule pp_t_singleton_family_in_boundary_stock_iff[
      OF pp_t_probe_modal_boolean_stock_seed_at_in_domain Fp])
  show ?thesis
    using probe boundary
    unfolding family pp_t_modal_boundary_stock_def
    by blast
qed

end
