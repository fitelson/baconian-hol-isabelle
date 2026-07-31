theory Bacon_PP_ZF_Goodman_M1_Fn59
  imports
    Bacon_PP_ZF_Tree_CEV_Soundness
    "Higher_Order_Metaphysics_PP_Frontier.Bacon_PP_Goodman_M1_Complete"
begin

section \<open>Goodman M1 and Bacon's footnote 59 in the exact tree semantics\<close>

context pp_t_moving_internal_parameters
begin

lemma pp_t_M1_fn59_liar_denotation:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval (pp_t_moving_internal_constants Pure) \<rho>
        pp_M1_fn59_liar \<acute> p) w
    \<longleftrightarrow>
    (\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
      (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        (Pure pp_unary_ty w X
          \<and> pp_t_eqv Prop w q (pp_t_moving_seed w)
          \<and> pp_t_eqv Prop w p (X \<acute> q)
          \<longrightarrow> \<not> pp_t_holds (X \<acute> p) w)))"
proof -
  have beta:
      "pp_t_eval (pp_t_moving_internal_constants Pure) \<rho>
          pp_M1_fn59_liar \<acute> p
       =
       pp_t_eval (pp_t_moving_internal_constants Pure)
          (extend_env p \<rho>)
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (pp_fun Prop (Var 0))
                    (Eq Prop (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))"
    unfolding pp_M1_fn59_liar_def
    using p by (simp add: Lambda_app)
  show ?thesis
    unfolding beta pp_pure_def pp_fun_def
    apply (simp only: pp_t_eval_Forall_holds
      pp_t_eval_Imp_holds pp_t_eval_Conj_holds
      pp_t_eval_Neg_holds pp_t_eval_Eq_holds)
    by (simp del: pp_t_eqv.simps
      add: pp_t_classifier_holds extend_env.simps
        pp_t_three_extensions_index_two
        pp_t_moving_fundamental_at.simps pp_unary_ty_def)
qed

lemma pp_t_M1_fn59_QSS_denotation:
  "pp_t_holds
      (pp_t_eval (pp_t_moving_internal_constants Pure) \<rho> pp_QSS) w
    \<longleftrightarrow>
    (\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_t_domain pp_unary_ty) \<longrightarrow>
        (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
          (Pure pp_unary_ty w X
            \<and> Pure pp_unary_ty w Y
            \<and> pp_t_eqv Prop w q (pp_t_moving_seed w)
            \<longrightarrow>
            (pp_t_eqv Prop w (X \<acute> q) (Y \<acute> q)
              \<longrightarrow> pp_t_eqv pp_unary_ty w X Y)))))"
  unfolding pp_QSS_def pp_pure_def pp_fun_def
  apply (simp only: pp_t_eval_Forall_holds
    pp_t_eval_Imp_holds pp_t_eval_Conj_holds
    pp_t_eval_Eq_holds)
  by (simp del: pp_t_eqv.simps
    add: pp_t_classifier_holds extend_env.simps
      pp_t_three_extensions_index_two
      pp_t_moving_fundamental_at.simps pp_unary_ty_def)

theorem pp_t_M1_fn59_diagonal_contradiction:
  fixes \<rho> :: "nat \<Rightarrow> ZF"
  defines "D \<equiv>
    pp_t_eval (pp_t_moving_internal_constants Pure) \<rho>
      pp_M1_fn59_liar"
  assumes D_pure: "Pure pp_unary_ty w D"
    and qss_holds:
      "pp_t_holds
        (pp_t_eval (pp_t_moving_internal_constants Pure) \<rho> pp_QSS) w"
  shows False
proof -
  let ?r = "pp_t_moving_seed w"
  let ?d = "D \<acute> ?r"
  have D_dom: "Elem D (pp_t_domain pp_unary_ty)"
    unfolding D_def
    using MovingTreeConstants.pp_t_eval_type[
      OF typed_pp_M1_fn59_liar pp_t_empty_env_typed]
    by (simp add: pp_t_dom_def)
  have r_dom: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_moving_seed_in_domain)
  have d_dom: "Elem ?d (pp_t_domain Prop)"
    using D_dom r_dom unfolding pp_unary_ty_def
    by (rule pp_t_app_closed)
  have d_dom_unfolded:
      "Elem
        (pp_t_eval (pp_t_moving_internal_constants Pure) \<rho>
          pp_M1_fn59_liar \<acute> ?r)
        (pp_t_domain Prop)"
    using d_dom unfolding D_def .
  have diagonal:
      "pp_t_holds (D \<acute> ?d) w
        \<longleftrightarrow>
       (\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
         (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
           (Pure pp_unary_ty w X
             \<and> pp_t_eqv Prop w q ?r
             \<and> pp_t_eqv Prop w ?d (X \<acute> q)
             \<longrightarrow> \<not> pp_t_holds (X \<acute> ?d) w)))"
    unfolding D_def
    by (rule pp_t_M1_fn59_liar_denotation[OF d_dom_unfolded])
  have qss:
      "\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
        (\<forall>Y. Elem Y (pp_t_domain pp_unary_ty) \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> Pure pp_unary_ty w Y
              \<and> pp_t_eqv Prop w q ?r
              \<longrightarrow>
              (pp_t_eqv Prop w (X \<acute> q) (Y \<acute> q)
                \<longrightarrow> pp_t_eqv pp_unary_ty w X Y))))"
    using qss_holds pp_t_M1_fn59_QSS_denotation by blast
  have not_true:
      "pp_t_holds (D \<acute> ?d) w \<Longrightarrow>
        \<not> pp_t_holds (D \<acute> ?d) w"
  proof -
    assume true_Dd: "pp_t_holds (D \<acute> ?d) w"
    have rhs:
        "\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> pp_t_eqv Prop w q ?r
              \<and> pp_t_eqv Prop w ?d (X \<acute> q)
              \<longrightarrow> \<not> pp_t_holds (X \<acute> ?d) w))"
      using diagonal true_Dd by blast
    have rr: "pp_t_eqv Prop w ?r ?r"
      by (rule pp_t_eqv_reflexive[OF r_dom])
    have dd: "pp_t_eqv Prop w ?d (D \<acute> ?r)"
      by (rule pp_t_eqv_reflexive[OF d_dom])
    show "\<not> pp_t_holds (D \<acute> ?d) w"
      using rhs D_dom r_dom D_pure rr dd by blast
  qed
  have true_if_not:
      "\<not> pp_t_holds (D \<acute> ?d) w \<Longrightarrow>
        pp_t_holds (D \<acute> ?d) w"
  proof -
    assume false_Dd: "\<not> pp_t_holds (D \<acute> ?d) w"
    have rhs:
        "\<forall>X. Elem X (pp_t_domain pp_unary_ty) \<longrightarrow>
          (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            (Pure pp_unary_ty w X
              \<and> pp_t_eqv Prop w q ?r
              \<and> pp_t_eqv Prop w ?d (X \<acute> q)
              \<longrightarrow> \<not> pp_t_holds (X \<acute> ?d) w))"
    proof (intro allI impI)
      fix X q
      assume X_dom: "Elem X (pp_t_domain pp_unary_ty)"
        and q_dom: "Elem q (pp_t_domain Prop)"
        and antecedent:
          "Pure pp_unary_ty w X
            \<and> pp_t_eqv Prop w q ?r
            \<and> pp_t_eqv Prop w ?d (X \<acute> q)"
      then have X_pure: "Pure pp_unary_ty w X"
        and qr: "pp_t_eqv Prop w q ?r"
        and d_Xq: "pp_t_eqv Prop w ?d (X \<acute> q)"
        by auto
      have Xq_dom: "Elem (X \<acute> q) (pp_t_domain Prop)"
        using X_dom q_dom unfolding pp_unary_ty_def
        by (rule pp_t_app_closed)
      have Xr_dom: "Elem (X \<acute> ?r) (pp_t_domain Prop)"
        using X_dom r_dom unfolding pp_unary_ty_def
        by (rule pp_t_app_closed)
      have Xq_Xr: "pp_t_eqv Prop w (X \<acute> q) (X \<acute> ?r)"
        using X_dom q_dom r_dom qr unfolding pp_unary_ty_def
        by (rule pp_t_arrow_member_respects)
      have d_Xr: "pp_t_eqv Prop w ?d (X \<acute> ?r)"
        using d_dom Xq_dom Xr_dom d_Xq Xq_Xr
        by (rule pp_t_eqv_transitive)
      have rr: "pp_t_eqv Prop w ?r ?r"
        by (rule pp_t_eqv_reflexive[OF r_dom])
      have D_X: "pp_t_eqv pp_unary_ty w D X"
        using qss D_dom X_dom r_dom D_pure X_pure rr d_Xr
        by blast
      have dd: "pp_t_eqv Prop w ?d ?d"
        by (rule pp_t_eqv_reflexive[OF d_dom])
      have Dd_Xd: "pp_t_eqv Prop w (D \<acute> ?d) (X \<acute> ?d)"
        using D_X d_dom d_dom dd unfolding pp_unary_ty_def
        by (rule pp_t_app_respects)
      show "\<not> pp_t_holds (X \<acute> ?d) w"
        using false_Dd pp_t_prop_eqv_at[OF Dd_Xd, of w]
        by blast
    qed
    show "pp_t_holds (D \<acute> ?d) w"
      using diagonal rhs by blast
  qed
  show False
    using not_true true_if_not by blast
qed

theorem pp_t_M1_fn59_PP_failure:
  assumes background_valid:
      "MovingTreeConstants.TreeHenkin.gvalid_set
        (pp_M1_fn59_axioms - {pp_target_PP})"
    and qss_valid:
      "MovingTreeConstants.TreeHenkin.gvalid [] pp_QSS"
  shows "\<not> MovingTreeConstants.TreeHenkin.gvalid [] pp_target_PP"
proof
  assume PP_valid:
    "MovingTreeConstants.TreeHenkin.gvalid [] pp_target_PP"
  have PP_all:
      "\<And>\<Gamma>. MovingTreeConstants.TreeHenkin.gvalid
        \<Gamma> pp_target_PP"
    using typed_pp_target_PP PP_valid
    by (rule MovingTreeConstants.pp_t_closed_gvalid_all_contexts)
  have axioms_valid:
      "MovingTreeConstants.TreeHenkin.gvalid_set pp_M1_fn59_axioms"
    unfolding MovingTreeConstants.TreeHenkin.gvalid_set_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume "A \<in> pp_M1_fn59_axioms"
    then show
      "MovingTreeConstants.TreeHenkin.gvalid \<Gamma> A"
    proof (cases "A = pp_target_PP")
      case True
      then show ?thesis using PP_all by simp
    next
      case False
      then have "A \<in> pp_M1_fn59_axioms - {pp_target_PP}"
        using \<open>A \<in> pp_M1_fn59_axioms\<close> by blast
      then show ?thesis
        using background_valid
        unfolding MovingTreeConstants.TreeHenkin.gvalid_set_def
        by blast
    qed
  qed
  have liar_pure_valid:
      "MovingTreeConstants.TreeHenkin.gvalid []
        (pp_pure pp_unary_ty pp_M1_fn59_liar)"
    using MovingTreeConstants.pp_t_base_sound
      MovingTreeConstants.pp_t_zeta_sound
      axioms_valid pp_M1_fn59_liar_pure
    by (rule MovingTreeConstants.TreeHenkin.CEV_axiom_soundness)
  let ?rho = "pp_t_list_env []"
  have pure_holds:
      "pp_t_holds
        (pp_t_eval (pp_t_moving_internal_constants Pure) ?rho
          (pp_pure pp_unary_ty pp_M1_fn59_liar)) w"
    using MovingTreeConstants.TreeHenkin.gvalidD[
      OF liar_pure_valid, of "[]" w]
    unfolding MovingTreeConstants.pp_t_den_def
    by simp
  have D_pure:
      "Pure pp_unary_ty w
        (pp_t_eval (pp_t_moving_internal_constants Pure) ?rho
          pp_M1_fn59_liar)"
    using pure_holds
      pp_t_moving_eval_pure_holds[
        OF typed_pp_M1_fn59_liar pp_t_empty_env_typed]
    by blast
  have qss_holds:
      "pp_t_holds
        (pp_t_eval (pp_t_moving_internal_constants Pure) ?rho pp_QSS) w"
    using MovingTreeConstants.TreeHenkin.gvalidD[
      OF qss_valid, of "[]" w]
    unfolding MovingTreeConstants.pp_t_den_def
    by simp
  show False
    using D_pure qss_holds
    by (rule pp_t_M1_fn59_diagonal_contradiction)
qed

end

end
