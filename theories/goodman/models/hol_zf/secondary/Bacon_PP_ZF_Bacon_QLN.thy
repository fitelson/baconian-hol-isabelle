theory Bacon_PP_ZF_Bacon_QLN
  imports Bacon_PP_ZF_Bacon_10_1
begin

section \<open>Bacon's omitted QLN verification\<close>

text \<open>
  Bacon's appendix defines an entity to be pure at a world when its view there
  is the denotation of a closed term containing only logical vocabulary.  It
  defines the fundamental entities analogously from the nonlogical constants,
  and then states without proof that the resulting interpretation validates
  Quantified Logical Necessity.

  In Goodman's unique-fundamental-proposition specialization, the only
  nonvacuous instances are zeroary and unary.  The generic-seed interpretation
  is the corresponding completed interpretation: its pure extension is the
  complete closed-logical stock, and its unique fundamental proposition was
  chosen by the countable gluing construction so that unary Recombination
  holds.  It remains to verify Exhaustion.  The key fact is that the denotation
  of every closed logical term is invariant under every cone restriction.
\<close>

subsection \<open>Zeroary Exhaustion\<close>

lemma pp_t_closed_logical_true_is_necessary:
  assumes P: "Elem P (pp_t_domain Prop)"
    and pure: "pp_t_closed_logical_stock Prop w P"
    and true: "pp_t_holds P w"
  shows "pp_t_eqv Prop w P (pp_zf_truth True)"
proof -
  obtain M where typed: "[] \<turnstile> M : Prop"
    and logical: "pp_logical_vocabulary M"
    and PM: "pp_t_eqv Prop w P (pp_t_closed_den M)"
    using pure unfolding pp_t_closed_logical_stock_def by blast
  have M_domain: "Elem (pp_t_closed_den M) (pp_t_domain Prop)"
    using pp_t_closed_den_in_domain[OF typed] .
  have M_root:
      "pp_t_eqv Prop [] (pp_t_closed_den M)
        (pp_zf_truth (pp_t_holds (pp_t_closed_den M) []))"
    using pp_t_closed_logical_prop_den_root_truth[OF typed logical] .
  have PM_at_w:
      "pp_t_holds P w = pp_t_holds (pp_t_closed_den M) w"
    using pp_t_prop_eqv_at[OF PM, of w] by simp
  have M_root_at_w:
      "pp_t_holds (pp_t_closed_den M) w =
        pp_t_holds
          (pp_zf_truth (pp_t_holds (pp_t_closed_den M) [])) w"
    using pp_t_prop_eqv_at[
      OF pp_t_eqv_persistent[OF M_root, of w], of w] by simp
  have root_true: "pp_t_holds (pp_t_closed_den M) []"
    using true PM_at_w M_root_at_w by simp
  have M_true_root:
      "pp_t_eqv Prop [] (pp_t_closed_den M) (pp_zf_truth True)"
    using M_root root_true by simp
  have M_true_w:
      "pp_t_eqv Prop w (pp_t_closed_den M) (pp_zf_truth True)"
    using pp_t_eqv_persistent[OF M_true_root, of w] by simp
  have truth_domain:
      "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  show ?thesis
    using pp_t_eqv_transitive[
      OF P M_domain truth_domain PM M_true_w] .
qed

lemma pp_t_generic_zeroary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_zeroary_exhaustion) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_exhaustion_def
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
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> pp_t_closed_logical_stock Prop w P"
      using pp_t_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    show "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_t_eval_Imp_holds
      using pure_iff pp_t_closed_logical_true_is_necessary[OF P]
      by (simp add: pp_t_eval_ObjBox_holds)
  qed
qed

theorem pp_t_generic_zeroary_exhaustion_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_zeroary_exhaustion_holds by blast

subsection \<open>Unary Exhaustion\<close>

lemma pp_t_closed_logical_unary_exhausts:
  assumes X: "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_t_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w X"
    and r: "Elem r (pp_t_domain Prop)"
    and universal:
      "\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
        pp_t_holds (X \<acute> q) w"
  shows "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> r) v"
proof (intro allI impI)
  fix v
  assume wv: "prefix w v"
  obtain u where v: "v = w @ u"
    using wv unfolding prefix_def by blast
  obtain M where typed:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
    and XM:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) w
        X (pp_t_closed_den M)"
    using X_stock unfolding pp_t_closed_logical_stock_def by blast
  let ?M = "pp_t_closed_den M"
  let ?p = "pp_t_cone_restrict Prop v r"
  let ?q = "pp_t_cone_lift w ?p"
  have M_domain:
      "Elem ?M (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_closed_den_in_domain[OF typed] .
  have p: "Elem ?p (pp_t_domain Prop)"
    using pp_t_cone_restrict_in_domain[OF r] .
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have q_p: "pp_t_cone_rel Prop w ?q ?p"
    using pp_t_cone_extend_related[OF p, of w] by simp
  have r_p: "pp_t_cone_rel Prop v r ?p"
    using pp_t_cone_restrict_related[OF r] .
  have M_cone_w:
      "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) w ?M ?M"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
  have M_cone_v:
      "pp_t_cone_rel (Prop \<rightarrow>\<^sub>o Prop) v ?M ?M"
    using UnconditionalCone.pp_t_closed_logical_den_cone_related[
      OF typed logical] .
  have Xq_Mq:
      "pp_t_eqv Prop w (X \<acute> ?q) (?M \<acute> ?q)"
  proof -
    have qq: "pp_t_eqv Prop w ?q ?q"
      using pp_t_eqv_reflexive[OF q] .
    show ?thesis
      using pp_t_app_respects[OF XM q q qq] .
  qed
  have Xq_true: "pp_t_holds (X \<acute> ?q) w"
    using universal q by blast
  have Mq_true: "pp_t_holds (?M \<acute> ?q) w"
    using pp_t_prop_eqv_at[OF Xq_Mq, of w] Xq_true by simp
  have Mq_Mp: "pp_t_cone_rel Prop w (?M \<acute> ?q) (?M \<acute> ?p)"
    using M_cone_w q p q_p by auto
  have Mq_Mp_at_root:
      "pp_t_holds (?M \<acute> ?q) w
        \<longleftrightarrow> pp_t_holds (?M \<acute> ?p) []"
  proof -
    have relation:
        "\<forall>u. pp_t_holds (?M \<acute> ?q) (w @ u)
          \<longleftrightarrow> pp_t_holds (?M \<acute> ?p) u"
      using Mq_Mp by simp
    show ?thesis
      using relation[rule_format, of "[]"] by simp
  qed
  have Mp_true: "pp_t_holds (?M \<acute> ?p) []"
    using Mq_Mp_at_root Mq_true by blast
  have Mr_Mp: "pp_t_cone_rel Prop v (?M \<acute> r) (?M \<acute> ?p)"
    using M_cone_v r p r_p by auto
  have Mr_Mp_at_root:
      "pp_t_holds (?M \<acute> r) v
        \<longleftrightarrow> pp_t_holds (?M \<acute> ?p) []"
  proof -
    have relation:
        "\<forall>u. pp_t_holds (?M \<acute> r) (v @ u)
          \<longleftrightarrow> pp_t_holds (?M \<acute> ?p) u"
      using Mr_Mp by simp
    show ?thesis
      using relation[rule_format, of "[]"] by simp
  qed
  have Mr_true: "pp_t_holds (?M \<acute> r) v"
    using Mr_Mp_at_root Mp_true by blast
  have XM_v:
      "pp_t_eqv (Prop \<rightarrow>\<^sub>o Prop) v X ?M"
    using pp_t_eqv_persistent[OF XM wv] .
  have rr: "pp_t_eqv Prop v r r"
    using pp_t_eqv_reflexive[OF r] .
  have Xr_Mr: "pp_t_eqv Prop v (X \<acute> r) (?M \<acute> r)"
    using pp_t_app_respects[OF XM_v r r rr] .
  show "pp_t_holds (X \<acute> r) v"
    using pp_t_prop_eqv_at[OF Xr_Mr, of v] Mr_true by simp
qed

lemma pp_t_generic_unary_exhaustion_holds_iff:
  "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_t_domain Prop) \<longrightarrow>
        (pp_t_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_t_generic_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
            pp_t_holds (X \<acute> q) w)
          \<longrightarrow>
          (\<forall>v. prefix w v \<longrightarrow>
            pp_t_holds (X \<acute> r) v))))"
  by (simp add: pp_unary_exhaustion_def
      pp_pure_def pp_fun_def pp_t_classifier_holds
      pp_t_prop_eqv_truth_iff pp_t_eval_ObjBox_holds
      extend_env.simps pp_t_three_extensions_index_two)

theorem pp_t_generic_unary_exhaustion_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_t_generic_unary_exhaustion_holds_iff
  using pp_t_closed_logical_unary_exhausts by blast

theorem pp_t_generic_unary_exhaustion_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_unary_exhaustion_holds by blast

subsection \<open>Quantified Logical Necessity\<close>

lemma pp_t_generic_zeroary_QLN_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_zeroary_QLN) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_QLN_def
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
          (pp_t_eval pp_t_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> pp_t_closed_logical_stock Prop w P"
      using pp_t_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_t_eqv Prop w P (pp_zf_truth True) \<longrightarrow>
          pp_t_holds P w"
      using pp_t_prop_eqv_at[of w P "pp_zf_truth True" w] by simp
    have exhaustion:
        "pp_t_closed_logical_stock Prop w P \<longrightarrow>
          pp_t_holds P w \<longrightarrow>
          pp_t_eqv Prop w P (pp_zf_truth True)"
      using pp_t_closed_logical_true_is_necessary[OF P] by blast
    show "pp_t_holds
        (pp_t_eval pp_t_generic_internal_constants
          (extend_env P \<rho>)
          (Imp (pp_pure Prop (Var 0))
            ((\<box>\<^sub>o (Var 0)) \<longleftrightarrow>\<^sub>o Var 0))) w"
      apply (simp only: pp_t_eval_Imp_holds
          pp_t_eval_Conj_holds pp_t_eval_ObjBox_holds
          pp_t_eval.simps extend_env.simps pp_t_holds_prop)
      using pure_iff modal_T exhaustion by blast
  qed
qed

theorem pp_t_generic_zeroary_QLN_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma> pp_zeroary_QLN"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_zeroary_QLN_holds by blast

lemma pp_t_generic_unary_QLN_instance:
  assumes X: "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and r: "Elem r (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_eval pp_t_generic_internal_constants
        (extend_env r (extend_env X \<rho>))
        (Imp
          (Conj
            (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_fun Prop (Var 0)))
          ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
            Forall Prop (App (Var 2) (Var 0))))) w"
proof -
  have base: "pp_t_env_typed [] \<rho>"
    by (simp add: pp_t_env_typed_def lookup_def)
  have env_X:
      "pp_t_env_typed [Prop \<rightarrow>\<^sub>o Prop]
        (extend_env X \<rho>)"
    using pp_t_env_typed_extend[OF base X] .
  let ?env = "extend_env r (extend_env X \<rho>)"
      have env:
          "pp_t_env_typed [Prop, Prop \<rightarrow>\<^sub>o Prop] ?env"
        using pp_t_env_typed_extend[OF env_X r] .
      have X_var:
          "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile>
            Var 1 : (Prop \<rightarrow>\<^sub>o Prop)"
        by simp
      have r_var:
          "[Prop, Prop \<rightarrow>\<^sub>o Prop] \<turnstile> Var 0 : Prop"
        by simp
      have pure_iff:
          "pp_t_holds
              (pp_t_eval pp_t_generic_internal_constants ?env
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))) w
            \<longleftrightarrow>
            pp_t_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop) w X"
        using pp_t_generic_eval_pure_holds[OF X_var env, of w]
        by simp
      have fun_iff:
          "pp_t_holds
              (pp_t_eval pp_t_generic_internal_constants ?env
                (pp_fun Prop (Var 0))) w
            \<longleftrightarrow>
            pp_t_generic_fundamental_at Prop w r"
        using pp_t_generic_eval_fun_holds[OF r_var env, of w]
        by simp
      have box_iff:
          "pp_t_holds
              (pp_t_eval pp_t_generic_internal_constants ?env
                (\<box>\<^sub>o (App (Var 1) (Var 0)))) w
            \<longleftrightarrow>
            (\<forall>v. prefix w v \<longrightarrow>
              pp_t_holds (X \<acute> r) v)"
        by (simp only: pp_t_eval_ObjBox_holds
            pp_t_eval.simps extend_env.simps
            One_nat_def pp_t_prop_eqv_truth_iff)
      have universal_iff:
          "pp_t_holds
              (pp_t_eval pp_t_generic_internal_constants ?env
                (Forall Prop (App (Var 2) (Var 0)))) w
            \<longleftrightarrow>
            (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
              pp_t_holds (X \<acute> q) w)"
        by (simp only: pp_t_eval_Forall_holds
            pp_t_eval.simps extend_env.simps
            pp_t_three_extensions_index_two pp_t_holds_prop)
      have recombination:
          "pp_t_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop) w X \<longrightarrow>
            pp_t_generic_fundamental_at Prop w r \<longrightarrow>
            (\<forall>v. prefix w v \<longrightarrow>
              pp_t_holds (X \<acute> r) v) \<longrightarrow>
            (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
              pp_t_holds (X \<acute> q) w)"
        using pp_t_generic_fundamental_recombines[OF X _ r]
        by blast
      have exhaustion:
          "pp_t_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop) w X \<longrightarrow>
            (\<forall>q. Elem q (pp_t_domain Prop) \<longrightarrow>
              pp_t_holds (X \<acute> q) w) \<longrightarrow>
            (\<forall>v. prefix w v \<longrightarrow>
              pp_t_holds (X \<acute> r) v)"
        using pp_t_closed_logical_unary_exhausts[OF X _ r]
        by blast
  show "pp_t_holds
          (pp_t_eval pp_t_generic_internal_constants ?env
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              ((\<box>\<^sub>o (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o
                Forall Prop (App (Var 2) (Var 0))))) w"
      apply (simp only: pp_t_eval_Imp_holds pp_t_eval_Conj_holds)
      using pure_iff fun_iff box_iff universal_iff
        recombination exhaustion by blast
qed

theorem pp_t_generic_unary_QLN_holds:
  "pp_t_holds
    (pp_t_eval pp_t_generic_internal_constants \<rho>
      pp_unary_QLN) w"
  unfolding pp_unary_QLN_def
  apply (simp only: pp_t_eval_Forall_holds)
  using pp_t_generic_unary_QLN_instance by blast

theorem pp_t_generic_unary_QLN_gvalid:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma> pp_unary_QLN"
  unfolding GenericTreeConstants.TreeHenkin.gvalid_def
    GenericTreeConstants.pp_t_den_def
  using pp_t_generic_unary_QLN_holds by blast

theorem pp_t_Bacon_QLN_unique_fundamental_proposition:
  "GenericTreeConstants.TreeHenkin.gvalid \<Gamma> pp_zeroary_QLN
    \<and>
   GenericTreeConstants.TreeHenkin.gvalid \<Gamma> pp_unary_QLN"
  using pp_t_generic_zeroary_QLN_gvalid
    pp_t_generic_unary_QLN_gvalid by blast

text \<open>
  This discharges Bacon's omitted QLN verification for the specialization used
  in Goodman's consistency question.  It does not supply the future-work
  extension mentioned by Bacon for arbitrary individual types or signatures
  with several pairwise-distinct fundamental entities.
\<close>

end
