theory Bacon_PP_ZF_Tree_Stabilizer_Orbit
  imports Bacon_PP_ZF_Tree_Quotient_Diagonal_Builder
begin

section \<open>The actual tree-model precomposition action\<close>

definition pp_t_qd_precompose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_qd_precompose G \<psi> =
    Lambda (pp_t_domain Prop) (\<lambda>p. G \<acute> (\<psi> \<acute> p))"

lemma pp_t_qd_precompose_in_domain:
  assumes G: "Elem G (pp_t_domain pp_t_unary_type)"
    and psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
  shows "Elem (pp_t_qd_precompose G \<psi>)
    (pp_t_domain pp_t_unary_type)"
proof (unfold pp_t_qd_precompose_def, rule pp_t_lambda_closed)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  have psi_p: "Elem (\<psi> \<acute> p) (pp_t_domain Prop)"
    using pp_t_app_closed[OF psi p] .
  show "Elem (G \<acute> (\<psi> \<acute> p)) (pp_t_domain Prop)"
    using pp_t_app_closed[OF G psi_p] .
next
  fix w p q
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_eqv Prop w p q"
  have psi_p: "Elem (\<psi> \<acute> p) (pp_t_domain Prop)"
    using pp_t_app_closed[OF psi p] .
  have psi_q: "Elem (\<psi> \<acute> q) (pp_t_domain Prop)"
    using pp_t_app_closed[OF psi q] .
  have images:
      "pp_t_eqv Prop w (\<psi> \<acute> p) (\<psi> \<acute> q)"
    using pp_t_arrow_member_respects[OF psi p q pq] .
  show "pp_t_eqv Prop w
      (G \<acute> (\<psi> \<acute> p)) (G \<acute> (\<psi> \<acute> q))"
    using pp_t_arrow_member_respects[
      OF G psi_p psi_q images] .
qed

lemma pp_t_qd_precompose_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_qd_precompose G \<psi> \<acute> p =
    G \<acute> (\<psi> \<acute> p)"
  using p by (simp add: pp_t_qd_precompose_def Lambda_app)

lemma pp_b_operator_of_precompose:
  assumes G: "Elem G (pp_t_domain pp_t_unary_type)"
    and psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
  shows "pp_b_operator_of (pp_t_qd_precompose G \<psi>) =
    pp_b_operator_of G \<circ> pp_b_operator_of \<psi>"
proof (rule ext)
  fix P
  have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have psi_p: "Elem (\<psi> \<acute> pp_zf_of_b P) (pp_t_domain Prop)"
    using pp_t_app_closed[OF psi p] .
  show "pp_b_operator_of (pp_t_qd_precompose G \<psi>) P =
      (pp_b_operator_of G \<circ> pp_b_operator_of \<psi>) P"
    unfolding pp_b_operator_of_def comp_def
    using pp_zf_of_b_of_zf[OF psi_p]
    by (simp add: pp_t_qd_precompose_apply[OF p])
qed

section \<open>Internal bijectivity and the stabilizer relation\<close>

definition pp_t_qd_world_bijective ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_world_bijective w \<psi> \<longleftrightarrow>
    ((\<forall>p q.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      Elem q (pp_t_domain Prop) \<longrightarrow>
      pp_t_eqv Prop w (\<psi> \<acute> p) (\<psi> \<acute> q)
        \<longrightarrow> pp_t_eqv Prop w p q) \<and>
     (\<forall>q.
      Elem q (pp_t_domain Prop) \<longrightarrow>
      (\<exists>p.
        Elem p (pp_t_domain Prop) \<and>
        pp_t_eqv Prop w (\<psi> \<acute> p) q)))"

definition pp_t_qd_stabilizer_orbit ::
    "bool list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_stabilizer_orbit w q F G \<longleftrightarrow>
    (\<exists>\<psi>.
      Elem \<psi> (pp_t_domain pp_t_unary_type) \<and>
      pp_t_qd_world_bijective w \<psi> \<and>
      pp_t_eqv pp_t_unary_type w F (pp_t_qd_precompose G \<psi>) \<and>
      pp_t_eqv Prop w (\<psi> \<acute> q) q)"

definition pp_qd_stabilizer_relation :: oterm where
  "pp_qd_stabilizer_relation =
    Lam Prop
      (Lam pp_t_unary_type
        (Lam pp_t_unary_type
          (Exists pp_t_unary_type
            (Conj
              (Conj
                (Forall Prop
                  (Forall Prop
                    (Imp
                      (Eq Prop
                        (App (Var 2) (Var 1))
                        (App (Var 2) (Var 0)))
                      (Eq Prop (Var 1) (Var 0)))))
                (Forall Prop
                  (Exists Prop
                    (Eq Prop
                      (App (Var 2) (Var 0))
                      (Var 1)))))
              (Conj
                (Eq pp_t_unary_type
                  (Var 2)
                  (Lam Prop
                    (App
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Eq Prop
                  (App (Var 0) (Var 3))
                  (Var 3)))))))"

lemma pp_qd_stabilizer_relation_typed:
  "[] \<turnstile> pp_qd_stabilizer_relation :
    pp_t_qd_relation_type"
  unfolding pp_qd_stabilizer_relation_def
  by (intro has_type.Lam has_type.Exists has_type.Forall
      has_type.Imp has_type.Conj has_type.Eq
      has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma pp_qd_stabilizer_relation_logical:
  "pp_logical_vocabulary pp_qd_stabilizer_relation"
  unfolding pp_qd_stabilizer_relation_def
    pp_logical_vocabulary_def by simp

abbreviation pp_t_qd_stabilizer_relation :: ZF where
  "pp_t_qd_stabilizer_relation \<equiv>
    pp_t_closed_den pp_qd_stabilizer_relation"

lemma pp_t_qd_stabilizer_relation_in_domain:
  "Elem pp_t_qd_stabilizer_relation
    (pp_t_domain pp_t_qd_relation_type)"
  using pp_t_closed_den_in_domain[
    OF pp_qd_stabilizer_relation_typed] .

theorem pp_t_qd_stabilizer_relation_holds:
  assumes q: "Elem q (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
  shows "pp_t_holds
      (((pp_t_qd_stabilizer_relation \<acute> q) \<acute> F) \<acute> G) w
    \<longleftrightarrow> pp_t_qd_stabilizer_orbit w q F G"
  unfolding pp_t_closed_den_def
    pp_qd_stabilizer_relation_def
    pp_t_qd_stabilizer_orbit_def
    pp_t_qd_world_bijective_def
    pp_t_qd_precompose_def
  using q F G
  by (simp add: Lambda_app pp_t_default_constants_def
      pp_t_closed_env_def extend_env.simps pp_t_app_closed
      numeral_eq_Suc)

section \<open>Root identification with the ambient action\<close>

lemma pp_t_qd_root_prop_eqv_iff_eq:
  assumes P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_t_eqv Prop [] P Q \<longleftrightarrow> P = Q"
  by (rule pp_t_root_eqv_iff_eq[OF P Q])

lemma pp_b_of_zf_eq_iff:
  assumes P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
  shows "pp_b_of_zf P = pp_b_of_zf Q \<longleftrightarrow> P = Q"
proof
  assume encoded: "pp_b_of_zf P = pp_b_of_zf Q"
  have decoded:
      "pp_zf_of_b (pp_b_of_zf P) =
        pp_zf_of_b (pp_b_of_zf Q)"
    using encoded by (rule arg_cong)
  show "P = Q"
    using decoded pp_zf_of_b_of_zf[OF P]
      pp_zf_of_b_of_zf[OF Q] by simp
next
  assume "P = Q"
  then show "pp_b_of_zf P = pp_b_of_zf Q"
    by simp
qed

lemma pp_b_operator_of_encoded:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_b_operator_of \<psi> (pp_b_of_zf p) =
    pp_b_of_zf (\<psi> \<acute> p)"
  unfolding pp_b_operator_of_def
  using pp_zf_of_b_of_zf[OF p] by simp

lemma pp_t_qd_world_bijective_root_imp:
  assumes psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
    and internal: "pp_t_qd_world_bijective [] \<psi>"
  shows "bij (pp_b_operator_of \<psi>)"
proof -
  have internal_inj:
      "\<And>p q.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        Elem q (pp_t_domain Prop) \<Longrightarrow>
        pp_t_eqv Prop [] (\<psi> \<acute> p) (\<psi> \<acute> q) \<Longrightarrow>
        pp_t_eqv Prop [] p q"
    using internal unfolding pp_t_qd_world_bijective_def by blast
  have internal_surj:
      "\<And>q.
        Elem q (pp_t_domain Prop) \<Longrightarrow>
        \<exists>p. Elem p (pp_t_domain Prop) \<and>
          pp_t_eqv Prop [] (\<psi> \<acute> p) q"
    using internal unfolding pp_t_qd_world_bijective_def by blast
  have raw_inj: "inj (pp_b_operator_of \<psi>)"
  proof (rule injI)
    fix P Q
    assume outputs:
        "pp_b_operator_of \<psi> P = pp_b_operator_of \<psi> Q"
    let ?p = "pp_zf_of_b P"
    let ?q = "pp_zf_of_b Q"
    have p: "Elem ?p (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have q: "Elem ?q (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have psi_p: "Elem (\<psi> \<acute> ?p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi p] .
    have psi_q: "Elem (\<psi> \<acute> ?q) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi q] .
    have encoded_outputs:
        "pp_b_of_zf (\<psi> \<acute> ?p) =
          pp_b_of_zf (\<psi> \<acute> ?q)"
      using outputs pp_b_operator_of_encoded[OF p, of \<psi>]
        pp_b_operator_of_encoded[OF q, of \<psi>] by simp
    have output_eq: "\<psi> \<acute> ?p = \<psi> \<acute> ?q"
      using pp_b_of_zf_eq_iff[OF psi_p psi_q]
        encoded_outputs by blast
    have output_eqv:
        "pp_t_eqv Prop [] (\<psi> \<acute> ?p) (\<psi> \<acute> ?q)"
      using pp_t_qd_root_prop_eqv_iff_eq[OF psi_p psi_q]
        output_eq by blast
    have input_eqv: "pp_t_eqv Prop [] ?p ?q"
      using internal_inj[OF p q output_eqv] .
    have input_eq: "?p = ?q"
      using pp_t_qd_root_prop_eqv_iff_eq[OF p q] input_eqv
      by blast
    show "P = Q"
      using arg_cong[OF input_eq, of pp_b_of_zf] by simp
  qed
  have raw_surj: "surj (pp_b_operator_of \<psi>)"
    unfolding surj_def
  proof (intro allI)
    fix Q
    let ?q = "pp_zf_of_b Q"
    have q: "Elem ?q (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    obtain p where p: "Elem p (pp_t_domain Prop)"
      and output_eqv: "pp_t_eqv Prop [] (\<psi> \<acute> p) ?q"
      using internal_surj[OF q] by blast
    have psi_p: "Elem (\<psi> \<acute> p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi p] .
    have output_eq: "\<psi> \<acute> p = ?q"
      using pp_t_qd_root_prop_eqv_iff_eq[OF psi_p q]
        output_eqv by blast
    show "\<exists>P. Q = pp_b_operator_of \<psi> P"
    proof (rule exI[of _ "pp_b_of_zf p"])
      have action:
          "pp_b_operator_of \<psi> (pp_b_of_zf p) =
            pp_b_of_zf (\<psi> \<acute> p)"
        by (rule pp_b_operator_of_encoded[OF p])
      show "Q = pp_b_operator_of \<psi> (pp_b_of_zf p)"
        using action output_eq by simp
    qed
  qed
  show "bij (pp_b_operator_of \<psi>)"
    using raw_inj raw_surj by (simp add: bij_def)
qed

lemma pp_t_qd_world_bijective_root_if:
  assumes psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
    and raw_bij: "bij (pp_b_operator_of \<psi>)"
  shows "pp_t_qd_world_bijective [] \<psi>"
proof -
  have raw_inj: "inj (pp_b_operator_of \<psi>)"
    using bij_is_inj[OF raw_bij] .
  have raw_surj: "surj (pp_b_operator_of \<psi>)"
    using bij_is_surj[OF raw_bij] .
  have internal_inj:
      "\<And>p q.
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        Elem q (pp_t_domain Prop) \<Longrightarrow>
        pp_t_eqv Prop [] (\<psi> \<acute> p) (\<psi> \<acute> q) \<Longrightarrow>
        pp_t_eqv Prop [] p q"
  proof -
    fix p q
    assume p: "Elem p (pp_t_domain Prop)"
      and q: "Elem q (pp_t_domain Prop)"
      and outputs:
        "pp_t_eqv Prop [] (\<psi> \<acute> p) (\<psi> \<acute> q)"
    have psi_p: "Elem (\<psi> \<acute> p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi p] .
    have psi_q: "Elem (\<psi> \<acute> q) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi q] .
    have output_eq: "\<psi> \<acute> p = \<psi> \<acute> q"
      using pp_t_qd_root_prop_eqv_iff_eq[OF psi_p psi_q]
        outputs by blast
    have raw_eq:
        "pp_b_operator_of \<psi> (pp_b_of_zf p) =
          pp_b_operator_of \<psi> (pp_b_of_zf q)"
      using pp_b_operator_of_encoded[OF p, of \<psi>]
        pp_b_operator_of_encoded[OF q, of \<psi>] output_eq
      by simp
    have inputs: "pp_b_of_zf p = pp_b_of_zf q"
      using injD[OF raw_inj raw_eq] .
    have input_eq: "p = q"
      using pp_b_of_zf_eq_iff[OF p q] inputs by blast
    show "pp_t_eqv Prop [] p q"
      using pp_t_qd_root_prop_eqv_iff_eq[OF p q]
        input_eq by blast
  qed
  have internal_surj:
      "\<And>q.
        Elem q (pp_t_domain Prop) \<Longrightarrow>
        \<exists>p. Elem p (pp_t_domain Prop) \<and>
          pp_t_eqv Prop [] (\<psi> \<acute> p) q"
  proof -
    fix q
    assume q: "Elem q (pp_t_domain Prop)"
    obtain P where raw_output:
        "pp_b_operator_of \<psi> P = pp_b_of_zf q"
      using surjD[OF raw_surj, of "pp_b_of_zf q"] by blast
    let ?p = "pp_zf_of_b P"
    have p: "Elem ?p (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have psi_p: "Elem (\<psi> \<acute> ?p) (pp_t_domain Prop)"
      using pp_t_app_closed[OF psi p] .
    have action:
        "pp_b_operator_of \<psi> (pp_b_of_zf ?p) =
          pp_b_of_zf (\<psi> \<acute> ?p)"
      by (rule pp_b_operator_of_encoded[OF p])
    have encoded_output:
        "pp_b_of_zf (\<psi> \<acute> ?p) = pp_b_of_zf q"
      using raw_output action by simp
    have output_eq: "\<psi> \<acute> ?p = q"
      using pp_b_of_zf_eq_iff[OF psi_p q]
        encoded_output by blast
    have output_eqv: "pp_t_eqv Prop [] (\<psi> \<acute> ?p) q"
      using pp_t_qd_root_prop_eqv_iff_eq[OF psi_p q]
        output_eq by blast
    show "\<exists>p. Elem p (pp_t_domain Prop) \<and>
        pp_t_eqv Prop [] (\<psi> \<acute> p) q"
      using p output_eqv by blast
  qed
  show ?thesis
    unfolding pp_t_qd_world_bijective_def
    using internal_inj internal_surj by blast
qed

theorem pp_t_qd_world_bijective_root_iff:
  assumes psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
  shows "pp_t_qd_world_bijective [] \<psi>
    \<longleftrightarrow> bij (pp_b_operator_of \<psi>)"
proof
  assume "pp_t_qd_world_bijective [] \<psi>"
  show "bij (pp_b_operator_of \<psi>)"
    by (rule pp_t_qd_world_bijective_root_imp[OF psi
          \<open>pp_t_qd_world_bijective [] \<psi>\<close>])
next
  assume "bij (pp_b_operator_of \<psi>)"
  show "pp_t_qd_world_bijective [] \<psi>"
    by (rule pp_t_qd_world_bijective_root_if[OF psi
          \<open>bij (pp_b_operator_of \<psi>)\<close>])
qed

corollary pp_t_qd_root_bijection_induces_cone_bijections:
  assumes psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
    and internal: "pp_t_qd_world_bijective [] \<psi>"
  shows "bij (pp_b_induced (pp_b_operator_of \<psi>) w)"
proof -
  have raw: "bij (pp_b_operator_of \<psi>)"
    using pp_t_qd_world_bijective_root_imp[OF psi internal] .
  show ?thesis
    using pp_t_ambient_bijection_induces_cone_bijections[
      OF psi raw] .
qed

corollary pp_t_qd_root_bijection_inverse_respects_views:
  assumes psi: "Elem \<psi> (pp_t_domain pp_t_unary_type)"
    and internal: "pp_t_qd_world_bijective [] \<psi>"
  shows "pp_b_respects_views (inv (pp_b_operator_of \<psi>))"
proof -
  have raw: "bij (pp_b_operator_of \<psi>)"
    using pp_t_qd_world_bijective_root_imp[OF psi internal] .
  show ?thesis
    using pp_t_ambient_inverse_respects_views[OF psi raw] .
qed

definition pp_t_qd_ambient_stabilizer_orbit ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_ambient_stabilizer_orbit q F G \<longleftrightarrow>
    (\<exists>\<psi>.
      Elem \<psi> (pp_t_domain pp_t_unary_type) \<and>
      bij (pp_b_operator_of \<psi>) \<and>
      F = pp_t_qd_precompose G \<psi> \<and>
      \<psi> \<acute> q = q)"

theorem pp_t_qd_stabilizer_orbit_root_iff_ambient:
  assumes q: "Elem q (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
  shows "pp_t_qd_stabilizer_orbit [] q F G
    \<longleftrightarrow> pp_t_qd_ambient_stabilizer_orbit q F G"
proof
  assume orbit: "pp_t_qd_stabilizer_orbit [] q F G"
  obtain psi where
      psi: "Elem psi (pp_t_domain pp_t_unary_type)"
    and internal: "pp_t_qd_world_bijective [] psi"
    and composition:
      "pp_t_eqv pp_t_unary_type []
        F (pp_t_qd_precompose G psi)"
    and fixed: "pp_t_eqv Prop [] (psi \<acute> q) q"
    using orbit unfolding pp_t_qd_stabilizer_orbit_def
    by clarify
  have precompose:
      "Elem (pp_t_qd_precompose G psi)
        (pp_t_domain pp_t_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[OF G psi])
  have psi_q: "Elem (psi \<acute> q) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF psi q])
  have raw: "bij (pp_b_operator_of psi)"
    by (rule pp_t_qd_world_bijective_root_imp[OF psi internal])
  have composition_eq: "F = pp_t_qd_precompose G psi"
    using pp_t_root_eqv_iff_eq[OF F precompose] composition
    by (rule iffD1)
  have fixed_eq: "psi \<acute> q = q"
    using pp_t_qd_root_prop_eqv_iff_eq[OF psi_q q] fixed
    by (rule iffD1)
  show "pp_t_qd_ambient_stabilizer_orbit q F G"
    unfolding pp_t_qd_ambient_stabilizer_orbit_def
  proof (rule exI[of _ psi], intro conjI)
    show "Elem psi (pp_t_domain pp_t_unary_type)"
      by (rule psi)
    show "bij (pp_b_operator_of psi)"
      by (rule raw)
    show "F = pp_t_qd_precompose G psi"
      by (rule composition_eq)
    show "psi \<acute> q = q"
      by (rule fixed_eq)
  qed
next
  assume orbit: "pp_t_qd_ambient_stabilizer_orbit q F G"
  obtain psi where
      psi: "Elem psi (pp_t_domain pp_t_unary_type)"
    and raw: "bij (pp_b_operator_of psi)"
    and composition_eq: "F = pp_t_qd_precompose G psi"
    and fixed_eq: "psi \<acute> q = q"
    using orbit unfolding pp_t_qd_ambient_stabilizer_orbit_def
    by blast
  have precompose:
      "Elem (pp_t_qd_precompose G psi)
        (pp_t_domain pp_t_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[OF G psi])
  have psi_q: "Elem (psi \<acute> q) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF psi q])
  have internal: "pp_t_qd_world_bijective [] psi"
    by (rule pp_t_qd_world_bijective_root_if[OF psi raw])
  have composition:
      "pp_t_eqv pp_t_unary_type []
        F (pp_t_qd_precompose G psi)"
    using pp_t_root_eqv_iff_eq[OF F precompose] composition_eq
    by (rule iffD2)
  have fixed: "pp_t_eqv Prop [] (psi \<acute> q) q"
    using pp_t_qd_root_prop_eqv_iff_eq[OF psi_q q] fixed_eq
    by (rule iffD2)
  show "pp_t_qd_stabilizer_orbit [] q F G"
    unfolding pp_t_qd_stabilizer_orbit_def
  proof (rule exI[of _ psi], intro conjI)
    show "Elem psi (pp_t_domain pp_t_unary_type)"
      by (rule psi)
    show "pp_t_qd_world_bijective [] psi"
      by (rule internal)
    show "pp_t_eqv pp_t_unary_type []
        F (pp_t_qd_precompose G psi)"
      by (rule composition)
    show "pp_t_eqv Prop [] (psi \<acute> q) q"
      by (rule fixed)
  qed
qed

section \<open>Truth congruence and generatedness\<close>

lemma pp_t_qd_stabilizing_precomposition_in_orbit:
  assumes q: "Elem q (pp_t_domain Prop)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
    and psi: "Elem psi (pp_t_domain pp_t_unary_type)"
    and bijective: "pp_t_qd_world_bijective w psi"
    and fixed: "pp_t_eqv Prop w (psi \<acute> q) q"
  shows "pp_t_qd_stabilizer_orbit w q
    (pp_t_qd_precompose G psi) G"
proof -
  have precompose:
      "Elem (pp_t_qd_precompose G psi)
        (pp_t_domain pp_t_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[OF G psi])
  have composition:
      "pp_t_eqv pp_t_unary_type w
        (pp_t_qd_precompose G psi)
        (pp_t_qd_precompose G psi)"
    by (rule pp_t_eqv_reflexive[OF precompose])
  show ?thesis
    unfolding pp_t_qd_stabilizer_orbit_def
  proof (rule exI[of _ psi], intro conjI)
    show "Elem psi (pp_t_domain pp_t_unary_type)"
      by (rule psi)
    show "pp_t_qd_world_bijective w psi"
      by (rule bijective)
    show "pp_t_eqv pp_t_unary_type w
        (pp_t_qd_precompose G psi)
        (pp_t_qd_precompose G psi)"
      by (rule composition)
    show "pp_t_eqv Prop w (psi \<acute> q) q"
      by (rule fixed)
  qed
qed

corollary pp_t_qd_stabilizing_precomposition_relation_holds:
  assumes q: "Elem q (pp_t_domain Prop)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
    and psi: "Elem psi (pp_t_domain pp_t_unary_type)"
    and bijective: "pp_t_qd_world_bijective w psi"
    and fixed: "pp_t_eqv Prop w (psi \<acute> q) q"
  shows "pp_t_holds
    (((pp_t_qd_stabilizer_relation \<acute> q) \<acute>
      pp_t_qd_precompose G psi) \<acute> G) w"
proof -
  have precompose:
      "Elem (pp_t_qd_precompose G psi)
        (pp_t_domain pp_t_unary_type)"
    by (rule pp_t_qd_precompose_in_domain[OF G psi])
  have orbit:
      "pp_t_qd_stabilizer_orbit w q
        (pp_t_qd_precompose G psi) G"
    by (rule pp_t_qd_stabilizing_precomposition_in_orbit[
      OF q G psi bijective fixed])
  show ?thesis
    using pp_t_qd_stabilizer_relation_holds[
      OF q precompose G, of w] orbit
    by (rule iffD2)
qed

theorem pp_t_qd_stabilizer_orbit_truth_congruent:
  assumes q: "Elem q (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
    and orbit: "pp_t_qd_stabilizer_orbit w q F G"
  shows "pp_t_holds (F \<acute> q) w
    \<longleftrightarrow> pp_t_holds (G \<acute> q) w"
proof -
  obtain psi where
      psi: "Elem psi (pp_t_domain pp_t_unary_type)"
    and composition:
      "pp_t_eqv pp_t_unary_type w
        F (pp_t_qd_precompose G psi)"
    and fixed: "pp_t_eqv Prop w (psi \<acute> q) q"
    using orbit unfolding pp_t_qd_stabilizer_orbit_def by blast
  have precompose:
      "Elem (pp_t_qd_precompose G psi)
        (pp_t_domain pp_t_unary_type)"
    using pp_t_qd_precompose_in_domain[OF G psi] .
  have q_refl: "pp_t_eqv Prop w q q"
    using pp_t_eqv_reflexive[OF q] .
  have first:
      "pp_t_eqv Prop w
        (F \<acute> q) (pp_t_qd_precompose G psi \<acute> q)"
    using composition q q q_refl by simp
  have psi_q: "Elem (psi \<acute> q) (pp_t_domain Prop)"
    using pp_t_app_closed[OF psi q] .
  have second:
      "pp_t_eqv Prop w (G \<acute> (psi \<acute> q)) (G \<acute> q)"
    using pp_t_arrow_member_respects[
      OF G psi_q q fixed] .
  have combined:
      "pp_t_eqv Prop w (F \<acute> q) (G \<acute> q)"
  proof -
    have rewritten:
        "pp_t_eqv Prop w
          (F \<acute> q) (G \<acute> (psi \<acute> q))"
      using first pp_t_qd_precompose_apply[OF q, of G psi]
      by simp
    show ?thesis
      using pp_t_prop_eqv_transitive[OF rewritten second] .
  qed
  show ?thesis
    using combined by simp
qed

theorem pp_t_qd_stabilizer_relation_truth_congruent:
  assumes q: "Elem q (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_unary_type)"
    and relation:
      "pp_t_holds
        (((pp_t_qd_stabilizer_relation \<acute> q) \<acute> F) \<acute> G) w"
  shows "pp_t_holds (F \<acute> q) w
    \<longleftrightarrow> pp_t_holds (G \<acute> q) w"
proof -
  have orbit: "pp_t_qd_stabilizer_orbit w q F G"
    using relation
      pp_t_qd_stabilizer_relation_holds[OF q F G, of w]
    by blast
  show ?thesis
    using pp_t_qd_stabilizer_orbit_truth_congruent[
      OF q F G orbit] .
qed

theorem pp_t_qd_stabilizer_relation_in_enumerator_basis:
  "pp_t_qd_stabilizer_relation
    \<in> pp_t_enumerator_basis E pp_t_qd_relation_type"
  using pp_t_enumerator_basis_contains_logical[
    OF pp_qd_stabilizer_relation_typed
      pp_qd_stabilizer_relation_logical] .

context pp_t_cone_natural_enumerator
begin

theorem pp_t_qd_stabilizer_relation_in_generated_stock:
  "pp_t_basis_stock (pp_t_enumerator_basis E)
    pp_t_qd_relation_type [] pp_t_qd_stabilizer_relation"
  using TermBasis.pp_t_basis_stock_contains_logical_den[
    OF pp_qd_stabilizer_relation_typed
      pp_qd_stabilizer_relation_logical] .

theorem pp_t_qd_stabilizer_diagonal_in_generated_stock:
  assumes H:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        pp_t_qd_tag_type [] H"
  shows "pp_t_basis_stock (pp_t_enumerator_basis E)
    pp_t_unary_type []
    (pp_t_qd_den E H pp_t_qd_stabilizer_relation)"
  using pp_t_qd_den_in_generated_stock[
    OF H pp_t_qd_stabilizer_relation_in_generated_stock] .

end

end
