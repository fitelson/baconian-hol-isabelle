theory Bacon_PP_ZF_Tree_Boundary_Probe_Nonabsorption
  imports
    Higher_Order_Metaphysics_PP_ZF_Boundary_Operator_Probe.Bacon_PP_ZF_Tree_Boundary_Operator_Probe
begin

section \<open>Two distinct points on every moving boundary\<close>

lemma pp_t_future_world_flip_is_on_fundamental_boundary:
  assumes R: "Elem R (pp_t_domain Prop)"
    and wv: "prefix w v"
  shows "pp_t_fundamental_boundary R w
    (pp_t_flip_at_world R v)"
proof -
  have flip: "Elem (pp_t_flip_at_world R v) (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have not_equivalent:
      "\<not> pp_t_eqv Prop w R (pp_t_flip_at_world R v)"
  proof
    assume equivalent:
        "pp_t_eqv Prop w R (pp_t_flip_at_world R v)"
    have at_v:
        "pp_t_holds R v
          \<longleftrightarrow>
         pp_t_holds (pp_t_flip_at_world R v) v"
      by (rule pp_t_prop_eqv_at[OF equivalent wv])
    show False
      using at_v pp_t_flip_at_world_differs[of R v]
      by blast
  qed
  have recovered_reverse:
      "pp_t_eqv Prop (v @ [True])
        (pp_t_flip_at_world R v) R"
    by (rule pp_t_flip_at_world_recovers_on_child[OF R])
  have recovered:
      "pp_t_eqv Prop (v @ [True])
        R (pp_t_flip_at_world R v)"
    by (rule pp_t_eqv_symmetric[
      OF flip R recovered_reverse])
  have future: "prefix w (v @ [True])"
    using wv by simp
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
    using flip not_equivalent future recovered by blast
qed

lemma pp_t_two_future_flips_are_distinct_at_root:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv Prop []
    (pp_t_flip_at_world R [])
    (pp_t_flip_at_world R [True])"
proof
  assume equivalent:
      "pp_t_eqv Prop []
        (pp_t_flip_at_world R [])
        (pp_t_flip_at_world R [True])"
  have at_root:
      "pp_t_holds (pp_t_flip_at_world R []) []
        \<longleftrightarrow>
       pp_t_holds (pp_t_flip_at_world R [True]) []"
    by (rule pp_t_prop_eqv_at[OF equivalent], simp)
  show False
    using at_root
    by (simp add: pp_t_flip_at_world_def)
qed

section \<open>The boundary probe at identity\<close>

definition pp_t_cone_lift_boundary_identity_probe :: "ZF \<Rightarrow> ZF"
where
  "pp_t_cone_lift_boundary_identity_probe R =
    pp_t_moving_boundary_operator_probe
      (\<lambda>w. pp_t_cone_lift w R)
      \<acute> pp_t_closed_den prop_id"

lemma pp_t_cone_lift_boundary_identity_probe_in_domain:
  "Elem (pp_t_cone_lift_boundary_identity_probe R)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_cone_lift_boundary_identity_probe_def
  by (rule pp_t_app_closed[
    OF pp_t_moving_boundary_operator_probe_in_domain])
    (rule pp_t_closed_den_in_domain, rule typed_prop_id)

lemma pp_t_cone_lift_boundary_identity_probe_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> p) w
      \<longleftrightarrow>
    pp_t_fundamental_boundary (pp_t_cone_lift w R) w p"
proof -
  have identity:
      "Elem (pp_t_closed_den prop_id)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule typed_prop_id)
  have probe:
      "pp_t_holds
        (pp_t_cone_lift_boundary_identity_probe R \<acute> p) w
        \<longleftrightarrow>
      pp_t_fundamental_boundary (pp_t_cone_lift w R) w
        (pp_t_closed_den prop_id \<acute> p)"
    unfolding pp_t_cone_lift_boundary_identity_probe_def
    by (rule pp_t_moving_boundary_operator_probe_apply_holds[
      OF pp_t_cone_lift_in_domain identity p])
  show ?thesis
    using probe
    unfolding pp_t_closed_identity_apply[OF p]
    by simp
qed

lemma pp_t_cone_lift_boundary_identity_probe_two_true_points:
  assumes R: "Elem R (pp_t_domain Prop)"
  defines "A \<equiv> pp_t_cone_lift [] R"
    and "p \<equiv> pp_t_flip_at_world (pp_t_cone_lift [] R) []"
    and "q \<equiv> pp_t_flip_at_world (pp_t_cone_lift [] R) [True]"
  shows
    "Elem p (pp_t_domain Prop)"
    "Elem q (pp_t_domain Prop)"
    "\<not> pp_t_eqv Prop [] p q"
    "pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> p) []"
    "pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> q) []"
proof -
  have A: "Elem A (pp_t_domain Prop)"
    unfolding A_def by (rule pp_t_cone_lift_in_domain)
  show p: "Elem p (pp_t_domain Prop)"
    unfolding p_def by (rule pp_t_flip_at_world_in_domain)
  show q: "Elem q (pp_t_domain Prop)"
    unfolding q_def by (rule pp_t_flip_at_world_in_domain)
  show "\<not> pp_t_eqv Prop [] p q"
    unfolding p_def q_def
    by (rule pp_t_two_future_flips_are_distinct_at_root)
      (rule pp_t_cone_lift_in_domain)
  have p_boundary: "pp_t_fundamental_boundary A [] p"
    unfolding p_def A_def
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF pp_t_cone_lift_in_domain])
      simp
  have q_boundary: "pp_t_fundamental_boundary A [] q"
    unfolding q_def A_def
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF pp_t_cone_lift_in_domain])
      simp
  show "pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> p) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF p, of R "[]"]
      p_boundary
    unfolding A_def by blast
  show "pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> q) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF q, of R "[]"]
      q_boundary
    unfolding A_def by blast
qed

lemma pp_t_cone_lift_boundary_identity_probe_two_false_points:
  assumes R: "Elem R (pp_t_domain Prop)"
  defines "A \<equiv> pp_t_cone_lift [] R"
    and "p \<equiv> pp_t_cone_lift [] R"
    and "q \<equiv> pp_t_complement (pp_t_cone_lift [] R)"
  shows
    "Elem p (pp_t_domain Prop)"
    "Elem q (pp_t_domain Prop)"
    "\<not> pp_t_eqv Prop [] p q"
    "\<not> pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> p) []"
    "\<not> pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> q) []"
proof -
  have A: "Elem A (pp_t_domain Prop)"
    unfolding A_def by (rule pp_t_cone_lift_in_domain)
  show p: "Elem p (pp_t_domain Prop)"
    unfolding p_def by (rule pp_t_cone_lift_in_domain)
  show q: "Elem q (pp_t_domain Prop)"
    unfolding q_def
    by (rule pp_t_complement_in_domain)
  show "\<not> pp_t_eqv Prop [] p q"
    unfolding p_def q_def
    by (rule pp_t_proposition_never_equivalent_to_its_complement)
      (rule pp_t_cone_lift_in_domain)
  have not_p_boundary: "\<not> pp_t_fundamental_boundary A [] p"
  proof -
    have reflexive:
        "pp_t_eqv Prop []
          (pp_t_cone_lift [] R) (pp_t_cone_lift [] R)"
      by (rule pp_t_eqv_reflexive)
        (rule pp_t_cone_lift_in_domain)
    show ?thesis
      unfolding pp_t_fundamental_boundary_def p_def A_def
      using reflexive by blast
  qed
  have not_q_boundary: "\<not> pp_t_fundamental_boundary A [] q"
  proof
    assume boundary: "pp_t_fundamental_boundary A [] q"
    obtain v where "pp_t_eqv Prop v A q"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    moreover have
        "\<not> pp_t_eqv Prop v
          (pp_t_cone_lift [] R)
          (pp_t_complement (pp_t_cone_lift [] R))"
      by (rule pp_t_proposition_never_equivalent_to_its_complement)
        (rule pp_t_cone_lift_in_domain)
    ultimately show False
      unfolding q_def A_def by blast
  qed
  show "\<not> pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> p) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF p, of R "[]"]
      not_p_boundary
    unfolding A_def by blast
  show "\<not> pp_t_holds
      (pp_t_cone_lift_boundary_identity_probe R \<acute> q) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF q, of R "[]"]
      not_q_boundary
    unfolding A_def by blast
qed

lemma pp_t_equivalent_unary_operators_agree_at_argument:
  assumes XY:
      "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (X \<acute> p) w
      \<longleftrightarrow>
     pp_t_holds (Y \<acute> p) w"
proof -
  have pp: "pp_t_eqv Prop w p p"
    by (rule pp_t_eqv_reflexive[OF p])
  have applications:
      "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
    by (rule pp_t_app_respects[OF XY p p pp])
  show ?thesis
    by (rule pp_t_prop_eqv_at[OF applications], simp)
qed

lemma pp_t_boundary_identity_probe_not_singleton:
  assumes R: "Elem R (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv pp_t_one_context_unary_type []
      (pp_t_cone_lift_boundary_identity_probe R)
      (pp_t_singleton_family_at r)"
proof
  let ?A = "pp_t_cone_lift [] R"
  let ?p = "pp_t_flip_at_world ?A []"
  let ?q = "pp_t_flip_at_world ?A [True]"
  let ?P = "pp_t_cone_lift_boundary_identity_probe R"
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type []
        ?P (pp_t_singleton_family_at r)"
  have A: "Elem ?A (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have p_boundary: "pp_t_fundamental_boundary ?A [] ?p"
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF A])
      simp
  have q_boundary: "pp_t_fundamental_boundary ?A [] ?q"
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF A])
      simp
  have Pp: "pp_t_holds (?P \<acute> ?p) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF p, of R "[]"]
      p_boundary by blast
  have Pq: "pp_t_holds (?P \<acute> ?q) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF q, of R "[]"]
      q_boundary by blast
  have Sp: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?p) []"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent p]
      Pp by blast
  have Sq: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?q) []"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent q]
      Pq by blast
  have pr: "pp_t_eqv Prop [] ?p r"
    using pp_t_singleton_family_at_apply_holds[OF r p, of "[]"]
      Sp by blast
  have qr: "pp_t_eqv Prop [] ?q r"
    using pp_t_singleton_family_at_apply_holds[OF r q, of "[]"]
      Sq by blast
  have rq: "pp_t_eqv Prop [] r ?q"
    by (rule pp_t_eqv_symmetric[OF q r qr])
  have pq: "pp_t_eqv Prop [] ?p ?q"
    by (rule pp_t_eqv_transitive[OF p r q pr rq])
  show False
    using pp_t_two_future_flips_are_distinct_at_root[OF A]
      pq by blast
qed

lemma pp_t_boundary_identity_probe_not_complemented_singleton:
  assumes R: "Elem R (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv pp_t_one_context_unary_type []
      (pp_t_cone_lift_boundary_identity_probe R)
      (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
proof
  let ?A = "pp_t_cone_lift [] R"
  let ?q = "pp_t_complement ?A"
  let ?P = "pp_t_cone_lift_boundary_identity_probe R"
  let ?N =
    "pp_t_pointwise_complement (pp_t_singleton_family_at r)"
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type [] ?P ?N"
  have A: "Elem ?A (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have not_A_boundary:
      "\<not> pp_t_fundamental_boundary ?A [] ?A"
    unfolding pp_t_fundamental_boundary_def
    using pp_t_eqv_reflexive[OF A, of "[]"] by blast
  have not_q_boundary:
      "\<not> pp_t_fundamental_boundary ?A [] ?q"
  proof
    assume boundary: "pp_t_fundamental_boundary ?A [] ?q"
    obtain v where "pp_t_eqv Prop v ?A ?q"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    then show False
      using pp_t_proposition_never_equivalent_to_its_complement[
        OF A, of v]
      by blast
  qed
  have not_PA: "\<not> pp_t_holds (?P \<acute> ?A) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF A, of R "[]"]
      not_A_boundary by blast
  have not_Pq: "\<not> pp_t_holds (?P \<acute> ?q) []"
    using pp_t_cone_lift_boundary_identity_probe_holds[
      OF q, of R "[]"]
      not_q_boundary by blast
  have not_NA: "\<not> pp_t_holds (?N \<acute> ?A) []"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent A]
      not_PA by blast
  have not_Nq: "\<not> pp_t_holds (?N \<acute> ?q) []"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent q]
      not_Pq by blast
  have SA: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?A) []"
    using pp_t_pointwise_complement_holds[
      OF A, of "pp_t_singleton_family_at r" "[]"]
      not_NA by simp
  have Sq: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?q) []"
    using pp_t_pointwise_complement_holds[
      OF q, of "pp_t_singleton_family_at r" "[]"]
      not_Nq by simp
  have Ar: "pp_t_eqv Prop [] ?A r"
    using pp_t_singleton_family_at_apply_holds[OF r A, of "[]"]
      SA by blast
  have qr: "pp_t_eqv Prop [] ?q r"
    using pp_t_singleton_family_at_apply_holds[OF r q, of "[]"]
      Sq by blast
  have rq: "pp_t_eqv Prop [] r ?q"
    by (rule pp_t_eqv_symmetric[OF q r qr])
  have Aq: "pp_t_eqv Prop [] ?A ?q"
    by (rule pp_t_eqv_transitive[OF A r q Ar rq])
  show False
    using pp_t_proposition_never_equivalent_to_its_complement[
      OF A, of "[]"]
      Aq by blast
qed

theorem pp_t_boundary_identity_probe_not_absorbed:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows
    "\<not> pp_t_boundary_singleton_stock
      (pp_t_cone_lift [] R) []
      (pp_t_cone_lift_boundary_identity_probe R)"
proof
  assume stock:
      "pp_t_boundary_singleton_stock
        (pp_t_cone_lift [] R) []
        (pp_t_cone_lift_boundary_identity_probe R)"
  obtain r where boundary:
      "pp_t_fundamental_boundary (pp_t_cone_lift [] R) [] r"
    and representation:
      "pp_t_eqv pp_t_one_context_unary_type []
          (pp_t_cone_lift_boundary_identity_probe R)
          (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type []
          (pp_t_cone_lift_boundary_identity_probe R)
          (pp_t_pointwise_complement
            (pp_t_singleton_family_at r))"
    using stock
    unfolding pp_t_boundary_singleton_stock_def
    by blast
  have r: "Elem r (pp_t_domain Prop)"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  show False
    using pp_t_boundary_identity_probe_not_singleton[OF R r]
      pp_t_boundary_identity_probe_not_complemented_singleton[OF R r]
      representation by blast
qed

end
