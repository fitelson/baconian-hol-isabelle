theory Bacon_PP_ZF_Tree_Guarded_Collision_Invariant
  imports
    Higher_Order_Metaphysics_PP_ZF_Guarded_Indexed_Family.Bacon_PP_ZF_Tree_Guarded_Indexed_Family
begin

section \<open>Pointwise negation of a semantic unary operator\<close>

definition pp_t_pointwise_complement :: "ZF \<Rightarrow> ZF"
where
  "pp_t_pointwise_complement F =
    Lambda (pp_t_domain Prop)
      (\<lambda>q. pp_t_complement (F \<acute> q))"

lemma pp_t_pointwise_complement_in_domain:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows "Elem (pp_t_pointwise_complement F)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_pointwise_complement_def
proof (rule pp_t_lambda_closed)
  fix q
  assume "Elem q (pp_t_domain Prop)"
  show "Elem (pp_t_complement (F \<acute> q)) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
next
  fix w p q
  assume p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and pq: "pp_t_eqv Prop w p q"
  have images:
      "pp_t_eqv Prop w (F \<acute> p) (F \<acute> q)"
    by (rule pp_t_arrow_member_respects[OF F p q pq])
  show "pp_t_eqv Prop w
      (pp_t_complement (F \<acute> p))
      (pp_t_complement (F \<acute> q))"
    using images
    by auto
qed

lemma pp_t_pointwise_complement_apply:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_pointwise_complement F \<acute> q =
    pp_t_complement (F \<acute> q)"
  using q
  by (simp add: pp_t_pointwise_complement_def Lambda_app)

lemma pp_t_pointwise_complement_holds:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds (pp_t_pointwise_complement F \<acute> q) w
    \<longleftrightarrow>
    \<not> pp_t_holds (F \<acute> q) w"
  unfolding pp_t_pointwise_complement_apply[OF q]
  by simp

section \<open>What an operator-indexed singleton collision says\<close>

lemma pp_t_operator_indexed_collision_settles_parameter:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at r)"
  shows
    "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth True)
      \<or> pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth False)"
proof -
  let ?P =
    "pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder \<acute> F"
  have P: "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_indexed_family_probe_section_in_domain[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible F])
  have rr: "pp_t_eqv Prop w r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have applications:
      "pp_t_eqv Prop w (?P \<acute> r)
        (pp_t_singleton_family_at r \<acute> r)"
    by (rule pp_t_app_respects[OF collision r r rr])
  have target_true:
      "pp_t_holds (pp_t_singleton_family_at r \<acute> r) w"
    using pp_t_singleton_family_at_apply_holds[OF r r, of w]
      rr by blast
  have probe_true: "pp_t_holds (?P \<acute> r) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      target_true by simp
  show ?thesis
    using pp_t_operator_indexed_singleton_probe_apply_holds[
      OF F r, of w]
      probe_true by blast
qed

lemma pp_t_operator_indexed_collision_unsettles_world_flip:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at r)"
  shows
    "\<not> (pp_t_eqv Prop w
        (F \<acute> pp_t_flip_at_world r w) (pp_zf_truth True)
      \<or>
      pp_t_eqv Prop w
        (F \<acute> pp_t_flip_at_world r w) (pp_zf_truth False))"
proof -
  let ?q = "pp_t_flip_at_world r w"
  let ?P =
    "pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder \<acute> F"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have P: "Elem ?P (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_indexed_family_probe_section_in_domain[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible F])
  have qq: "pp_t_eqv Prop w ?q ?q"
    by (rule pp_t_eqv_reflexive[OF q])
  have applications:
      "pp_t_eqv Prop w (?P \<acute> ?q)
        (pp_t_singleton_family_at r \<acute> ?q)"
    by (rule pp_t_app_respects[OF collision q q qq])
  have target_false:
      "\<not> pp_t_holds (pp_t_singleton_family_at r \<acute> ?q) w"
    using pp_t_singleton_family_at_apply_holds[OF r q, of w]
      pp_t_flip_at_world_not_equivalent_at_world[OF r]
    by blast
  have probe_false: "\<not> pp_t_holds (?P \<acute> ?q) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      target_false by simp
  show ?thesis
    using pp_t_operator_indexed_singleton_probe_apply_holds[
      OF F q, of w]
      probe_false by blast
qed

section \<open>The temporal-evasion invariant imposed by Recombination\<close>

lemma pp_t_flip_at_world_recovers_after_every_strict_future:
  assumes r: "Elem r (pp_t_domain Prop)"
    and wv: "prefix w v"
    and strict: "v \<noteq> w"
  shows "pp_t_eqv Prop v (pp_t_flip_at_world r w) r"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix u
  assume vu: "prefix v u"
  have "u \<noteq> w"
    using wv strict vu
    by (auto simp: prefix_def)
  then show "pp_t_holds (pp_t_flip_at_world r w) u =
      pp_t_holds r u"
    by (simp add: pp_t_flip_at_world_def)
qed

lemma pp_t_recombining_collision_index_is_presently_constant:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and F_pure: "Pure w F"
    and complement_pure: "Pure w (pp_t_pointwise_complement F)"
    and recombines: "pp_t_unary_recombines_at Pure r w"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at r)"
  shows
    "(\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (F \<acute> q) w)
      \<or>
     (\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> \<not> pp_t_holds (F \<acute> q) w)"
proof -
  have settled:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth True)
        \<or> pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth False)"
    by (rule pp_t_operator_indexed_collision_settles_parameter[
      OF F r collision])
  from settled show ?thesis
  proof
    assume true_at_r:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth True)"
    have necessary:
        "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (F \<acute> r) v"
      using true_at_r pp_t_prop_eqv_truth_iff by blast
    have all:
        "\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (F \<acute> q) w"
      using recombines F F_pure necessary
      unfolding pp_t_unary_recombines_at_def
      by blast
    then show ?thesis
      by blast
  next
    assume false_at_r:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth False)"
    let ?N = "pp_t_pointwise_complement F"
    have N: "Elem ?N (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF F])
    have necessary:
        "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (?N \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have at_v:
          "pp_t_holds (F \<acute> r) v
            \<longleftrightarrow>
          pp_t_holds (pp_zf_truth False) v"
        by (rule pp_t_prop_eqv_at[OF false_at_r wv])
      show "pp_t_holds (?N \<acute> r) v"
        using pp_t_pointwise_complement_holds[OF r, of F v]
          at_v by simp
    qed
    have all_complements:
        "\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (?N \<acute> q) w"
      using recombines N complement_pure necessary
      unfolding pp_t_unary_recombines_at_def
      by blast
    have all_false:
        "\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> \<not> pp_t_holds (F \<acute> q) w"
      using all_complements pp_t_pointwise_complement_holds
      by blast
    then show ?thesis
      by blast
  qed
qed

theorem pp_t_recombining_collision_index_must_change_later:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and F_pure: "Pure w F"
    and complement_pure: "Pure w (pp_t_pointwise_complement F)"
    and recombines: "pp_t_unary_recombines_at Pure r w"
    and collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at r)"
  shows
    "(\<exists>v. prefix w v
        \<and> pp_t_holds (F \<acute> pp_t_flip_at_world r w) w
        \<and> \<not> pp_t_holds
          (F \<acute> pp_t_flip_at_world r w) v)
      \<or>
     (\<exists>v. prefix w v
        \<and> \<not> pp_t_holds
          (F \<acute> pp_t_flip_at_world r w) w
        \<and> pp_t_holds
          (F \<acute> pp_t_flip_at_world r w) v)"
proof -
  let ?q = "pp_t_flip_at_world r w"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have unsettled:
      "\<not> (pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth True)
        \<or> pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth False))"
    by (rule pp_t_operator_indexed_collision_unsettles_world_flip[
      OF F r collision])
  have uniform:
      "(\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (F \<acute> q) w)
        \<or>
       (\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> \<not> pp_t_holds (F \<acute> q) w)"
    by (rule pp_t_recombining_collision_index_is_presently_constant[
      OF F r F_pure complement_pure recombines collision])
  from uniform show ?thesis
  proof
    assume all_true:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (F \<acute> q) w"
    have now: "pp_t_holds (F \<acute> ?q) w"
      using all_true q by blast
    have not_necessary:
        "\<not> pp_t_eqv Prop w
          (F \<acute> ?q) (pp_zf_truth True)"
      using unsettled by blast
    have later:
        "\<exists>v. prefix w v \<and> \<not> pp_t_holds (F \<acute> ?q) v"
      using not_necessary pp_t_prop_eqv_truth_iff by blast
    then show ?thesis
      using now by blast
  next
    assume all_false:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> \<not> pp_t_holds (F \<acute> q) w"
    have now: "\<not> pp_t_holds (F \<acute> ?q) w"
      using all_false q by blast
    have not_necessarily_false:
        "\<not> pp_t_eqv Prop w
          (F \<acute> ?q) (pp_zf_truth False)"
      using unsettled by blast
    have later:
        "\<exists>v. prefix w v \<and> pp_t_holds (F \<acute> ?q) v"
    proof (rule ccontr)
      assume "\<not> (\<exists>v.
        prefix w v \<and> pp_t_holds (F \<acute> ?q) v)"
      then have all_false:
          "\<forall>v. prefix w v \<longrightarrow>
            \<not> pp_t_holds (F \<acute> ?q) v"
        by blast
      have necessarily_false:
          "pp_t_eqv Prop w
            (F \<acute> ?q) (pp_zf_truth False)"
        using all_false by simp
      show False
        using not_necessarily_false necessarily_false by blast
    qed
    then show ?thesis
      using now by blast
  qed
qed

theorem pp_t_recombination_excludes_every_pure_singleton_collision_index:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and r: "Elem r (pp_t_domain Prop)"
    and F_pure: "Pure w F"
    and complement_pure: "Pure w (pp_t_pointwise_complement F)"
    and recombines: "pp_t_unary_recombines_at Pure r w"
  shows
    "\<not> pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_indexed_family_probe_for_stock
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder \<acute> F)
      (pp_t_singleton_family_at r)"
proof
  let ?q = "pp_t_flip_at_world r w"
  assume collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at r)"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have unsettled:
      "\<not> (pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth True)
        \<or> pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth False))"
    by (rule pp_t_operator_indexed_collision_unsettles_world_flip[
      OF F r collision])
  have settled_r:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth True)
        \<or> pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth False)"
    by (rule pp_t_operator_indexed_collision_settles_parameter[
      OF F r collision])
  from settled_r show False
  proof
    assume true_r:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth True)"
    have necessary_r:
        "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (F \<acute> r) v"
      using true_r pp_t_prop_eqv_truth_iff by blast
    have all_now:
        "\<forall>x. Elem x (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (F \<acute> x) w"
      using recombines F F_pure necessary_r
      unfolding pp_t_unary_recombines_at_def
      by blast
    have q_now: "pp_t_holds (F \<acute> ?q) w"
      using all_now q by blast
    have q_necessary:
        "pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth True)"
      unfolding pp_t_prop_eqv_truth_iff
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      show "pp_t_holds (F \<acute> ?q) v"
      proof (cases "v = w")
        case True
        then show ?thesis
          using q_now by simp
      next
        case False
        have qr_v: "pp_t_eqv Prop v ?q r"
          by (rule
            pp_t_flip_at_world_recovers_after_every_strict_future[
              OF r wv False])
        have images:
            "pp_t_eqv Prop v (F \<acute> ?q) (F \<acute> r)"
          by (rule pp_t_arrow_member_respects[OF F q r qr_v])
        have r_true: "pp_t_holds (F \<acute> r) v"
          using necessary_r wv by blast
        show ?thesis
          using pp_t_prop_eqv_at[OF images, of v]
            r_true by simp
      qed
    qed
    show False
      using unsettled q_necessary by blast
  next
    assume false_r:
      "pp_t_eqv Prop w (F \<acute> r) (pp_zf_truth False)"
    let ?N = "pp_t_pointwise_complement F"
    have N: "Elem ?N (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF F])
    have necessary_Nr:
        "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (?N \<acute> r) v"
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have r_false:
          "\<not> pp_t_holds (F \<acute> r) v"
        using pp_t_prop_eqv_at[OF false_r wv] by simp
      show "pp_t_holds (?N \<acute> r) v"
        using pp_t_pointwise_complement_holds[OF r, of F v]
          r_false by simp
    qed
    have all_N_now:
        "\<forall>x. Elem x (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (?N \<acute> x) w"
      using recombines N complement_pure necessary_Nr
      unfolding pp_t_unary_recombines_at_def
      by blast
    have q_now: "\<not> pp_t_holds (F \<acute> ?q) w"
      using all_N_now q
        pp_t_pointwise_complement_holds[OF q, of F w]
      by blast
    have q_necessarily_false:
        "pp_t_eqv Prop w (F \<acute> ?q) (pp_zf_truth False)"
    proof -
      have all_false:
          "\<forall>v. prefix w v \<longrightarrow>
            \<not> pp_t_holds (F \<acute> ?q) v"
      proof (intro allI impI)
        fix v
        assume wv: "prefix w v"
        show "\<not> pp_t_holds (F \<acute> ?q) v"
        proof (cases "v = w")
          case True
          then show ?thesis
            using q_now by simp
        next
          case False
          have qr_v: "pp_t_eqv Prop v ?q r"
            by (rule
              pp_t_flip_at_world_recovers_after_every_strict_future[
                OF r wv False])
          have images:
              "pp_t_eqv Prop v (F \<acute> ?q) (F \<acute> r)"
            by (rule pp_t_arrow_member_respects[OF F q r qr_v])
          have r_false:
              "\<not> pp_t_holds (F \<acute> r) v"
            using pp_t_prop_eqv_at[OF false_r wv] by simp
          show ?thesis
            using pp_t_prop_eqv_at[OF images, of v]
              r_false by simp
        qed
      qed
      show ?thesis
        using all_false by simp
    qed
    show False
      using unsettled q_necessarily_false by blast
  qed
qed

section \<open>Recombination restricts which singleton families may be pure\<close>

theorem pp_t_pure_singleton_parameter_must_reach_fundamental:
  assumes R: "Elem R (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
    and singleton_pure: "Pure w (pp_t_singleton_family_at r)"
    and complement_pure:
      "Pure w
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
    and recombines: "pp_t_unary_recombines_at Pure R w"
  shows "\<exists>v. prefix w v \<and> pp_t_eqv Prop v R r"
proof (rule ccontr)
  let ?S = "pp_t_singleton_family_at r"
  let ?N = "pp_t_pointwise_complement ?S"
  assume no_recovery:
      "\<not> (\<exists>v. prefix w v \<and> pp_t_eqv Prop v R r)"
  have S: "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  have N: "Elem ?N (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF S])
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (?N \<acute> R) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have not_equivalent: "\<not> pp_t_eqv Prop v R r"
      using no_recovery wv by blast
    have singleton_false:
        "\<not> pp_t_holds (?S \<acute> R) v"
      using pp_t_singleton_family_at_apply_holds[OF r R, of v]
        not_equivalent by blast
    show "pp_t_holds (?N \<acute> R) v"
      using pp_t_pointwise_complement_holds[OF R, of ?S v]
        singleton_false by simp
  qed
  have all:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (?N \<acute> q) w"
    using recombines N complement_pure necessary
    unfolding pp_t_unary_recombines_at_def
    by blast
  have Nr: "pp_t_holds (?N \<acute> r) w"
    using all r by blast
  have Srr: "pp_t_holds (?S \<acute> r) w"
    using pp_t_singleton_family_at_apply_holds[OF r r, of w]
      pp_t_eqv_reflexive[OF r, of w]
    by blast
  show False
    using pp_t_pointwise_complement_holds[OF r, of ?S w]
      Nr Srr by simp
qed

theorem pp_t_pure_singleton_parameter_not_currently_fundamental:
  assumes R: "Elem R (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
    and singleton_pure: "Pure w (pp_t_singleton_family_at r)"
    and recombines: "pp_t_unary_recombines_at Pure R w"
  shows "\<not> pp_t_eqv Prop w R r"
proof
  let ?S = "pp_t_singleton_family_at r"
  assume equivalent: "pp_t_eqv Prop w R r"
  have S: "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (?S \<acute> R) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have equivalent_v: "pp_t_eqv Prop v R r"
      by (rule pp_t_eqv_persistent[OF equivalent wv])
    show "pp_t_holds (?S \<acute> R) v"
      using pp_t_singleton_family_at_apply_holds[OF r R, of v]
        equivalent_v by blast
  qed
  have all:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (?S \<acute> q) w"
    using recombines S singleton_pure necessary
    unfolding pp_t_unary_recombines_at_def
    by blast
  let ?q = "pp_t_complement r"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have Sq: "pp_t_holds (?S \<acute> ?q) w"
    using all q by blast
  have not_qr: "\<not> pp_t_eqv Prop w ?q r"
  proof
    assume qr: "pp_t_eqv Prop w ?q r"
    have at_w:
        "pp_t_holds ?q w \<longleftrightarrow> pp_t_holds r w"
      by (rule pp_t_prop_eqv_at[OF qr], simp)
    show False
      using at_w by simp
  qed
  show False
    using pp_t_singleton_family_at_apply_holds[OF r q, of w]
      Sq not_qr by blast
qed

corollary pp_t_pure_singleton_parameter_lies_on_fundamental_boundary:
  assumes R: "Elem R (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
    and singleton_pure: "Pure w (pp_t_singleton_family_at r)"
    and complement_pure:
      "Pure w
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
    and recombines: "pp_t_unary_recombines_at Pure R w"
  shows
    "\<not> pp_t_eqv Prop w R r
      \<and> (\<exists>v. prefix w v \<and> pp_t_eqv Prop v R r)"
  using pp_t_pure_singleton_parameter_not_currently_fundamental[
      OF R r singleton_pure recombines]
    pp_t_pure_singleton_parameter_must_reach_fundamental[
      OF R r singleton_pure complement_pure recombines]
  by blast

lemma pp_t_proposition_never_equivalent_to_its_complement:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv Prop w r (pp_t_complement r)"
proof
  assume equivalent:
      "pp_t_eqv Prop w r (pp_t_complement r)"
  have at_w:
      "pp_t_holds r w
        \<longleftrightarrow>
      pp_t_holds (pp_t_complement r) w"
    by (rule pp_t_prop_eqv_at[OF equivalent], simp)
  show False
    using at_w by simp
qed

corollary pp_t_complement_singleton_cannot_be_pure_under_recombination:
  assumes R: "Elem R (pp_t_domain Prop)"
    and singleton_pure:
      "Pure w (pp_t_singleton_family_at (pp_t_complement R))"
    and complement_pure:
      "Pure w
        (pp_t_pointwise_complement
          (pp_t_singleton_family_at (pp_t_complement R)))"
    and recombines: "pp_t_unary_recombines_at Pure R w"
  shows False
proof -
  have complement_R:
      "Elem (pp_t_complement R) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  obtain v where wv: "prefix w v"
    and equivalent:
      "pp_t_eqv Prop v R (pp_t_complement R)"
    using pp_t_pure_singleton_parameter_must_reach_fundamental[
      OF R complement_R singleton_pure complement_pure recombines]
    by blast
  show False
    using pp_t_proposition_never_equivalent_to_its_complement[
      OF R, of v]
      equivalent by blast
qed

end
