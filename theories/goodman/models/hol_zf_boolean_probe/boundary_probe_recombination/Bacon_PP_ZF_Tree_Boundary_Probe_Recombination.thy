theory Bacon_PP_ZF_Tree_Boundary_Probe_Recombination
  imports
    Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Nonabsorption.Bacon_PP_ZF_Tree_Boundary_Probe_Nonabsorption
begin

section \<open>The first new boundary probe\<close>

definition pp_t_moving_boundary_identity_probe ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> ZF"
where
  "pp_t_moving_boundary_identity_probe R =
    pp_t_moving_boundary_operator_probe R
      \<acute> pp_t_closed_den prop_id"

lemma pp_t_moving_boundary_identity_probe_in_domain:
  "Elem (pp_t_moving_boundary_identity_probe R)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_moving_boundary_identity_probe_def
  by (rule pp_t_app_closed[
    OF pp_t_moving_boundary_operator_probe_in_domain])
    (rule pp_t_closed_den_in_domain, rule typed_prop_id)

lemma pp_t_moving_boundary_identity_probe_holds:
  assumes R: "Elem (R w) (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      (pp_t_moving_boundary_identity_probe R \<acute> p) w
      \<longleftrightarrow>
    pp_t_fundamental_boundary (R w) w p"
proof -
  have identity:
      "Elem (pp_t_closed_den prop_id)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_closed_den_in_domain)
      (rule typed_prop_id)
  have probe:
      "pp_t_holds
        (pp_t_moving_boundary_identity_probe R \<acute> p) w
        \<longleftrightarrow>
      pp_t_fundamental_boundary (R w) w
        (pp_t_closed_den prop_id \<acute> p)"
    unfolding pp_t_moving_boundary_identity_probe_def
    by (rule pp_t_moving_boundary_operator_probe_apply_holds[
      where R=R and w=w and F="pp_t_closed_den prop_id" and p=p,
      OF R identity p])
  show ?thesis
    using probe
    unfolding pp_t_closed_identity_apply[OF p]
    by simp
qed

definition pp_t_seed_boundary_recurrence ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_seed_boundary_recurrence R w
    \<longleftrightarrow>
    (\<exists>v. prefix w v
      \<and> pp_t_fundamental_boundary (R v) v (R w))"

definition pp_t_recombination_safe_unary_operator ::
    "ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_recombination_safe_unary_operator X r w
    \<longleftrightarrow>
    ((\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> r) v)
      \<longrightarrow>
     (\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (X \<acute> q) w))"

lemma pp_t_moving_boundary_identity_probe_recombination_safe:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_moving_boundary_identity_probe R) (R w) w"
proof -
  have not_boundary:
      "\<not> pp_t_fundamental_boundary (R w) w (R w)"
    unfolding pp_t_fundamental_boundary_def
    using pp_t_eqv_reflexive[OF R[of w], of w] by blast
  have not_at_seed:
      "\<not> pp_t_holds
        (pp_t_moving_boundary_identity_probe R \<acute> R w) w"
    using pp_t_moving_boundary_identity_probe_holds[
      where R=R and w=w and p="R w",
      OF R[of w] R[of w]]
      not_boundary by blast
  show ?thesis
    unfolding pp_t_recombination_safe_unary_operator_def
    using not_at_seed by blast
qed

theorem
  pp_t_complemented_boundary_probe_recombines_iff_seed_recurrence:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
  shows
    "pp_t_recombination_safe_unary_operator
        (pp_t_pointwise_complement
          (pp_t_moving_boundary_identity_probe R))
        (R w) w
      \<longleftrightarrow>
    pp_t_seed_boundary_recurrence R w"
proof
  let ?P = "pp_t_moving_boundary_identity_probe R"
  let ?N = "pp_t_pointwise_complement ?P"
  assume safe:
      "pp_t_recombination_safe_unary_operator ?N (R w) w"
  show "pp_t_seed_boundary_recurrence R w"
  proof (rule ccontr)
    assume no_recurrence:
        "\<not> pp_t_seed_boundary_recurrence R w"
    have no_boundary:
        "\<And>v. prefix w v
          \<Longrightarrow>
          \<not> pp_t_fundamental_boundary (R v) v (R w)"
      using no_recurrence
      unfolding pp_t_seed_boundary_recurrence_def
      by blast
    have necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (?N \<acute> R w) v"
    proof (intro allI impI)
      fix v
      assume wv: "prefix w v"
      have not_probe:
          "\<not> pp_t_holds (?P \<acute> R w) v"
        using pp_t_moving_boundary_identity_probe_holds[
          where R=R and w=v and p="R w",
          OF R[of v] R[of w]]
          no_boundary[OF wv] by blast
      show "pp_t_holds (?N \<acute> R w) v"
        using pp_t_pointwise_complement_holds[
          OF R[of w], of ?P v]
          not_probe by simp
    qed
    have universal:
        "\<forall>q. Elem q (pp_t_domain Prop)
          \<longrightarrow> pp_t_holds (?N \<acute> q) w"
      using safe necessary
      unfolding pp_t_recombination_safe_unary_operator_def
      by blast
    let ?q = "pp_t_flip_at_world (R w) w"
    have q: "Elem ?q (pp_t_domain Prop)"
      by (rule pp_t_flip_at_world_in_domain)
    have q_boundary:
        "pp_t_fundamental_boundary (R w) w ?q"
      by (rule pp_t_world_flip_is_on_fundamental_boundary[
        OF R[of w]])
    have probe_q: "pp_t_holds (?P \<acute> ?q) w"
      using pp_t_moving_boundary_identity_probe_holds[
        where R=R and w=w,
        OF R[of w] q]
        q_boundary by blast
    have complement_q: "pp_t_holds (?N \<acute> ?q) w"
      using universal q by blast
    show False
      using pp_t_pointwise_complement_holds[
        OF q, of ?P w]
        probe_q complement_q by simp
  qed
next
  let ?P = "pp_t_moving_boundary_identity_probe R"
  let ?N = "pp_t_pointwise_complement ?P"
  assume recurrence: "pp_t_seed_boundary_recurrence R w"
  show "pp_t_recombination_safe_unary_operator ?N (R w) w"
  proof (unfold pp_t_recombination_safe_unary_operator_def,
      intro impI)
    assume necessary:
        "\<forall>v. prefix w v \<longrightarrow>
          pp_t_holds (?N \<acute> R w) v"
    obtain v where wv: "prefix w v"
      and boundary:
        "pp_t_fundamental_boundary (R v) v (R w)"
      using recurrence
      unfolding pp_t_seed_boundary_recurrence_def by blast
    have probe: "pp_t_holds (?P \<acute> R w) v"
      using pp_t_moving_boundary_identity_probe_holds[
        where R=R and w=v and p="R w",
        OF R[of v] R[of w]]
        boundary by blast
    have complement: "pp_t_holds (?N \<acute> R w) v"
      using necessary wv by blast
    show "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (?N \<acute> q) w"
      using pp_t_pointwise_complement_holds[
        OF R[of w], of ?P v]
        probe complement by simp
  qed
qed

end
