theory Bacon_PP_ZF_Tree_Recurrent_Probe_Stabilization
  imports
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Stock.Bacon_PP_ZF_Tree_Recurrent_Probe_Stock
begin

section \<open>The moving boundary probe is never a singleton family\<close>

lemma pp_t_two_future_flips_are_distinct:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv Prop w
    (pp_t_flip_at_world R w)
    (pp_t_flip_at_world R (w @ [True]))"
proof
  assume equivalent:
      "pp_t_eqv Prop w
        (pp_t_flip_at_world R w)
        (pp_t_flip_at_world R (w @ [True]))"
  have at_w:
      "pp_t_holds (pp_t_flip_at_world R w) w
        \<longleftrightarrow>
       pp_t_holds (pp_t_flip_at_world R (w @ [True])) w"
    by (rule pp_t_prop_eqv_at[OF equivalent], simp)
  show False
    using at_w
    by (simp add: pp_t_flip_at_world_def)
qed

lemma pp_t_moving_boundary_identity_probe_not_singleton:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_moving_boundary_identity_probe R)
      (pp_t_singleton_family_at r)"
proof
  let ?A = "R w"
  let ?p = "pp_t_flip_at_world ?A w"
  let ?q = "pp_t_flip_at_world ?A (w @ [True])"
  let ?P = "pp_t_moving_boundary_identity_probe R"
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type w
        ?P (pp_t_singleton_family_at r)"
  have A: "Elem ?A (pp_t_domain Prop)"
    by (rule R)
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have p_boundary: "pp_t_fundamental_boundary ?A w ?p"
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF A])
      simp
  have q_boundary: "pp_t_fundamental_boundary ?A w ?q"
    by (rule pp_t_future_world_flip_is_on_fundamental_boundary[
      OF A])
      simp
  have Pp: "pp_t_holds (?P \<acute> ?p) w"
    using pp_t_moving_boundary_identity_probe_holds[
      where R=R and w=w and p="?p", OF A p]
      p_boundary by blast
  have Pq: "pp_t_holds (?P \<acute> ?q) w"
    using pp_t_moving_boundary_identity_probe_holds[
      where R=R and w=w and p="?q", OF A q]
      q_boundary by blast
  have Sp:
      "pp_t_holds (pp_t_singleton_family_at r \<acute> ?p) w"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent p]
      Pp by blast
  have Sq:
      "pp_t_holds (pp_t_singleton_family_at r \<acute> ?q) w"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent q]
      Pq by blast
  have pr: "pp_t_eqv Prop w ?p r"
    using pp_t_singleton_family_at_apply_holds[OF r p, of w]
      Sp by blast
  have qr: "pp_t_eqv Prop w ?q r"
    using pp_t_singleton_family_at_apply_holds[OF r q, of w]
      Sq by blast
  have rq: "pp_t_eqv Prop w r ?q"
    by (rule pp_t_eqv_symmetric[OF q r qr])
  have pq: "pp_t_eqv Prop w ?p ?q"
    by (rule pp_t_eqv_transitive[OF p r q pr rq])
  show False
    using pp_t_two_future_flips_are_distinct[OF A, of w]
      pq by blast
qed

lemma pp_t_moving_boundary_identity_probe_not_complemented_singleton:
  assumes R: "\<And>v. Elem (R v) (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "\<not> pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_moving_boundary_identity_probe R)
      (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
proof
  let ?A = "R w"
  let ?q = "pp_t_complement ?A"
  let ?P = "pp_t_moving_boundary_identity_probe R"
  let ?N =
    "pp_t_pointwise_complement (pp_t_singleton_family_at r)"
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type w ?P ?N"
  have A: "Elem ?A (pp_t_domain Prop)"
    by (rule R)
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have not_A_boundary:
      "\<not> pp_t_fundamental_boundary ?A w ?A"
    unfolding pp_t_fundamental_boundary_def
    using pp_t_eqv_reflexive[OF A, of w] by blast
  have not_q_boundary:
      "\<not> pp_t_fundamental_boundary ?A w ?q"
  proof
    assume boundary: "pp_t_fundamental_boundary ?A w ?q"
    obtain v where "pp_t_eqv Prop v ?A ?q"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    then show False
      using pp_t_proposition_never_equivalent_to_its_complement[
        OF A, of v]
      by blast
  qed
  have not_PA: "\<not> pp_t_holds (?P \<acute> ?A) w"
    using pp_t_moving_boundary_identity_probe_holds[
      where R=R and w=w and p="?A", OF A A]
      not_A_boundary by blast
  have not_Pq: "\<not> pp_t_holds (?P \<acute> ?q) w"
    using pp_t_moving_boundary_identity_probe_holds[
      where R=R and w=w and p="?q", OF A q]
      not_q_boundary by blast
  have not_NA: "\<not> pp_t_holds (?N \<acute> ?A) w"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent A]
      not_PA by blast
  have not_Nq: "\<not> pp_t_holds (?N \<acute> ?q) w"
    using pp_t_equivalent_unary_operators_agree_at_argument[
      OF equivalent q]
      not_Pq by blast
  have SA: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?A) w"
    using pp_t_pointwise_complement_holds[
      OF A, of "pp_t_singleton_family_at r" w]
      not_NA by simp
  have Sq: "pp_t_holds (pp_t_singleton_family_at r \<acute> ?q) w"
    using pp_t_pointwise_complement_holds[
      OF q, of "pp_t_singleton_family_at r" w]
      not_Nq by simp
  have Ar: "pp_t_eqv Prop w ?A r"
    using pp_t_singleton_family_at_apply_holds[OF r A, of w]
      SA by blast
  have qr: "pp_t_eqv Prop w ?q r"
    using pp_t_singleton_family_at_apply_holds[OF r q, of w]
      Sq by blast
  have rq: "pp_t_eqv Prop w r ?q"
    by (rule pp_t_eqv_symmetric[OF q r qr])
  have Aq: "pp_t_eqv Prop w ?A ?q"
    by (rule pp_t_eqv_transitive[OF A r q Ar rq])
  show False
    using pp_t_proposition_never_equivalent_to_its_complement[
      OF A, of w]
      Aq by blast
qed

section \<open>One-step stabilization on singleton-family queries\<close>

lemma pp_t_recurrent_probe_not_singleton:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    pp_t_recurrent_boundary_probe
    (pp_t_singleton_family_at p)"
  by (rule pp_t_moving_boundary_identity_probe_not_singleton[
    where R=pp_t_probe_modal_boolean_recurrent_seed_at,
    OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain p])

lemma pp_t_recurrent_probe_not_complemented_singleton:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    pp_t_recurrent_boundary_probe
    (pp_t_pointwise_complement (pp_t_singleton_family_at p))"
  by (rule
    pp_t_moving_boundary_identity_probe_not_complemented_singleton[
      where R=pp_t_probe_modal_boolean_recurrent_seed_at,
      OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain p])

lemma pp_t_singleton_not_equivalent_to_recurrent_probe:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_singleton_family_at p)
    pp_t_recurrent_boundary_probe"
proof
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        pp_t_recurrent_boundary_probe"
  have reverse:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_recurrent_boundary_probe
        (pp_t_singleton_family_at p)"
    by (rule pp_t_eqv_symmetric[
      OF pp_t_singleton_family_at_in_domain[OF p]
        pp_t_recurrent_boundary_probe_in_domain equivalent])
  show False
    using pp_t_recurrent_probe_not_singleton[OF p] reverse
    by blast
qed

lemma pp_t_singleton_not_equivalent_to_complemented_recurrent_probe:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_singleton_family_at p)
    pp_t_recurrent_complemented_boundary_probe"
proof
  let ?S = "pp_t_singleton_family_at p"
  assume equivalent:
      "pp_t_eqv pp_t_one_context_unary_type w
        ?S pp_t_recurrent_complemented_boundary_probe"
  have S: "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  have complements:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_pointwise_complement ?S)
        (pp_t_pointwise_complement
          pp_t_recurrent_complemented_boundary_probe)"
    by (rule pp_t_pointwise_complement_respects_equivalence[
      OF S pp_t_recurrent_complemented_boundary_probe_in_domain
        equivalent])
  have involution:
      "pp_t_pointwise_complement
          pp_t_recurrent_complemented_boundary_probe
        =
       pp_t_recurrent_boundary_probe"
    by (rule pp_t_pointwise_complement_involution[
      OF pp_t_recurrent_boundary_probe_in_domain])
  have complements':
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_pointwise_complement ?S)
        pp_t_recurrent_boundary_probe"
    using complements
    unfolding involution .
  have reverse:
      "pp_t_eqv pp_t_one_context_unary_type w
        pp_t_recurrent_boundary_probe
        (pp_t_pointwise_complement ?S)"
    by (rule pp_t_eqv_symmetric[
      OF pp_t_pointwise_complement_in_domain[OF S]
        pp_t_recurrent_boundary_probe_in_domain complements'])
  show False
    using pp_t_recurrent_probe_not_complemented_singleton[OF p]
      reverse by blast
qed

theorem pp_t_recurrent_probe_stock_singleton_stabilizes:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_recurrent_probe_stock w (pp_t_singleton_family_at p)
      \<longleftrightarrow>
     pp_t_recurrent_modal_boundary_stock w
       (pp_t_singleton_family_at p)"
proof -
  have S:
      "Elem (pp_t_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  show ?thesis
    using S pp_t_singleton_not_equivalent_to_recurrent_probe[OF p]
      pp_t_singleton_not_equivalent_to_complemented_recurrent_probe[OF p]
    unfolding pp_t_recurrent_probe_stock_def
    by blast
qed

corollary pp_t_recurrent_probe_stock_singleton_exact:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_recurrent_probe_stock w (pp_t_singleton_family_at p)
      \<longleftrightarrow>
     pp_t_probe_modal_boolean_stock w (pp_t_singleton_family_at p)
      \<or>
     pp_t_fundamental_boundary
       (pp_t_probe_modal_boolean_recurrent_seed_at w) w p"
proof -
  have boundary:
      "pp_t_moving_boundary_singleton_stock
          pp_t_probe_modal_boolean_recurrent_seed_at w
          (pp_t_singleton_family_at p)
        \<longleftrightarrow>
       pp_t_fundamental_boundary
          (pp_t_probe_modal_boolean_recurrent_seed_at w) w p"
    unfolding pp_t_moving_boundary_singleton_stock_def
    by (rule pp_t_singleton_family_in_boundary_stock_iff[
      OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain p])
  show ?thesis
    using pp_t_recurrent_probe_stock_singleton_stabilizes[OF p]
      boundary
    unfolding pp_t_recurrent_modal_boundary_stock_def
    by blast
qed

section \<open>The object-language operator-indexed probe is stabilized\<close>

definition pp_t_recurrent_modal_boundary_operator_probe :: ZF
where
  "pp_t_recurrent_modal_boundary_operator_probe =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      pp_t_recurrent_modal_boundary_stock
      pp_t_operator_indexed_singleton_family_builder"

definition pp_t_recurrent_probe_operator_probe :: ZF
where
  "pp_t_recurrent_probe_operator_probe =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      pp_t_recurrent_probe_stock
      pp_t_operator_indexed_singleton_family_builder"

lemma pp_t_recurrent_modal_boundary_operator_probe_in_domain:
  "Elem pp_t_recurrent_modal_boundary_operator_probe
    (pp_t_domain
      (pp_t_one_context_unary_type
        \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_recurrent_modal_boundary_operator_probe_def
  by (rule pp_t_indexed_family_probe_for_stock_in_domain[
    OF pp_t_operator_indexed_singleton_terms_typed(1)
      pp_t_recurrent_modal_boundary_stock_admissible])

lemma pp_t_recurrent_probe_operator_probe_in_domain:
  "Elem pp_t_recurrent_probe_operator_probe
    (pp_t_domain
      (pp_t_one_context_unary_type
        \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_recurrent_probe_operator_probe_def
  by (rule pp_t_indexed_family_probe_for_stock_in_domain[
    OF pp_t_operator_indexed_singleton_terms_typed(1)
      pp_t_recurrent_probe_stock_admissible])

theorem pp_t_recurrent_probe_operator_probe_apply_holds:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p) w
      \<longleftrightarrow>
     pp_t_recurrent_probe_stock w
       (pp_t_singleton_family_at (F \<acute> p))"
proof -
  have probe:
      "pp_t_holds
        ((pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p) w
        \<longleftrightarrow>
       pp_t_recurrent_probe_stock w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    unfolding pp_t_recurrent_probe_operator_probe_def
    by (rule pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_recurrent_probe_stock_admissible F p])
  show ?thesis
    using probe
    unfolding pp_t_operator_indexed_singleton_family_value[OF F p]
    by blast
qed

theorem pp_t_recurrent_modal_boundary_operator_probe_apply_holds:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p) w
      \<longleftrightarrow>
     pp_t_recurrent_modal_boundary_stock w
       (pp_t_singleton_family_at (F \<acute> p))"
proof -
  have probe:
      "pp_t_holds
        ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p) w
        \<longleftrightarrow>
       pp_t_recurrent_modal_boundary_stock w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    unfolding pp_t_recurrent_modal_boundary_operator_probe_def
    by (rule pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_recurrent_modal_boundary_stock_admissible F p])
  show ?thesis
    using probe
    unfolding pp_t_operator_indexed_singleton_family_value[OF F p]
    by blast
qed

theorem pp_t_recurrent_operator_probe_stabilizes:
  "pp_t_recurrent_probe_operator_probe
    =
   pp_t_recurrent_modal_boundary_operator_probe"
proof (rule pp_t_indexed_unary_function_ext)
  show "Elem pp_t_recurrent_probe_operator_probe
      (pp_t_domain
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    by (rule pp_t_recurrent_probe_operator_probe_in_domain)
  show "Elem pp_t_recurrent_modal_boundary_operator_probe
      (pp_t_domain
        (pp_t_one_context_unary_type
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    by (rule pp_t_recurrent_modal_boundary_operator_probe_in_domain)
  fix F
  assume F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  show "pp_t_recurrent_probe_operator_probe \<acute> F
      =
    pp_t_recurrent_modal_boundary_operator_probe \<acute> F"
  proof (rule pp_t_unary_function_ext)
    show "Elem (pp_t_recurrent_probe_operator_probe \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_recurrent_probe_operator_probe_in_domain F])
    show "Elem
        (pp_t_recurrent_modal_boundary_operator_probe \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_recurrent_modal_boundary_operator_probe_in_domain F])
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "(pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p
        =
      (pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          ((pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_recurrent_probe_operator_probe_in_domain F] p])
      show "Elem
          ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p)
          (pp_t_domain Prop)"
        by (rule pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_recurrent_modal_boundary_operator_probe_in_domain F] p])
      fix w
      have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
        by (rule pp_t_app_closed[OF F p])
      have left:
          "pp_t_holds
              ((pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p) w
            \<longleftrightarrow>
           pp_t_recurrent_probe_stock w
             (pp_t_singleton_family_at (F \<acute> p))"
        by (rule
          pp_t_recurrent_probe_operator_probe_apply_holds[OF F p])
      have right:
          "pp_t_holds
              ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F)
                \<acute> p) w
            \<longleftrightarrow>
           pp_t_recurrent_modal_boundary_stock w
             (pp_t_singleton_family_at (F \<acute> p))"
        by (rule
          pp_t_recurrent_modal_boundary_operator_probe_apply_holds[OF F p])
      show "pp_t_holds
          ((pp_t_recurrent_probe_operator_probe \<acute> F) \<acute> p) w
        =
        pp_t_holds
          ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p)
          w"
        using left right
          pp_t_recurrent_probe_stock_singleton_stabilizes[OF Fp]
        by blast
    qed
  qed
qed

section \<open>The exact outstanding application-closure range\<close>

definition pp_t_modal_singleton_operator_probe :: ZF
where
  "pp_t_modal_singleton_operator_probe =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      pp_t_probe_modal_boolean_stock
      pp_t_operator_indexed_singleton_family_builder"

lemma pp_t_modal_singleton_operator_probe_in_domain:
  "Elem pp_t_modal_singleton_operator_probe
    (pp_t_domain
      (pp_t_one_context_unary_type
        \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_modal_singleton_operator_probe_def
  by (rule pp_t_indexed_family_probe_for_stock_in_domain[
    OF pp_t_operator_indexed_singleton_terms_typed(1)
      pp_t_probe_modal_boolean_stock_admissible])

theorem pp_t_modal_singleton_operator_probe_apply_holds:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      ((pp_t_modal_singleton_operator_probe \<acute> F) \<acute> p) w
      \<longleftrightarrow>
     pp_t_probe_modal_boolean_stock w
       (pp_t_singleton_family_at (F \<acute> p))"
proof -
  have probe:
      "pp_t_holds
        ((pp_t_modal_singleton_operator_probe \<acute> F) \<acute> p) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        ((pp_t_closed_den
            pp_t_operator_indexed_singleton_family_builder \<acute> F)
          \<acute> p)"
    unfolding pp_t_modal_singleton_operator_probe_def
    by (rule pp_t_indexed_family_probe_for_stock_apply_holds[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_probe_modal_boolean_stock_admissible F p])
  show ?thesis
    using probe
    unfolding pp_t_operator_indexed_singleton_family_value[OF F p]
    by blast
qed

theorem pp_t_recurrent_modal_boundary_probe_decomposition:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_recurrent_modal_boundary_operator_probe \<acute> F
      =
     pp_t_unary_output_disjunction
       (pp_t_modal_singleton_operator_probe \<acute> F)
       (pp_t_moving_boundary_operator_probe
          pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)"
proof (rule pp_t_unary_function_ext)
  have modal:
      "Elem (pp_t_modal_singleton_operator_probe \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_modal_singleton_operator_probe_in_domain F])
  have boundary:
      "Elem
        (pp_t_moving_boundary_operator_probe
            pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  show "Elem
      (pp_t_recurrent_modal_boundary_operator_probe \<acute> F)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_recurrent_modal_boundary_operator_probe_in_domain F])
  show "Elem
      (pp_t_unary_output_disjunction
        (pp_t_modal_singleton_operator_probe \<acute> F)
        (pp_t_moving_boundary_operator_probe
          pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_unary_output_disjunction_in_domain[
      OF modal boundary])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "(pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p
      =
    pp_t_unary_output_disjunction
      (pp_t_modal_singleton_operator_probe \<acute> F)
      (pp_t_moving_boundary_operator_probe
        pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F) \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_app_closed[
          OF pp_t_recurrent_modal_boundary_operator_probe_in_domain F] p])
    show "Elem
        (pp_t_unary_output_disjunction
          (pp_t_modal_singleton_operator_probe \<acute> F)
          (pp_t_moving_boundary_operator_probe
            pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F) \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_unary_output_disjunction_in_domain[
          OF modal boundary] p])
    fix w
    have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
      by (rule pp_t_app_closed[OF F p])
    have combined:
        "pp_t_holds
            ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F)
              \<acute> p) w
          \<longleftrightarrow>
         pp_t_probe_modal_boolean_stock w
            (pp_t_singleton_family_at (F \<acute> p))
          \<or>
         pp_t_fundamental_boundary
            (pp_t_probe_modal_boolean_recurrent_seed_at w) w
            (F \<acute> p)"
      using pp_t_recurrent_modal_boundary_operator_probe_apply_holds[
        OF F p, of w]
      unfolding pp_t_recurrent_modal_boundary_stock_def
        pp_t_moving_boundary_singleton_stock_def
      using pp_t_singleton_family_in_boundary_stock_iff[
        OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain Fp,
        of w]
      by blast
    have modal_holds:
        "pp_t_holds
            ((pp_t_modal_singleton_operator_probe \<acute> F) \<acute> p) w
          \<longleftrightarrow>
         pp_t_probe_modal_boolean_stock w
            (pp_t_singleton_family_at (F \<acute> p))"
      by (rule pp_t_modal_singleton_operator_probe_apply_holds[OF F p])
    have boundary_holds:
        "pp_t_holds
            ((pp_t_moving_boundary_operator_probe
                pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)
              \<acute> p) w
          \<longleftrightarrow>
         pp_t_fundamental_boundary
            (pp_t_probe_modal_boolean_recurrent_seed_at w) w
            (F \<acute> p)"
      by (rule pp_t_moving_boundary_operator_probe_apply_holds[
        OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain F p])
    have disjunction_holds:
        "pp_t_holds
          (pp_t_unary_output_disjunction
            (pp_t_modal_singleton_operator_probe \<acute> F)
            (pp_t_moving_boundary_operator_probe
              pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)
            \<acute> p) w
          \<longleftrightarrow>
         pp_t_holds
            ((pp_t_modal_singleton_operator_probe \<acute> F) \<acute> p) w
          \<or>
         pp_t_holds
            ((pp_t_moving_boundary_operator_probe
                pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)
              \<acute> p) w"
      by (rule pp_t_unary_output_disjunction_apply_holds[
        OF modal boundary p])
    show "pp_t_holds
          ((pp_t_recurrent_modal_boundary_operator_probe \<acute> F) \<acute> p)
          w
        =
        pp_t_holds
          (pp_t_unary_output_disjunction
            (pp_t_modal_singleton_operator_probe \<acute> F)
            (pp_t_moving_boundary_operator_probe
              pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)
            \<acute> p) w"
      using combined modal_holds boundary_holds disjunction_holds
      by blast
  qed
qed

corollary pp_t_recurrent_probe_full_classifier_decomposition:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "pp_t_recurrent_probe_operator_probe \<acute> F
      =
     pp_t_unary_output_disjunction
       (pp_t_modal_singleton_operator_probe \<acute> F)
       (pp_t_moving_boundary_operator_probe
          pp_t_probe_modal_boolean_recurrent_seed_at \<acute> F)"
  unfolding pp_t_recurrent_operator_probe_stabilizes
  by (rule pp_t_recurrent_modal_boundary_probe_decomposition[OF F])

end
