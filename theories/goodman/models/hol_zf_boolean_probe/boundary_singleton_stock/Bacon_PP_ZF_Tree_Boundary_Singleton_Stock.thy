theory Bacon_PP_ZF_Tree_Boundary_Singleton_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Guarded_Collision_Invariant.Bacon_PP_ZF_Tree_Guarded_Collision_Invariant
begin

section \<open>The moving boundary of the fundamental proposition\<close>

definition pp_t_fundamental_boundary ::
    "ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_fundamental_boundary R w r
    \<longleftrightarrow>
    Elem r (pp_t_domain Prop)
    \<and> \<not> pp_t_eqv Prop w R r
    \<and> (\<exists>v. prefix w v \<and> pp_t_eqv Prop v R r)"

definition pp_t_boundary_singleton_stock ::
    "ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_boundary_singleton_stock R w X
    \<longleftrightarrow>
    (\<exists>r.
      pp_t_fundamental_boundary R w r
      \<and>
      (pp_t_eqv pp_t_one_context_unary_type w
        X (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w
        X
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))))"

lemma pp_t_world_flip_is_on_fundamental_boundary:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows "pp_t_fundamental_boundary R w
    (pp_t_flip_at_world R w)"
proof -
  have recovered:
      "pp_t_eqv Prop (w @ [True])
        R (pp_t_flip_at_world R w)"
  proof -
    have reverse:
        "pp_t_eqv Prop (w @ [True])
          (pp_t_flip_at_world R w) R"
      by (rule pp_t_flip_at_world_recovers_on_child[OF R])
    show ?thesis
      by (rule pp_t_eqv_symmetric[
        OF pp_t_flip_at_world_in_domain R reverse])
  qed
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem (pp_t_flip_at_world R w) (pp_t_domain Prop)"
      by (rule pp_t_flip_at_world_in_domain)
    show "\<not> pp_t_eqv Prop w R (pp_t_flip_at_world R w)"
    proof
      assume equivalent:
          "pp_t_eqv Prop w R (pp_t_flip_at_world R w)"
      have reverse:
          "pp_t_eqv Prop w (pp_t_flip_at_world R w) R"
        by (rule pp_t_eqv_symmetric[
          OF R pp_t_flip_at_world_in_domain equivalent])
      show False
        using pp_t_flip_at_world_not_equivalent_at_world[OF R]
          reverse by blast
    qed
    show "\<exists>v. prefix w v
        \<and> pp_t_eqv Prop v R (pp_t_flip_at_world R w)"
    proof (rule exI[of _ "w @ [True]"], intro conjI)
      show "prefix w (w @ [True])"
        by simp
      show "pp_t_eqv Prop (w @ [True])
          R (pp_t_flip_at_world R w)"
        by (rule recovered)
    qed
  qed
qed

lemma pp_t_boundary_singleton_stock_nonempty:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows "pp_t_boundary_singleton_stock R w
    (pp_t_singleton_family_at (pp_t_flip_at_world R w))"
proof -
  have r: "Elem (pp_t_flip_at_world R w) (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have S:
      "Elem (pp_t_singleton_family_at (pp_t_flip_at_world R w))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  have reflexive:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at (pp_t_flip_at_world R w))
        (pp_t_singleton_family_at (pp_t_flip_at_world R w))"
    by (rule pp_t_eqv_reflexive[OF S])
  show ?thesis
    unfolding pp_t_boundary_singleton_stock_def
    using pp_t_world_flip_is_on_fundamental_boundary[OF R]
      reflexive by blast
qed

lemma pp_t_three_classes_leave_fresh_proposition:
  assumes p: "Elem p (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and> \<not> pp_t_eqv Prop w q p
    \<and> \<not> pp_t_eqv Prop w q r"
proof -
  let ?T = "pp_zf_truth True"
  let ?F = "pp_zf_truth False"
  let ?P = "pp_t_parity_prop"
  have T: "Elem ?T (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have F: "Elem ?F (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have P: "Elem ?P (pp_t_domain Prop)"
    by (rule pp_t_parity_prop_in_domain)
  have TF: "\<not> pp_t_eqv Prop w ?T ?F"
  proof
    assume equivalent: "pp_t_eqv Prop w ?T ?F"
    have at_w:
        "pp_t_holds ?T w \<longleftrightarrow> pp_t_holds ?F w"
      by (rule pp_t_prop_eqv_at[OF equivalent], simp)
    then show False by simp
  qed
  have FT: "\<not> pp_t_eqv Prop w ?F ?T"
  proof
    assume equivalent: "pp_t_eqv Prop w ?F ?T"
    have reverse: "pp_t_eqv Prop w ?T ?F"
      by (rule pp_t_eqv_symmetric[OF F T equivalent])
    show False using TF reverse by blast
  qed
  show ?thesis
  proof (cases "pp_t_eqv Prop w ?T p")
    case Tp: True
    have pT: "pp_t_eqv Prop w p ?T"
      by (rule pp_t_eqv_symmetric[OF T p Tp])
    have not_Fp: "\<not> pp_t_eqv Prop w ?F p"
    proof
      assume Fp: "pp_t_eqv Prop w ?F p"
      have "pp_t_eqv Prop w ?F ?T"
        by (rule pp_t_eqv_transitive[OF F p T Fp pT])
      then show False using FT by blast
    qed
    show ?thesis
    proof (cases "pp_t_eqv Prop w ?F r")
      case Fr: True
      have rF: "pp_t_eqv Prop w r ?F"
        by (rule pp_t_eqv_symmetric[OF F r Fr])
      have not_Pp: "\<not> pp_t_eqv Prop w ?P p"
      proof
        assume Pp: "pp_t_eqv Prop w ?P p"
        have "pp_t_eqv Prop w ?P ?T"
          by (rule pp_t_eqv_transitive[OF P p T Pp pT])
        then show False
          using pp_t_parity_prop_not_true by blast
      qed
      have not_Pr: "\<not> pp_t_eqv Prop w ?P r"
      proof
        assume Pr: "pp_t_eqv Prop w ?P r"
        have "pp_t_eqv Prop w ?P ?F"
          by (rule pp_t_eqv_transitive[OF P r F Pr rF])
        then show False
          using pp_t_parity_prop_not_false by blast
      qed
      show ?thesis using P not_Pp not_Pr by blast
    next
      case not_Fr: False
      show ?thesis using F not_Fp not_Fr by blast
    qed
  next
    case not_Tp: False
    show ?thesis
    proof (cases "pp_t_eqv Prop w ?T r")
      case not_Tr: False
      show ?thesis using T not_Tp not_Tr by blast
    next
      case Tr: True
      have rT: "pp_t_eqv Prop w r ?T"
        by (rule pp_t_eqv_symmetric[OF T r Tr])
      have not_Fr: "\<not> pp_t_eqv Prop w ?F r"
      proof
        assume Fr: "pp_t_eqv Prop w ?F r"
        have "pp_t_eqv Prop w ?F ?T"
          by (rule pp_t_eqv_transitive[OF F r T Fr rT])
        then show False using FT by blast
      qed
      show ?thesis
      proof (cases "pp_t_eqv Prop w ?F p")
        case not_Fp: False
        show ?thesis using F not_Fp not_Fr by blast
      next
        case Fp: True
        have pF: "pp_t_eqv Prop w p ?F"
          by (rule pp_t_eqv_symmetric[OF F p Fp])
        have not_Pp: "\<not> pp_t_eqv Prop w ?P p"
        proof
          assume Pp: "pp_t_eqv Prop w ?P p"
          have "pp_t_eqv Prop w ?P ?F"
            by (rule pp_t_eqv_transitive[OF P p F Pp pF])
          then show False
            using pp_t_parity_prop_not_false by blast
        qed
        have not_Pr: "\<not> pp_t_eqv Prop w ?P r"
        proof
          assume Pr: "pp_t_eqv Prop w ?P r"
          have "pp_t_eqv Prop w ?P ?T"
            by (rule pp_t_eqv_transitive[OF P r T Pr rT])
          then show False
            using pp_t_parity_prop_not_true by blast
        qed
        show ?thesis using P not_Pp not_Pr by blast
      qed
    qed
  qed
qed

lemma pp_t_singleton_family_equivalent_iff_parameters_equivalent:
  assumes p: "Elem p (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at r)
      \<longleftrightarrow>
    pp_t_eqv Prop w p r"
proof
  assume families:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at r)"
  have pp: "pp_t_eqv Prop w p p"
    by (rule pp_t_eqv_reflexive[OF p])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_singleton_family_at p \<acute> p)
        (pp_t_singleton_family_at r \<acute> p)"
    by (rule pp_t_app_respects[OF families p p pp])
  have left_true:
      "pp_t_holds (pp_t_singleton_family_at p \<acute> p) w"
    using pp_t_singleton_family_at_apply_holds[OF p p, of w]
      pp by blast
  have right_true:
      "pp_t_holds (pp_t_singleton_family_at r \<acute> p) w"
    using pp_t_prop_eqv_at[OF applications, of w]
      left_true by simp
  show "pp_t_eqv Prop w p r"
    using pp_t_singleton_family_at_apply_holds[OF r p, of w]
      right_true by blast
next
  assume parameters: "pp_t_eqv Prop w p r"
  have builder:
      "Elem (pp_t_closed_den pp_t_singleton_family_builder)
        (pp_t_domain
          (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    by (rule pp_t_closed_den_in_domain)
      (rule pp_t_singleton_family_builder_typed)
  show "pp_t_eqv pp_t_one_context_unary_type w
      (pp_t_singleton_family_at p)
      (pp_t_singleton_family_at r)"
    by (rule pp_t_arrow_member_respects[OF builder p r parameters])
qed

lemma pp_t_singleton_family_never_equivalent_to_complemented_singleton:
  assumes p: "Elem p (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_singleton_family_at p)
    (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
proof
  assume families:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
  obtain q where q: "Elem q (pp_t_domain Prop)"
    and not_qp: "\<not> pp_t_eqv Prop w q p"
    and not_qr: "\<not> pp_t_eqv Prop w q r"
    using pp_t_three_classes_leave_fresh_proposition[OF p r]
    by blast
  have qq: "pp_t_eqv Prop w q q"
    by (rule pp_t_eqv_reflexive[OF q])
  have applications:
      "pp_t_eqv Prop w
        (pp_t_singleton_family_at p \<acute> q)
        (pp_t_pointwise_complement
          (pp_t_singleton_family_at r) \<acute> q)"
    by (rule pp_t_app_respects[OF families q q qq])
  have left_false:
      "\<not> pp_t_holds (pp_t_singleton_family_at p \<acute> q) w"
    using pp_t_singleton_family_at_apply_holds[OF p q, of w]
      not_qp by blast
  have singleton_false:
      "\<not> pp_t_holds (pp_t_singleton_family_at r \<acute> q) w"
    using pp_t_singleton_family_at_apply_holds[OF r q, of w]
      not_qr by blast
  have right_true:
      "pp_t_holds
        (pp_t_pointwise_complement
          (pp_t_singleton_family_at r) \<acute> q) w"
    using pp_t_pointwise_complement_holds[
      OF q, of "pp_t_singleton_family_at r" w]
      singleton_false by simp
  have at_w:
      "pp_t_holds (pp_t_singleton_family_at p \<acute> q) w
        \<longleftrightarrow>
       pp_t_holds
        (pp_t_pointwise_complement
          (pp_t_singleton_family_at r) \<acute> q) w"
    by (rule pp_t_prop_eqv_at[OF applications], simp)
  show False using left_false right_true at_w by blast
qed

lemma pp_t_fundamental_boundary_respects_equivalent_parameter:
  assumes R: "Elem R (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and boundary: "pp_t_fundamental_boundary R w r"
    and pr: "pp_t_eqv Prop w p r"
  shows "pp_t_fundamental_boundary R w p"
proof -
  have r: "Elem r (pp_t_domain Prop)"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  have not_Rp: "\<not> pp_t_eqv Prop w R p"
  proof
    assume Rp: "pp_t_eqv Prop w R p"
    have Rr: "pp_t_eqv Prop w R r"
      by (rule pp_t_eqv_transitive[OF R p r Rp pr])
    show False
      using boundary Rr
      unfolding pp_t_fundamental_boundary_def by blast
  qed
  obtain v where wv: "prefix w v"
    and Rr_v: "pp_t_eqv Prop v R r"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  have pr_v: "pp_t_eqv Prop v p r"
    by (rule pp_t_eqv_persistent[OF pr wv])
  have rp_v: "pp_t_eqv Prop v r p"
    by (rule pp_t_eqv_symmetric[OF p r pr_v])
  have Rp_v: "pp_t_eqv Prop v R p"
    by (rule pp_t_eqv_transitive[OF R r p Rr_v rp_v])
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
    using p not_Rp wv Rp_v by blast
qed

theorem pp_t_singleton_family_in_boundary_stock_iff:
  assumes R: "Elem R (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_boundary_singleton_stock R w
        (pp_t_singleton_family_at p)
      \<longleftrightarrow>
    pp_t_fundamental_boundary R w p"
proof
  assume stock:
      "pp_t_boundary_singleton_stock R w
        (pp_t_singleton_family_at p)"
  obtain r where boundary: "pp_t_fundamental_boundary R w r"
    and representation:
      "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at p)
          (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at p)
          (pp_t_pointwise_complement
            (pp_t_singleton_family_at r))"
    using stock
    unfolding pp_t_boundary_singleton_stock_def
    by blast
  have r: "Elem r (pp_t_domain Prop)"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  from representation show "pp_t_fundamental_boundary R w p"
  proof
    assume families:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at p)
          (pp_t_singleton_family_at r)"
    have pr: "pp_t_eqv Prop w p r"
      using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
        OF p r, of w]
        families by blast
    show ?thesis
      by (rule pp_t_fundamental_boundary_respects_equivalent_parameter[
        OF R p boundary pr])
  next
    assume impossible:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at p)
          (pp_t_pointwise_complement
            (pp_t_singleton_family_at r))"
    show ?thesis
      using pp_t_singleton_family_never_equivalent_to_complemented_singleton[
        OF p r, of w]
        impossible by blast
  qed
next
  assume boundary: "pp_t_fundamental_boundary R w p"
  have S:
      "Elem (pp_t_singleton_family_at p)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  have reflexive:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at p)
        (pp_t_singleton_family_at p)"
    by (rule pp_t_eqv_reflexive[OF S])
  show "pp_t_boundary_singleton_stock R w
      (pp_t_singleton_family_at p)"
    unfolding pp_t_boundary_singleton_stock_def
    using boundary reflexive by blast
qed

lemma pp_t_boundary_singleton_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    (pp_t_boundary_singleton_stock R)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have XY_v: "pp_t_eqv pp_t_one_context_unary_type v X Y"
    by (rule pp_t_eqv_persistent[OF XY wv])
  have YX_v: "pp_t_eqv pp_t_one_context_unary_type v Y X"
    by (rule pp_t_eqv_symmetric[OF X Y XY_v])
  show "pp_t_boundary_singleton_stock R v X
      \<longleftrightarrow>
    pp_t_boundary_singleton_stock R v Y"
  proof
    assume X_stock: "pp_t_boundary_singleton_stock R v X"
    then obtain r where boundary:
        "pp_t_fundamental_boundary R v r"
      and representation:
        "pp_t_eqv pp_t_one_context_unary_type v
            X (pp_t_singleton_family_at r)
        \<or>
         pp_t_eqv pp_t_one_context_unary_type v
            X
            (pp_t_pointwise_complement
              (pp_t_singleton_family_at r))"
      unfolding pp_t_boundary_singleton_stock_def
      by blast
    have r: "Elem r (pp_t_domain Prop)"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have S:
        "Elem (pp_t_singleton_family_at r)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_singleton_family_at_in_domain[OF r])
    have N:
        "Elem
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF S])
    have Y_representation:
        "pp_t_eqv pp_t_one_context_unary_type v
            Y (pp_t_singleton_family_at r)
        \<or>
         pp_t_eqv pp_t_one_context_unary_type v
            Y
            (pp_t_pointwise_complement
              (pp_t_singleton_family_at r))"
    proof -
    from representation show ?thesis
    proof
      assume X_S:
        "pp_t_eqv pp_t_one_context_unary_type v
          X (pp_t_singleton_family_at r)"
      have "pp_t_eqv pp_t_one_context_unary_type v
          Y (pp_t_singleton_family_at r)"
        by (rule pp_t_eqv_transitive[OF Y X S YX_v X_S])
      then show ?thesis by blast
    next
      assume X_N:
        "pp_t_eqv pp_t_one_context_unary_type v
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
      have "pp_t_eqv pp_t_one_context_unary_type v
          Y
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
        by (rule pp_t_eqv_transitive[OF Y X N YX_v X_N])
      then show ?thesis by blast
    qed
    qed
    show "pp_t_boundary_singleton_stock R v Y"
      unfolding pp_t_boundary_singleton_stock_def
      using boundary Y_representation by blast
  next
    assume Y_stock: "pp_t_boundary_singleton_stock R v Y"
    then obtain r where boundary:
        "pp_t_fundamental_boundary R v r"
      and representation:
        "pp_t_eqv pp_t_one_context_unary_type v
            Y (pp_t_singleton_family_at r)
        \<or>
         pp_t_eqv pp_t_one_context_unary_type v
            Y
            (pp_t_pointwise_complement
              (pp_t_singleton_family_at r))"
      unfolding pp_t_boundary_singleton_stock_def
      by blast
    have r: "Elem r (pp_t_domain Prop)"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have S:
        "Elem (pp_t_singleton_family_at r)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_singleton_family_at_in_domain[OF r])
    have N:
        "Elem
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_pointwise_complement_in_domain[OF S])
    have X_representation:
        "pp_t_eqv pp_t_one_context_unary_type v
            X (pp_t_singleton_family_at r)
        \<or>
         pp_t_eqv pp_t_one_context_unary_type v
            X
            (pp_t_pointwise_complement
              (pp_t_singleton_family_at r))"
    proof -
    from representation show ?thesis
    proof
      assume Y_S:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y (pp_t_singleton_family_at r)"
      have "pp_t_eqv pp_t_one_context_unary_type v
          X (pp_t_singleton_family_at r)"
        by (rule pp_t_eqv_transitive[OF X Y S XY_v Y_S])
      then show ?thesis by blast
    next
      assume Y_N:
        "pp_t_eqv pp_t_one_context_unary_type v
          Y
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
      have "pp_t_eqv pp_t_one_context_unary_type v
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
        by (rule pp_t_eqv_transitive[OF X Y N XY_v Y_N])
      then show ?thesis by blast
    qed
    qed
    show "pp_t_boundary_singleton_stock R v X"
      unfolding pp_t_boundary_singleton_stock_def
      using boundary X_representation by blast
  qed
qed

lemma pp_t_pointwise_complement_respects_equivalence:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
  shows "pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_pointwise_complement X)
    (pp_t_pointwise_complement Y)"
  using XY
  unfolding pp_t_eqv.simps pp_t_pointwise_complement_def
  by (simp add: Lambda_app)

lemma pp_t_pointwise_complement_involution:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
  shows "pp_t_pointwise_complement (pp_t_pointwise_complement X) = X"
proof (rule pp_t_unary_function_ext)
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  show "Elem
      (pp_t_pointwise_complement (pp_t_pointwise_complement X))
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF NX])
  show "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule X)
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  show "pp_t_pointwise_complement
          (pp_t_pointwise_complement X) \<acute> q
      =
      X \<acute> q"
    unfolding pp_t_pointwise_complement_apply[OF q]
      pp_t_complement_involution[
        OF pp_t_app_closed[OF X q]]
    by simp
qed

lemma pp_t_boundary_singleton_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_boundary_singleton_stock R w X"
  shows "pp_t_boundary_singleton_stock R w
    (pp_t_pointwise_complement X)"
proof -
  obtain r where boundary: "pp_t_fundamental_boundary R w r"
    and representation:
      "pp_t_eqv pp_t_one_context_unary_type w
          X (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
    using stock
    unfolding pp_t_boundary_singleton_stock_def by blast
  have r: "Elem r (pp_t_domain Prop)"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  have S:
      "Elem (pp_t_singleton_family_at r)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  have N:
      "Elem
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF S])
  have NX:
      "Elem (pp_t_pointwise_complement X)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF X])
  have complemented_representation:
      "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
  proof -
    from representation show ?thesis
    proof
      assume X_S:
        "pp_t_eqv pp_t_one_context_unary_type w
          X (pp_t_singleton_family_at r)"
      have "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
        by (rule pp_t_pointwise_complement_respects_equivalence[
          OF X S X_S])
      then show ?thesis by blast
    next
      assume X_N:
        "pp_t_eqv pp_t_one_context_unary_type w
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
      have complements:
          "pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_pointwise_complement X)
            (pp_t_pointwise_complement
              (pp_t_pointwise_complement
                (pp_t_singleton_family_at r)))"
        by (rule pp_t_pointwise_complement_respects_equivalence[
          OF X N X_N])
      have involution:
          "pp_t_pointwise_complement
              (pp_t_pointwise_complement
                (pp_t_singleton_family_at r))
            =
          pp_t_singleton_family_at r"
        by (rule pp_t_pointwise_complement_involution[OF S])
      have "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_pointwise_complement X)
          (pp_t_singleton_family_at r)"
        using complements unfolding involution .
      then show ?thesis by blast
    qed
  qed
  show ?thesis
    unfolding pp_t_boundary_singleton_stock_def
    using boundary complemented_representation by blast
qed

section \<open>Recombination for the boundary stock\<close>

theorem pp_t_boundary_singleton_stock_recombines:
  assumes R: "Elem R (pp_t_domain Prop)"
  shows "pp_t_unary_recombines_at
    (pp_t_boundary_singleton_stock R) R w"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and X_stock: "pp_t_boundary_singleton_stock R w X"
    and necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (X \<acute> R) v"
    and q: "Elem q (pp_t_domain Prop)"
  obtain r where boundary:
      "pp_t_fundamental_boundary R w r"
    and representation:
      "pp_t_eqv pp_t_one_context_unary_type w
          X (pp_t_singleton_family_at r)
      \<or>
       pp_t_eqv pp_t_one_context_unary_type w
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
    using X_stock
    unfolding pp_t_boundary_singleton_stock_def
    by blast
  have r: "Elem r (pp_t_domain Prop)"
    using boundary
    unfolding pp_t_fundamental_boundary_def by blast
  have S:
      "Elem (pp_t_singleton_family_at r)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  have N:
      "Elem
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF S])
  from representation show "pp_t_holds (X \<acute> q) w"
  proof
    assume X_S:
      "pp_t_eqv pp_t_one_context_unary_type w
        X (pp_t_singleton_family_at r)"
    have RR: "pp_t_eqv Prop w R R"
      by (rule pp_t_eqv_reflexive[OF R])
    have applications:
        "pp_t_eqv Prop w
          (X \<acute> R) (pp_t_singleton_family_at r \<acute> R)"
      by (rule pp_t_app_respects[OF X_S R R RR])
    have X_true: "pp_t_holds (X \<acute> R) w"
      using necessary by simp
    have S_true:
        "pp_t_holds (pp_t_singleton_family_at r \<acute> R) w"
      using pp_t_prop_eqv_at[OF applications, of w]
        X_true by simp
    have equivalent: "pp_t_eqv Prop w R r"
      using pp_t_singleton_family_at_apply_holds[OF r R, of w]
        S_true by blast
    show ?thesis
      using boundary equivalent
      unfolding pp_t_fundamental_boundary_def by blast
  next
    assume X_N:
      "pp_t_eqv pp_t_one_context_unary_type w
        X
        (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
    obtain v where wv: "prefix w v"
      and equivalent_v: "pp_t_eqv Prop v R r"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have representation_v:
        "pp_t_eqv pp_t_one_context_unary_type v
          X
          (pp_t_pointwise_complement (pp_t_singleton_family_at r))"
      by (rule pp_t_eqv_persistent[OF X_N wv])
    have RR: "pp_t_eqv Prop v R R"
      by (rule pp_t_eqv_reflexive[OF R])
    have applications:
        "pp_t_eqv Prop v
          (X \<acute> R)
          (pp_t_pointwise_complement
            (pp_t_singleton_family_at r) \<acute> R)"
      by (rule pp_t_app_respects[OF representation_v R R RR])
    have X_true: "pp_t_holds (X \<acute> R) v"
      using necessary wv by blast
    have N_true:
        "pp_t_holds
          (pp_t_pointwise_complement
            (pp_t_singleton_family_at r) \<acute> R) v"
      using pp_t_prop_eqv_at[OF applications, of v]
        X_true by simp
    have S_false:
        "\<not> pp_t_holds (pp_t_singleton_family_at r \<acute> R) v"
      using pp_t_pointwise_complement_holds[OF R,
        of "pp_t_singleton_family_at r" v]
        N_true by simp
    have S_true:
        "pp_t_holds (pp_t_singleton_family_at r \<acute> R) v"
      using pp_t_singleton_family_at_apply_holds[OF r R, of v]
        equivalent_v by blast
    show ?thesis
      using S_false S_true by blast
  qed
qed

section \<open>A world-indexed fundamental parameter\<close>

definition pp_t_moving_boundary_singleton_stock ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_moving_boundary_singleton_stock R w X
    \<longleftrightarrow>
    pp_t_boundary_singleton_stock (R w) w X"

lemma pp_t_moving_boundary_singleton_stock_admissible:
  "pp_t_predicate_admissible pp_t_one_context_unary_type
    (pp_t_moving_boundary_singleton_stock R)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type
        (pp_t_boundary_singleton_stock (R v))"
    by (rule pp_t_boundary_singleton_stock_admissible)
  show "pp_t_moving_boundary_singleton_stock R v X =
      pp_t_moving_boundary_singleton_stock R v Y"
    using admissible X Y XY wv
    unfolding pp_t_predicate_admissible_def
      pp_t_moving_boundary_singleton_stock_def
    by blast
qed

lemma pp_t_moving_boundary_singleton_stock_negation_closed:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and stock: "pp_t_moving_boundary_singleton_stock R w X"
  shows "pp_t_moving_boundary_singleton_stock R w
    (pp_t_pointwise_complement X)"
  using pp_t_boundary_singleton_stock_negation_closed[OF X]
    stock
  unfolding pp_t_moving_boundary_singleton_stock_def
  by blast

theorem pp_t_moving_boundary_singleton_stock_recombines:
  assumes R: "Elem (R w) (pp_t_domain Prop)"
  shows "pp_t_unary_recombines_at
    (pp_t_moving_boundary_singleton_stock R) (R w) w"
proof -
  have fixed:
      "pp_t_unary_recombines_at
        (pp_t_boundary_singleton_stock (R w)) (R w) w"
    by (rule pp_t_boundary_singleton_stock_recombines[OF R])
  show ?thesis
    using fixed
    unfolding pp_t_unary_recombines_at_def
      pp_t_moving_boundary_singleton_stock_def
    by simp
qed

end
