theory Bacon_PP_ZF_Tree_Dual_Recurrent_Generic_Seed
  imports
    Higher_Order_Metaphysics_PP_ZF_Recurrent_Probe_Antipatching.Bacon_PP_ZF_Tree_Recurrent_Probe_Antipatching
begin

section \<open>A generic witness with two guarded self-similar cones\<close>

fun pp_b_dual_recurrent_mem ::
    "(nat \<Rightarrow> pp_b_prop) \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_b_dual_recurrent_mem q [] = True"
| "pp_b_dual_recurrent_mem q (False # u) =
    (\<exists>n v.
      False # u = pp_b_recurrent_code n @ v
      \<and> v \<in> q n)"
| "pp_b_dual_recurrent_mem q [True] = False"
| "pp_b_dual_recurrent_mem q (True # False # u) =
    (if u = [] then False else pp_b_dual_recurrent_mem q u)"
| "pp_b_dual_recurrent_mem q (True # True # u) =
    (if u = [] then True else \<not> pp_b_dual_recurrent_mem q u)"

definition pp_b_dual_recurrent_generic_witness ::
    "(nat \<Rightarrow> pp_b_prop) \<Rightarrow> pp_b_prop"
where
  "pp_b_dual_recurrent_generic_witness q =
    {w. pp_b_dual_recurrent_mem q w}"

lemma pp_b_dual_recurrent_generic_witness_root[simp]:
  "[] \<in> pp_b_dual_recurrent_generic_witness q"
  by (simp add: pp_b_dual_recurrent_generic_witness_def)

lemma pp_b_view_dual_recurrent_generic_witness_code[simp]:
  "pp_b_view (pp_b_recurrent_code n)
      (pp_b_dual_recurrent_generic_witness q)
    =
   q n"
proof (rule set_eqI)
  fix u
  show "u \<in> pp_b_view (pp_b_recurrent_code n)
          (pp_b_dual_recurrent_generic_witness q)
      \<longleftrightarrow>
      u \<in> q n"
    unfolding pp_b_view_def
      pp_b_dual_recurrent_generic_witness_def
      pp_b_recurrent_code_def
    by (auto simp: pp_b_recurrent_code_def)
qed

lemma pp_b_dual_recurrent_identity_cone:
  "u \<in> pp_b_view [True, False]
      (pp_b_dual_recurrent_generic_witness q)
    \<longleftrightarrow>
   (if u = [] then False
    else u \<in> pp_b_dual_recurrent_generic_witness q)"
  by (cases u)
    (simp_all add: pp_b_view_def
      pp_b_dual_recurrent_generic_witness_def)

lemma pp_b_dual_recurrent_negation_cone:
  "u \<in> pp_b_view [True, True]
      (pp_b_dual_recurrent_generic_witness q)
    \<longleftrightarrow>
   (if u = [] then True
    else u \<notin> pp_b_dual_recurrent_generic_witness q)"
  by (cases u)
    (simp_all add: pp_b_view_def
      pp_b_dual_recurrent_generic_witness_def)

theorem pp_b_dual_recurrent_generic_witness_for_sequence:
  fixes E :: "nat \<Rightarrow> pp_b_operator"
  assumes equivariant: "\<And>n. pp_b_equivariant (E n)"
  shows "\<exists>R.
    (\<forall>n. pp_b_root_unary_recombination (E n) R)
    \<and> [] \<in> R
    \<and> (\<forall>u.
      (u \<in> pp_b_view [True, False] R
        \<longleftrightarrow> (if u = [] then False else u \<in> R)))
    \<and> (\<forall>u.
      (u \<in> pp_b_view [True, True] R
        \<longleftrightarrow> (if u = [] then True else u \<notin> R)))"
proof -
  let ?q = "pp_b_counterexample_choice E"
  let ?R = "pp_b_dual_recurrent_generic_witness ?q"
  have recombines:
      "pp_b_root_unary_recombination (E n) ?R" for n
  proof (unfold pp_b_root_unary_recombination_def, intro impI)
    assume necessary: "\<forall>w. w \<in> E n ?R"
    show "\<forall>P. [] \<in> E n P"
    proof (rule ccontr)
      assume nonuniversal: "\<not> (\<forall>P. [] \<in> E n P)"
      have false_choice: "[] \<notin> E n (?q n)"
        using pp_b_counterexample_choice_falsifies[
          where E=E and n=n, OF nonuniversal] .
      have view_operator:
          "pp_b_view (pp_b_recurrent_code n) (E n ?R)
            =
           E n (pp_b_view (pp_b_recurrent_code n) ?R)"
        using equivariant[of n]
        unfolding pp_b_equivariant_def by blast
      have at_code: "pp_b_recurrent_code n \<in> E n ?R"
        using necessary by blast
      have root_view:
          "[] \<in> pp_b_view
            (pp_b_recurrent_code n) (E n ?R)"
        using at_code by simp
      have "[] \<in> E n (?q n)"
        using root_view view_operator by simp
      then show False
        using false_choice by blast
    qed
  qed
  show ?thesis
    by (rule exI[of _ ?R])
      (simp add: recombines
        pp_b_dual_recurrent_identity_cone
        pp_b_dual_recurrent_negation_cone)
qed

theorem pp_b_dual_recurrent_generic_witness_for_countable_stock:
  fixes Stock :: "pp_b_operator set"
  assumes countable: "countable Stock"
    and equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows "\<exists>R.
    (\<forall>F \<in> Stock. pp_b_root_unary_recombination F R)
    \<and> [] \<in> R
    \<and> (\<forall>u.
      (u \<in> pp_b_view [True, False] R
        \<longleftrightarrow> (if u = [] then False else u \<in> R)))
    \<and> (\<forall>u.
      (u \<in> pp_b_view [True, True] R
        \<longleftrightarrow> (if u = [] then True else u \<notin> R)))"
proof (cases "Stock = {}")
  case True
  let ?E = "\<lambda>n. (\<lambda>P. {})"
  have equivariant_E: "pp_b_equivariant (?E n)" for n
    unfolding pp_b_equivariant_def pp_b_view_def by simp
  obtain R where sequence:
      "\<forall>n. pp_b_root_unary_recombination (?E n) R"
    and root: "[] \<in> R"
    and identity:
      "\<forall>u. u \<in> pp_b_view [True, False] R
        \<longleftrightarrow> (if u = [] then False else u \<in> R)"
    and negation:
      "\<forall>u. u \<in> pp_b_view [True, True] R
        \<longleftrightarrow> (if u = [] then True else u \<notin> R)"
    using pp_b_dual_recurrent_generic_witness_for_sequence[
      OF equivariant_E]
    by blast
  show ?thesis
    using True root identity negation by blast
next
  case False
  let ?E = "from_nat_into Stock"
  have range: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have E_mem: "?E n \<in> Stock" for n
    using range by blast
  have E_equivariant: "pp_b_equivariant (?E n)" for n
    by (rule equivariant[OF E_mem])
  obtain R where sequence:
      "\<forall>n. pp_b_root_unary_recombination (?E n) R"
    and root: "[] \<in> R"
    and identity:
      "\<forall>u. u \<in> pp_b_view [True, False] R
        \<longleftrightarrow> (if u = [] then False else u \<in> R)"
    and negation:
      "\<forall>u. u \<in> pp_b_view [True, True] R
        \<longleftrightarrow> (if u = [] then True else u \<notin> R)"
    using pp_b_dual_recurrent_generic_witness_for_sequence[
      where E="?E", OF E_equivariant]
    by blast
  have stock:
      "\<forall>F \<in> Stock. pp_b_root_unary_recombination F R"
  proof (intro ballI)
    fix F
    assume F: "F \<in> Stock"
    then obtain n where F_eq: "F = ?E n"
      using range by blast
    show "pp_b_root_unary_recombination F R"
      unfolding F_eq by (rule sequence[rule_format])
  qed
  show ?thesis
    using stock root identity negation by blast
qed

section \<open>The two guarded cones give identity and negation recurrence\<close>

lemma pp_t_closed_negation_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_closed_den pp_negation_operator \<acute> p
      =
     pp_t_complement p"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_closed_den pp_negation_operator \<acute> p)
      (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed] p])
  show "Elem (pp_t_complement p) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  fix w
  show "pp_t_holds
      (pp_t_closed_den pp_negation_operator \<acute> p) w
      =
    pp_t_holds (pp_t_complement p) w"
    using pp_t_closed_negation_holds[OF p, of w]
    by simp
qed

lemma pp_t_dual_guarded_seed_recurrences:
  assumes root: "[] \<in> B"
    and identity:
      "\<And>u. u \<in> pp_b_view [True, False] B
        \<longleftrightarrow> (if u = [] then False else u \<in> B)"
    and negation:
      "\<And>u. u \<in> pp_b_view [True, True] B
        \<longleftrightarrow> (if u = [] then True else u \<notin> B)"
  defines "r \<equiv> pp_zf_of_b B"
  shows
    "pp_t_operator_boundary_recurrence
      (\<lambda>v. pp_t_cone_lift v r)
      (pp_t_closed_den prop_id) w"
    "pp_t_operator_boundary_recurrence
      (\<lambda>v. pp_t_cone_lift v r)
      (pp_t_closed_den pp_negation_operator) w"
proof -
  let ?R = "\<lambda>v. pp_t_cone_lift v r"
  have r: "Elem r (pp_t_domain Prop)"
    unfolding r_def by (rule pp_zf_of_b_in_domain)
  have R_domain: "Elem (?R v) (pp_t_domain Prop)" for v
    by (rule pp_t_cone_lift_in_domain)
  let ?vi = "w @ [True, False]"
  have identity_boundary:
      "pp_t_fundamental_boundary (?R ?vi) ?vi (?R w)"
  proof -
    have not_equivalent: "\<not> pp_t_eqv Prop ?vi (?R ?vi) (?R w)"
    proof
      assume equivalent: "pp_t_eqv Prop ?vi (?R ?vi) (?R w)"
      have at_vi:
          "pp_t_holds (?R ?vi) ?vi
            \<longleftrightarrow> pp_t_holds (?R w) ?vi"
        by (rule pp_t_prop_eqv_at[OF equivalent], simp)
      show False
        using at_vi root identity[of "[]"]
        unfolding r_def
        by (simp add: pp_t_cone_lift_holds pp_b_view_def)
    qed
    let ?u = "?vi @ [True]"
    have recovered: "pp_t_eqv Prop ?u (?R ?vi) (?R w)"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix z
      assume uz: "prefix ?u z"
      obtain t where z: "z = ?u @ t"
        using uz unfolding prefix_def by blast
      show "pp_t_holds (?R ?vi) z = pp_t_holds (?R w) z"
        using identity[of "[True] @ t"]
        unfolding z r_def
        by (simp add: pp_t_cone_lift_holds
          pp_b_view_def append_assoc)
    qed
    show ?thesis
      unfolding pp_t_fundamental_boundary_def
    proof (intro conjI)
      show "Elem (?R w) (pp_t_domain Prop)"
        by (rule R_domain)
      show "\<not> pp_t_eqv Prop ?vi (?R ?vi) (?R w)"
        by (rule not_equivalent)
      show "\<exists>v. prefix ?vi v
          \<and> pp_t_eqv Prop v (?R ?vi) (?R w)"
        by (intro exI[of _ ?u]) (use recovered in simp)
    qed
  qed
  show "pp_t_operator_boundary_recurrence
      ?R (pp_t_closed_den prop_id) w"
    unfolding pp_t_operator_boundary_recurrence_def
      pp_t_closed_identity_apply[OF R_domain]
    using identity_boundary
    by (intro exI[of _ ?vi]) simp
  let ?vn = "w @ [True, True]"
  have negation_boundary:
      "pp_t_fundamental_boundary
        (?R ?vn) ?vn (pp_t_complement (?R w))"
  proof -
    have complement_domain:
        "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
      by (rule pp_t_complement_in_domain)
    have not_equivalent:
        "\<not> pp_t_eqv Prop ?vn (?R ?vn) (pp_t_complement (?R w))"
    proof
      assume equivalent:
          "pp_t_eqv Prop ?vn (?R ?vn) (pp_t_complement (?R w))"
      have at_vn:
          "pp_t_holds (?R ?vn) ?vn
            \<longleftrightarrow>
           pp_t_holds (pp_t_complement (?R w)) ?vn"
        by (rule pp_t_prop_eqv_at[OF equivalent], simp)
      show False
        using at_vn root negation[of "[]"]
        unfolding r_def
        by (simp add: pp_t_cone_lift_holds pp_b_view_def)
    qed
    let ?u = "?vn @ [True]"
    have recovered:
        "pp_t_eqv Prop ?u (?R ?vn) (pp_t_complement (?R w))"
      unfolding pp_t_eqv.simps
    proof (intro allI impI)
      fix z
      assume uz: "prefix ?u z"
      obtain t where z: "z = ?u @ t"
        using uz unfolding prefix_def by blast
      show "pp_t_holds (?R ?vn) z
          =
        pp_t_holds (pp_t_complement (?R w)) z"
        using negation[of "[True] @ t"]
        unfolding z r_def
        by (simp add: pp_t_cone_lift_holds
          pp_b_view_def append_assoc)
    qed
    show ?thesis
      unfolding pp_t_fundamental_boundary_def
    proof (intro conjI)
      show "Elem (pp_t_complement (?R w)) (pp_t_domain Prop)"
        by (rule complement_domain)
      show "\<not> pp_t_eqv Prop ?vn
          (?R ?vn) (pp_t_complement (?R w))"
        by (rule not_equivalent)
      show "\<exists>v. prefix ?vn v
          \<and> pp_t_eqv Prop v
            (?R ?vn) (pp_t_complement (?R w))"
        by (intro exI[of _ ?u]) (use recovered in simp)
    qed
  qed
  show "pp_t_operator_boundary_recurrence
      ?R (pp_t_closed_den pp_negation_operator) w"
    unfolding pp_t_operator_boundary_recurrence_def
      pp_t_closed_negation_apply[OF R_domain]
    using negation_boundary
      by (intro exI[of _ ?vn]) simp
qed

section \<open>Countably represented stocks admit dual-recurrent seeds\<close>

definition pp_t_dual_guarded_cones :: "ZF \<Rightarrow> bool"
where
  "pp_t_dual_guarded_cones r
    \<longleftrightarrow>
    pp_t_holds r []
    \<and> (\<forall>u.
      pp_t_holds r ([True, False] @ u)
        \<longleftrightarrow>
      (if u = [] then False else pp_t_holds r u))
    \<and> (\<forall>u.
      pp_t_holds r ([True, True] @ u)
        \<longleftrightarrow>
      (if u = [] then True else \<not> pp_t_holds r u))"

theorem
  pp_t_countably_represented_unary_stock_dual_recurrent_guarded_seed_exists:
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
  shows "\<exists>r.
    Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at S r []
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den prop_id) w)
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den pp_negation_operator) w)
    \<and> pp_t_dual_guarded_cones r"
proof -
  let ?T = "pp_b_operator_of ` D"
  have T_countable: "countable ?T"
    using countable by (rule countable_image)
  have T_equivariant:
      "\<And>F. F \<in> ?T \<Longrightarrow> pp_b_equivariant F"
    using D_equivariant by blast
  obtain B where generic:
      "\<forall>F \<in> ?T. pp_b_root_unary_recombination F B"
    and root: "[] \<in> B"
    and identity:
      "\<forall>u. u \<in> pp_b_view [True, False] B
        \<longleftrightarrow> (if u = [] then False else u \<in> B)"
    and negation:
      "\<forall>u. u \<in> pp_b_view [True, True] B
        \<longleftrightarrow> (if u = [] then True else u \<notin> B)"
    using pp_b_dual_recurrent_generic_witness_for_countable_stock[
      OF T_countable T_equivariant]
    by blast
  let ?r = "pp_zf_of_b B"
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
        by (rule pp_t_eqv_reflexive[OF r])
      have applications:
          "pp_t_eqv Prop w (X \<acute> ?r) (d \<acute> ?r)"
        by (rule pp_t_app_respects[OF Xd_w r r rr])
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
      by (rule pp_t_app_respects[
        OF Xd q q pp_t_eqv_reflexive[OF q]])
    have transfer:
        "pp_t_holds (X \<acute> q) []
          \<longleftrightarrow> pp_t_holds (d \<acute> q) []"
      by (rule pp_t_prop_eqv_at[OF Xd_q], simp)
    show "pp_t_holds (X \<acute> q) []"
      using transfer d_universal q by blast
  qed
  have recombines:
      "pp_t_unary_recombines_at S ?r []"
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
  have identity_recurrence:
      "\<And>w. pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v ?r)
        (pp_t_closed_den prop_id) w"
    by (rule pp_t_dual_guarded_seed_recurrences(1)[
      OF root identity[rule_format] negation[rule_format]])
  have negation_recurrence:
      "\<And>w. pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v ?r)
        (pp_t_closed_den pp_negation_operator) w"
    by (rule pp_t_dual_guarded_seed_recurrences(2)[
      OF root identity[rule_format] negation[rule_format]])
  have guarded: "pp_t_dual_guarded_cones ?r"
    unfolding pp_t_dual_guarded_cones_def
  proof (intro conjI)
    show "pp_t_holds ?r []"
      using root by simp
    show "\<forall>u.
        pp_t_holds ?r ([True, False] @ u)
          =
        (if u = [] then False else pp_t_holds ?r u)"
    proof
      fix u
      show "pp_t_holds ?r ([True, False] @ u)
          =
        (if u = [] then False else pp_t_holds ?r u)"
        using identity[rule_format, of u]
        by (simp add: pp_b_view_def)
    qed
    show "\<forall>u.
        pp_t_holds ?r ([True, True] @ u)
          =
        (if u = [] then True else \<not> pp_t_holds ?r u)"
    proof
      fix u
      show "pp_t_holds ?r ([True, True] @ u)
          =
        (if u = [] then True else \<not> pp_t_holds ?r u)"
        using negation[rule_format, of u]
        by (simp add: pp_b_view_def)
    qed
  qed
  show ?thesis
    using r recombines identity_recurrence negation_recurrence guarded
    by blast
qed

corollary pp_t_countably_represented_unary_stock_dual_recurrent_seed_exists:
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
  shows "\<exists>r.
    Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at S r []
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den prop_id) w)
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den pp_negation_operator) w)"
  using
    pp_t_countably_represented_unary_stock_dual_recurrent_guarded_seed_exists[
      OF countable D_domain D_equivariant represented]
  by blast

section \<open>A dual-recurrent modal-Boolean seed\<close>

theorem
  pp_t_probe_modal_boolean_dual_recurrent_guarded_root_seed_exists:
  "\<exists>r.
    Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock r []
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den prop_id) w)
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den pp_negation_operator) w)
    \<and> pp_t_dual_guarded_cones r"
proof (rule
    pp_t_countably_represented_unary_stock_dual_recurrent_guarded_seed_exists[
      where D=pp_t_probe_modal_boolean_representatives])
  show "countable pp_t_probe_modal_boolean_representatives"
    by (rule pp_t_probe_modal_boolean_representatives_countable)
  show "\<And>d.
      d \<in> pp_t_probe_modal_boolean_representatives
      \<Longrightarrow>
      Elem d (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_probe_modal_boolean_representative_in_domain)
  show "\<And>d.
      d \<in> pp_t_probe_modal_boolean_representatives
      \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    by (rule pp_t_probe_modal_boolean_representative_equivariant)
  show "\<And>X.
      Elem X (pp_t_domain pp_t_one_context_unary_type)
      \<Longrightarrow> pp_t_probe_modal_boolean_stock [] X
      \<Longrightarrow>
      \<exists>d \<in> pp_t_probe_modal_boolean_representatives.
        pp_t_eqv pp_t_one_context_unary_type [] X d"
    using pp_t_probe_modal_boolean_stock_root_represented by blast
qed

corollary pp_t_probe_modal_boolean_dual_recurrent_root_seed_exists:
  "\<exists>r.
    Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock r []
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den prop_id) w)
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r)
        (pp_t_closed_den pp_negation_operator) w)"
  using
    pp_t_probe_modal_boolean_dual_recurrent_guarded_root_seed_exists
  by blast

definition pp_t_probe_modal_boolean_dual_recurrent_root_seed :: ZF
where
  "pp_t_probe_modal_boolean_dual_recurrent_root_seed =
    (SOME r.
      Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock r []
      \<and> (\<forall>w.
        pp_t_operator_boundary_recurrence
          (\<lambda>v. pp_t_cone_lift v r)
          (pp_t_closed_den prop_id) w)
      \<and> (\<forall>w.
        pp_t_operator_boundary_recurrence
          (\<lambda>v. pp_t_cone_lift v r)
          (pp_t_closed_den pp_negation_operator) w)
      \<and> pp_t_dual_guarded_cones r)"

lemma pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec:
  "Elem pp_t_probe_modal_boolean_dual_recurrent_root_seed
      (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock
      pp_t_probe_modal_boolean_dual_recurrent_root_seed []
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v
          pp_t_probe_modal_boolean_dual_recurrent_root_seed)
        (pp_t_closed_den prop_id) w)
    \<and> (\<forall>w.
      pp_t_operator_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v
          pp_t_probe_modal_boolean_dual_recurrent_root_seed)
        (pp_t_closed_den pp_negation_operator) w)"
  unfolding pp_t_probe_modal_boolean_dual_recurrent_root_seed_def
  using someI_ex[
    OF
      pp_t_probe_modal_boolean_dual_recurrent_guarded_root_seed_exists]
  by blast

lemma pp_t_probe_modal_boolean_dual_recurrent_root_seed_guarded:
  "pp_t_dual_guarded_cones
    pp_t_probe_modal_boolean_dual_recurrent_root_seed"
  unfolding pp_t_probe_modal_boolean_dual_recurrent_root_seed_def
  using someI_ex[
    OF
      pp_t_probe_modal_boolean_dual_recurrent_guarded_root_seed_exists]
  by blast

definition pp_t_probe_modal_boolean_dual_recurrent_seed_at ::
    "bool list \<Rightarrow> ZF"
where
  "pp_t_probe_modal_boolean_dual_recurrent_seed_at w =
    pp_t_cone_lift w
      pp_t_probe_modal_boolean_dual_recurrent_root_seed"

lemma pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain:
  "Elem (pp_t_probe_modal_boolean_dual_recurrent_seed_at w)
    (pp_t_domain Prop)"
  unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem pp_t_probe_modal_boolean_dual_recurrent_seed_recombines:
  "pp_t_unary_recombines_at
    pp_t_probe_modal_boolean_stock
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def
  by (rule
    pp_t_unary_stock_root_recombination_transports_to_cone[
      OF
        pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[THEN conjunct1]
        pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[
          THEN conjunct2, THEN conjunct1]
        pp_t_probe_modal_boolean_stock_cone_iff])

theorem pp_t_probe_modal_boolean_dual_identity_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    (pp_t_closed_den prop_id) w"
  using pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[
    THEN conjunct2, THEN conjunct2, THEN conjunct1,
    rule_format, of w]
  unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def .

theorem pp_t_probe_modal_boolean_dual_negation_recurrence:
  "pp_t_operator_boundary_recurrence
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    (pp_t_closed_den pp_negation_operator) w"
  using pp_t_probe_modal_boolean_dual_recurrent_root_seed_spec[
    THEN conjunct2, THEN conjunct2, THEN conjunct2,
    rule_format, of w]
  unfolding pp_t_probe_modal_boolean_dual_recurrent_seed_at_def .

section \<open>Classifier sections over the dual-recurrent seed\<close>

abbreviation pp_t_dual_recurrent_full_section :: "ZF \<Rightarrow> ZF"
where
  "pp_t_dual_recurrent_full_section F \<equiv>
    pp_t_unary_output_disjunction
      (pp_t_recurrent_modal_component F)
      (pp_t_moving_boundary_operator_probe
        pp_t_probe_modal_boolean_dual_recurrent_seed_at \<acute> F)"

lemma pp_t_dual_recurrent_full_section_in_domain:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "Elem (pp_t_dual_recurrent_full_section F)
      (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_unary_output_disjunction_in_domain[
    OF pp_t_recurrent_modal_component_in_domain[OF F]
      pp_t_app_closed[
        OF pp_t_moving_boundary_operator_probe_in_domain F]])

theorem pp_t_dual_recurrent_complemented_identity_section_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den prop_id)))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule
    pp_t_complemented_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_closed_den_in_domain[OF typed_prop_id]
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_closed_den_in_domain[OF typed_prop_id]]
        pp_t_probe_modal_boolean_dual_identity_recurrence])

theorem pp_t_dual_recurrent_complemented_negation_section_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_negation_operator)))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule
    pp_t_complemented_generated_boundary_disjunction_recombination_safe[
      OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
        pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed]
        pp_t_recurrent_modal_component_in_domain[
          OF pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed]]
        pp_t_probe_modal_boolean_dual_negation_recurrence])

lemma pp_t_dual_recurrent_modal_identity_component_false_on_seed:
  "\<not> pp_t_holds
    (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
      \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have not_singleton:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?r)"
  proof
    assume singleton:
        "pp_t_probe_modal_boolean_stock w
          (pp_t_singleton_family_at ?r)"
    have not_reflexive: "\<not> pp_t_eqv Prop w ?r ?r"
      by (rule
        pp_t_pure_singleton_parameter_not_currently_fundamental[
          where Pure=pp_t_probe_modal_boolean_stock,
          OF r r singleton
            pp_t_probe_modal_boolean_dual_recurrent_seed_recombines])
    show False
      using not_reflexive pp_t_eqv_reflexive[OF r, of w]
      by blast
  qed
  have component:
      "pp_t_holds
          (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
            \<acute> ?r) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at
          (pp_t_closed_den prop_id \<acute> ?r))"
    by (rule pp_t_modal_singleton_operator_probe_apply_holds[
      OF pp_t_closed_den_in_domain[OF typed_prop_id] r])
  show ?thesis
    using component not_singleton
    unfolding pp_t_closed_identity_apply[OF r]
    by blast
qed

lemma pp_t_dual_recurrent_identity_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    (pp_t_closed_den prop_id)
    (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)) w"
proof (unfold pp_t_operator_boundary_antipatching_def,
    intro impI)
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have not_component:
      "\<not> pp_t_holds
        (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
          \<acute> ?r) w"
    by (rule pp_t_dual_recurrent_modal_identity_component_false_on_seed)
  have not_boundary:
      "\<not> pp_t_fundamental_boundary ?r w
        (pp_t_closed_den prop_id \<acute> ?r)"
    unfolding pp_t_closed_identity_apply[OF r]
      pp_t_fundamental_boundary_def
    using pp_t_eqv_reflexive[OF r, of w]
    by blast
  show "\<exists>v. prefix w v
      \<and> \<not> pp_t_holds
        (pp_t_recurrent_modal_component (pp_t_closed_den prop_id)
          \<acute> ?r) v
      \<and> \<not> pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) v
        (pp_t_closed_den prop_id \<acute> ?r)"
    using not_component not_boundary
    by (intro exI[of _ w]) simp
qed

theorem pp_t_dual_recurrent_identity_section_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section (pp_t_closed_den prop_id))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule pp_t_generated_boundary_disjunction_recombination_safe[
    OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
      pp_t_closed_den_in_domain[OF typed_prop_id]
      pp_t_recurrent_modal_component_in_domain[
        OF pp_t_closed_den_in_domain[OF typed_prop_id]]
      pp_t_dual_recurrent_identity_antipatching])

theorem pp_t_dual_recurrent_negation_section_safe_if:
  assumes antipatching:
      "pp_t_operator_boundary_antipatching
        pp_t_probe_modal_boolean_dual_recurrent_seed_at
        (pp_t_closed_den pp_negation_operator)
        (pp_t_recurrent_modal_component
          (pp_t_closed_den pp_negation_operator)) w"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_dual_recurrent_full_section
        (pp_t_closed_den pp_negation_operator))
      (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule pp_t_generated_boundary_disjunction_recombination_safe[
    OF pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain
      pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed]
      pp_t_recurrent_modal_component_in_domain[
        OF pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed]]
      antipatching])

lemma pp_t_dual_recurrent_modal_negation_component_false_on_seed:
  "\<not> pp_t_holds
    (pp_t_recurrent_modal_component
        (pp_t_closed_den pp_negation_operator)
      \<acute> pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
proof -
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  let ?nr = "pp_t_complement ?r"
  let ?S = "pp_t_singleton_family_at ?nr"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have nr: "Elem ?nr (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have S: "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF nr])
  have not_singleton:
      "\<not> pp_t_probe_modal_boolean_stock w ?S"
  proof
    assume singleton: "pp_t_probe_modal_boolean_stock w ?S"
    have complement:
        "pp_t_probe_modal_boolean_stock w
          (pp_t_pointwise_complement ?S)"
      unfolding pp_t_pointwise_complement_eq_unary_complement
      by (rule
        pp_t_probe_modal_boolean_stock_unary_complement_closed[
          OF S singleton])
    show False
      by (rule
        pp_t_complement_singleton_cannot_be_pure_under_recombination[
          where Pure=pp_t_probe_modal_boolean_stock,
          OF r singleton complement
            pp_t_probe_modal_boolean_dual_recurrent_seed_recombines])
  qed
  have component:
      "pp_t_holds
          (pp_t_recurrent_modal_component
              (pp_t_closed_den pp_negation_operator)
            \<acute> ?r) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at
          (pp_t_closed_den pp_negation_operator \<acute> ?r))"
    by (rule pp_t_modal_singleton_operator_probe_apply_holds[
      OF pp_t_closed_den_in_domain[OF pp_t_closed_negation_typed] r])
  show ?thesis
    using component not_singleton
    unfolding pp_t_closed_negation_apply[OF r]
    by blast
qed

lemma pp_t_dual_recurrent_negation_antipatching:
  "pp_t_operator_boundary_antipatching
    pp_t_probe_modal_boolean_dual_recurrent_seed_at
    (pp_t_closed_den pp_negation_operator)
    (pp_t_recurrent_modal_component
      (pp_t_closed_den pp_negation_operator)) w"
proof (unfold pp_t_operator_boundary_antipatching_def,
    intro impI)
  let ?r = "pp_t_probe_modal_boolean_dual_recurrent_seed_at w"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_probe_modal_boolean_dual_recurrent_seed_at_in_domain)
  have not_component:
      "\<not> pp_t_holds
        (pp_t_recurrent_modal_component
            (pp_t_closed_den pp_negation_operator)
          \<acute> ?r) w"
    by (rule pp_t_dual_recurrent_modal_negation_component_false_on_seed)
  have not_boundary:
      "\<not> pp_t_fundamental_boundary ?r w
        (pp_t_closed_den pp_negation_operator \<acute> ?r)"
  proof
    assume boundary:
        "pp_t_fundamental_boundary ?r w
          (pp_t_closed_den pp_negation_operator \<acute> ?r)"
    obtain v where
        "pp_t_eqv Prop v ?r
          (pp_t_closed_den pp_negation_operator \<acute> ?r)"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    then show False
      unfolding pp_t_closed_negation_apply[OF r]
      using pp_t_proposition_never_equivalent_to_its_complement[
        OF r, of v]
      by blast
  qed
  show "\<exists>v. prefix w v
      \<and> \<not> pp_t_holds
        (pp_t_recurrent_modal_component
            (pp_t_closed_den pp_negation_operator)
          \<acute> ?r) v
      \<and> \<not> pp_t_fundamental_boundary
        (pp_t_probe_modal_boolean_dual_recurrent_seed_at v) v
        (pp_t_closed_den pp_negation_operator \<acute> ?r)"
    using not_component not_boundary
    by (intro exI[of _ w]) simp
qed

corollary pp_t_dual_recurrent_negation_section_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_dual_recurrent_full_section
      (pp_t_closed_den pp_negation_operator))
    (pp_t_probe_modal_boolean_dual_recurrent_seed_at w) w"
  by (rule pp_t_dual_recurrent_negation_section_safe_if[
    OF pp_t_dual_recurrent_negation_antipatching])

end
