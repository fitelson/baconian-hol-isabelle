theory Bacon_PP_ZF_Tree_Recurrent_Generic_Seed
  imports
    Higher_Order_Metaphysics_PP_ZF_Boundary_Probe_Recombination.Bacon_PP_ZF_Tree_Boundary_Probe_Recombination
begin

section \<open>A generic witness with a reserved empty cone\<close>

definition pp_b_recurrent_code :: "nat \<Rightarrow> bool list"
where
  "pp_b_recurrent_code n = False # pp_b_code n"

lemma pp_b_recurrent_code_append_eq[simp]:
  "pp_b_recurrent_code n @ u = pp_b_recurrent_code m @ v
    \<longleftrightarrow> n = m \<and> u = v"
  unfolding pp_b_recurrent_code_def
  by simp

definition pp_b_recurrent_generic_witness ::
    "(nat \<Rightarrow> pp_b_prop) \<Rightarrow> pp_b_prop"
where
  "pp_b_recurrent_generic_witness q =
    insert [] (\<Union>n.
      pp_b_lift (pp_b_recurrent_code n) (q n))"

lemma pp_b_recurrent_generic_witness_mem:
  "w \<in> pp_b_recurrent_generic_witness q
    \<longleftrightarrow>
    (w = [] \<or>
      (\<exists>n u.
        w = pp_b_recurrent_code n @ u \<and> u \<in> q n))"
  by (auto simp: pp_b_recurrent_generic_witness_def
      pp_b_lift_def)

lemma pp_b_view_recurrent_generic_witness[simp]:
  "pp_b_view (pp_b_recurrent_code n)
      (pp_b_recurrent_generic_witness q)
    =
   q n"
proof (rule set_eqI)
  fix u
  show "u \<in> pp_b_view (pp_b_recurrent_code n)
          (pp_b_recurrent_generic_witness q)
      \<longleftrightarrow>
      u \<in> q n"
    unfolding pp_b_view_def pp_b_recurrent_generic_witness_mem
      pp_b_recurrent_code_def
    by auto
qed

lemma pp_b_recurrent_generic_witness_root[simp]:
  "[] \<in> pp_b_recurrent_generic_witness q"
  by (simp add: pp_b_recurrent_generic_witness_mem)

lemma pp_b_recurrent_generic_witness_right_cone_empty:
  "pp_b_view [True] (pp_b_recurrent_generic_witness q) = {}"
  by (auto simp: pp_b_view_def
      pp_b_recurrent_generic_witness_mem
      pp_b_recurrent_code_def)

theorem pp_b_recurrent_generic_witness_for_sequence:
  fixes E :: "nat \<Rightarrow> pp_b_operator"
  assumes equivariant: "\<And>n. pp_b_equivariant (E n)"
  shows "\<exists>R.
    (\<forall>n. pp_b_root_unary_recombination (E n) R)
    \<and> [] \<in> R
    \<and> pp_b_view [True] R = {}"
proof -
  let ?q = "pp_b_counterexample_choice E"
  let ?R = "pp_b_recurrent_generic_witness ?q"
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
        pp_b_recurrent_generic_witness_right_cone_empty)
qed

theorem pp_b_recurrent_generic_witness_for_countable_stock:
  fixes Stock :: "pp_b_operator set"
  assumes countable: "countable Stock"
    and equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows "\<exists>R.
    (\<forall>F \<in> Stock. pp_b_root_unary_recombination F R)
    \<and> [] \<in> R
    \<and> pp_b_view [True] R = {}"
proof (cases "Stock = {}")
  case True
  let ?R = "{[]} :: pp_b_prop"
  have root: "[] \<in> ?R"
    by simp
  have empty: "pp_b_view [True] ?R = {}"
    by (auto simp: pp_b_view_def)
  show ?thesis
    using True root empty by blast
next
  case False
  let ?E = "from_nat_into Stock"
  have range: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have E_mem: "?E n \<in> Stock" for n
    using range by blast
  have E_equivariant: "pp_b_equivariant (?E n)" for n
    by (rule equivariant[OF E_mem])
  have existence:
      "\<exists>R.
        (\<forall>n. pp_b_root_unary_recombination (?E n) R)
        \<and> [] \<in> R
        \<and> pp_b_view [True] R = {}"
    by (rule pp_b_recurrent_generic_witness_for_sequence[
      where E="?E"])
      (rule E_equivariant)
  obtain R where sequence:
      "\<forall>n. pp_b_root_unary_recombination (?E n) R"
    and root: "[] \<in> R"
    and empty: "pp_b_view [True] R = {}"
    using existence by blast
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
    using stock root empty by blast
qed

section \<open>The reserved cone gives boundary recurrence\<close>

lemma pp_t_reserved_cone_seed_recurrence:
  assumes root: "[] \<in> B"
    and empty: "pp_b_view [True] B = {}"
  defines "r \<equiv> pp_zf_of_b B"
  shows
    "pp_t_seed_boundary_recurrence
      (\<lambda>w. pp_t_cone_lift w r) w"
proof -
  have r: "Elem r (pp_t_domain Prop)"
    unfolding r_def by (rule pp_zf_of_b_in_domain)
  have no_right:
      "\<And>u. [True] @ u \<notin> B"
    using empty
    by (auto simp: pp_b_view_def)
  let ?v = "w @ [True]"
  let ?A = "pp_t_cone_lift ?v r"
  let ?P = "pp_t_cone_lift w r"
  have A: "Elem ?A (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have P: "Elem ?P (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have not_equivalent: "\<not> pp_t_eqv Prop ?v ?A ?P"
  proof
    assume equivalent: "pp_t_eqv Prop ?v ?A ?P"
    have at_v:
        "pp_t_holds ?A ?v \<longleftrightarrow> pp_t_holds ?P ?v"
      by (rule pp_t_prop_eqv_at[OF equivalent], simp)
    have A_true: "pp_t_holds ?A ?v"
      using root
      unfolding r_def
      by (simp add: pp_t_cone_lift_holds)
    have P_false: "\<not> pp_t_holds ?P ?v"
      using no_right[of "[]"]
      unfolding r_def
      by (simp add: pp_t_cone_lift_holds)
    show False using at_v A_true P_false by blast
  qed
  let ?u = "?v @ [True]"
  have recovered: "pp_t_eqv Prop ?u ?A ?P"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume uz: "prefix ?u z"
    obtain t where z: "z = ?u @ t"
      using uz unfolding prefix_def by blast
    have A_false: "\<not> pp_t_holds ?A z"
      using no_right[of t]
      unfolding z r_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
    have P_false: "\<not> pp_t_holds ?P z"
      using no_right[of "[True] @ t"]
      unfolding z r_def
      by (simp add: pp_t_cone_lift_holds append_assoc)
    show "pp_t_holds ?A z = pp_t_holds ?P z"
      using A_false P_false by blast
  qed
  have boundary: "pp_t_fundamental_boundary ?A ?v ?P"
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem ?P (pp_t_domain Prop)"
      by (rule P)
    show "\<not> pp_t_eqv Prop ?v ?A ?P"
      by (rule not_equivalent)
    show "\<exists>z. prefix ?v z \<and> pp_t_eqv Prop z ?A ?P"
    proof (rule exI[of _ ?u], intro conjI)
      show "prefix ?v ?u"
        by simp
      show "pp_t_eqv Prop ?u ?A ?P"
        by (rule recovered)
    qed
  qed
  show ?thesis
    unfolding pp_t_seed_boundary_recurrence_def
    using boundary by (intro exI[of _ ?v]) simp
qed

section \<open>Countably represented stocks admit recurrent seeds\<close>

theorem pp_t_countably_represented_unary_stock_recurrent_seed_exists:
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
      pp_t_seed_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r) w)"
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
    and empty: "pp_b_view [True] B = {}"
    using pp_b_recurrent_generic_witness_for_countable_stock[
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
    have dq: "pp_t_holds (d \<acute> q) []"
      using d_universal q by blast
    show "pp_t_holds (X \<acute> q) []"
      using transfer dq by blast
  qed
  have recombines:
      "pp_t_unary_recombines_at S ?r []"
    unfolding pp_t_unary_recombines_at_def
    using pointwise by auto
  have recurrence:
      "\<And>w. pp_t_seed_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v ?r) w"
    by (rule pp_t_reserved_cone_seed_recurrence[
      OF root empty])
  show ?thesis
    using r recombines recurrence by blast
qed

section \<open>A recurrent modal-Boolean Recombination seed\<close>

theorem pp_t_probe_modal_boolean_recurrent_root_seed_exists:
  "\<exists>r.
    Elem r (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock r []
    \<and> (\<forall>w.
      pp_t_seed_boundary_recurrence
        (\<lambda>v. pp_t_cone_lift v r) w)"
proof (rule
    pp_t_countably_represented_unary_stock_recurrent_seed_exists[
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

definition pp_t_probe_modal_boolean_recurrent_root_seed :: ZF
where
  "pp_t_probe_modal_boolean_recurrent_root_seed =
    (SOME r.
      Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock r []
      \<and> (\<forall>w.
        pp_t_seed_boundary_recurrence
          (\<lambda>v. pp_t_cone_lift v r) w))"

lemma pp_t_probe_modal_boolean_recurrent_root_seed_spec:
  "Elem pp_t_probe_modal_boolean_recurrent_root_seed
      (pp_t_domain Prop)
    \<and> pp_t_unary_recombines_at
      pp_t_probe_modal_boolean_stock
      pp_t_probe_modal_boolean_recurrent_root_seed []
    \<and> (\<forall>w.
      pp_t_seed_boundary_recurrence
        (\<lambda>v.
          pp_t_cone_lift v
            pp_t_probe_modal_boolean_recurrent_root_seed) w)"
  unfolding pp_t_probe_modal_boolean_recurrent_root_seed_def
  using someI_ex[
    OF pp_t_probe_modal_boolean_recurrent_root_seed_exists] .

definition pp_t_probe_modal_boolean_recurrent_seed_at ::
    "bool list \<Rightarrow> ZF"
where
  "pp_t_probe_modal_boolean_recurrent_seed_at w =
    pp_t_cone_lift w
      pp_t_probe_modal_boolean_recurrent_root_seed"

lemma pp_t_probe_modal_boolean_recurrent_seed_at_in_domain:
  "Elem (pp_t_probe_modal_boolean_recurrent_seed_at w)
    (pp_t_domain Prop)"
  unfolding pp_t_probe_modal_boolean_recurrent_seed_at_def
  by (rule pp_t_cone_lift_in_domain)

theorem pp_t_probe_modal_boolean_recurrent_seed_recombines:
  "pp_t_unary_recombines_at
    pp_t_probe_modal_boolean_stock
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  unfolding pp_t_probe_modal_boolean_recurrent_seed_at_def
  by (rule
    pp_t_unary_stock_root_recombination_transports_to_cone[
      OF
        pp_t_probe_modal_boolean_recurrent_root_seed_spec[THEN conjunct1]
        pp_t_probe_modal_boolean_recurrent_root_seed_spec[
          THEN conjunct2, THEN conjunct1]
        pp_t_probe_modal_boolean_stock_cone_iff])

theorem pp_t_probe_modal_boolean_recurrent_seed_recurrence:
  "pp_t_seed_boundary_recurrence
    pp_t_probe_modal_boolean_recurrent_seed_at w"
  using pp_t_probe_modal_boolean_recurrent_root_seed_spec[
    THEN conjunct2, THEN conjunct2, rule_format, of w]
  unfolding pp_t_probe_modal_boolean_recurrent_seed_at_def .

corollary
  pp_t_recurrent_seed_complemented_boundary_probe_recombination_safe:
  "pp_t_recombination_safe_unary_operator
    (pp_t_pointwise_complement
      (pp_t_moving_boundary_identity_probe
        pp_t_probe_modal_boolean_recurrent_seed_at))
    (pp_t_probe_modal_boolean_recurrent_seed_at w) w"
  using
    pp_t_complemented_boundary_probe_recombines_iff_seed_recurrence[
      where R=pp_t_probe_modal_boolean_recurrent_seed_at and w=w,
      OF pp_t_probe_modal_boolean_recurrent_seed_at_in_domain]
    pp_t_probe_modal_boolean_recurrent_seed_recurrence
  by blast

end
