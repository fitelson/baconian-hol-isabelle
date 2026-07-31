theory Bacon_PP_ZF_Tree_Dual_Pair_Grafting
  imports
    Higher_Order_Metaphysics_PP_ZF_Dual_Boolean_Closure.Bacon_PP_ZF_Tree_Dual_Boolean_Closure
begin

section \<open>A local boundary graft with a reserved generic cone\<close>

definition pp_b_pair_boundary_graft ::
    "pp_b_prop \<Rightarrow> pp_b_prop \<Rightarrow> pp_b_prop"
where
  "pp_b_pair_boundary_graft A G =
    (if [] \<in> A then {} else {[]})
      \<union> pp_b_lift [False] (pp_b_view [False] A)
      \<union> pp_b_lift [True] G"

lemma pp_b_pair_boundary_graft_root[simp]:
  "[] \<in> pp_b_pair_boundary_graft A G
    \<longleftrightarrow> [] \<notin> A"
  by (auto simp: pp_b_pair_boundary_graft_def pp_b_lift_def)

lemma pp_b_pair_boundary_graft_false_view[simp]:
  "pp_b_view [False] (pp_b_pair_boundary_graft A G)
    = pp_b_view [False] A"
  by (auto simp: pp_b_pair_boundary_graft_def
      pp_b_view_def pp_b_lift_def)

lemma pp_b_pair_boundary_graft_true_view[simp]:
  "pp_b_view [True] (pp_b_pair_boundary_graft A G) = G"
  by (auto simp: pp_b_pair_boundary_graft_def
      pp_b_view_def pp_b_lift_def)

lemma pp_b_pair_boundary_graft_nonempty_view:
  "pp_b_view (c # u) (pp_b_pair_boundary_graft A G)
    =
   pp_b_view u (if c then G else pp_b_view [False] A)"
proof -
  have
      "pp_b_view u
        (pp_b_view [c] (pp_b_pair_boundary_graft A G))
        =
       pp_b_view ([c] @ u) (pp_b_pair_boundary_graft A G)"
    by (rule pp_b_view_compose)
  then show ?thesis
    by (cases c) simp_all
qed

definition pp_b_view_omits ::
    "pp_b_prop \<Rightarrow> pp_b_prop \<Rightarrow> bool"
where
  "pp_b_view_omits P B
    \<longleftrightarrow> (\<forall>s. pp_b_view s P \<noteq> B)"

theorem pp_b_pair_boundary_graft_view_omits:
  assumes root: "pp_b_pair_boundary_graft A G \<noteq> B"
    and A_omits: "pp_b_view_omits A B"
    and G_omits: "pp_b_view_omits G B"
  shows "pp_b_view_omits (pp_b_pair_boundary_graft A G) B"
  unfolding pp_b_view_omits_def
proof
  fix s
  show "pp_b_view s (pp_b_pair_boundary_graft A G) \<noteq> B"
  proof (cases s)
    case Nil
    then show ?thesis using root by simp
  next
    case (Cons c u)
    show ?thesis
    proof (cases c)
      case False
      have omitted:
          "pp_b_view ([False] @ u) A \<noteq> B"
        using A_omits
        unfolding pp_b_view_omits_def by blast
      show ?thesis
        using Cons False omitted
        by (simp add: pp_b_pair_boundary_graft_nonempty_view
          pp_b_view_compose)
    next
      case True
      have omitted: "pp_b_view u G \<noteq> B"
        using G_omits
        unfolding pp_b_view_omits_def by blast
      show ?thesis
        using Cons True omitted
        by (simp add: pp_b_pair_boundary_graft_nonempty_view)
    qed
  qed
qed

definition pp_b_locally_distinct ::
    "pp_b_prop \<Rightarrow> pp_b_prop \<Rightarrow> bool"
where
  "pp_b_locally_distinct P Q
    \<longleftrightarrow>
    (\<forall>s. pp_b_view s P \<noteq> pp_b_view s Q)"

theorem pp_b_pair_boundary_graft_locally_distinct:
  assumes root:
      "pp_b_pair_boundary_graft A G \<noteq> B"
    and left:
      "pp_b_locally_distinct
        (pp_b_view [False] A) (pp_b_view [False] B)"
    and right:
      "pp_b_locally_distinct G (pp_b_view [True] B)"
  shows
    "pp_b_locally_distinct (pp_b_pair_boundary_graft A G) B"
  unfolding pp_b_locally_distinct_def
proof
  fix s
  show
      "pp_b_view s (pp_b_pair_boundary_graft A G)
        \<noteq> pp_b_view s B"
  proof (cases s)
    case Nil
    then show ?thesis using root by simp
  next
    case (Cons c u)
    show ?thesis
    proof (cases c)
      case False
      have distinct:
          "pp_b_view u (pp_b_view [False] A)
            \<noteq> pp_b_view u (pp_b_view [False] B)"
        using left
        unfolding pp_b_locally_distinct_def by blast
      show ?thesis
        using Cons False distinct
        by (simp add: pp_b_pair_boundary_graft_nonempty_view
          pp_b_view_compose)
    next
      case True
      have distinct:
          "pp_b_view u G
            \<noteq> pp_b_view u (pp_b_view [True] B)"
        using right
        unfolding pp_b_locally_distinct_def by blast
      show ?thesis
        using Cons True distinct
        by (simp add: pp_b_pair_boundary_graft_nonempty_view
          pp_b_view_compose)
    qed
  qed
qed

section \<open>The reserved generic cone preserves Recombination\<close>

theorem pp_b_pair_boundary_graft_recombination:
  assumes equivariant: "pp_b_equivariant F"
    and generic: "pp_b_root_unary_recombination F G"
  shows
    "pp_b_root_unary_recombination F
      (pp_b_pair_boundary_graft A G)"
  unfolding pp_b_root_unary_recombination_def
proof (intro impI)
  assume necessary:
      "\<forall>w. w \<in> F (pp_b_pair_boundary_graft A G)"
  have view:
      "pp_b_view [True] (F (pp_b_pair_boundary_graft A G))
        = F G"
    using equivariant
    unfolding pp_b_equivariant_def
    by simp
  have G_necessary: "\<forall>u. u \<in> F G"
  proof
    fix u
    have
        "u \<in> pp_b_view [True]
          (F (pp_b_pair_boundary_graft A G))"
      using necessary[rule_format, of "[True] @ u"]
      unfolding pp_b_view_def by simp
    then show "u \<in> F G"
      unfolding view .
  qed
  show "\<forall>P. [] \<in> F P"
    using generic G_necessary
    unfolding pp_b_root_unary_recombination_def
    by blast
qed

corollary pp_b_pair_boundary_graft_recombines_for_stock:
  assumes generic:
      "\<And>F. F \<in> Stock
        \<Longrightarrow> pp_b_root_unary_recombination F G"
    and equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_b_equivariant F"
  shows
    "\<And>F. F \<in> Stock
      \<Longrightarrow>
      pp_b_root_unary_recombination F
        (pp_b_pair_boundary_graft A G)"
  using pp_b_pair_boundary_graft_recombination
    generic equivariant by blast

theorem pp_t_pair_boundary_graft_recombines_for_represented_stock:
  fixes D :: "ZF set"
  assumes D_domain:
      "\<And>d. d \<in> D
        \<Longrightarrow> Elem d
          (pp_t_domain pp_t_one_context_unary_type)"
    and represented:
      "\<And>X.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S [] X
        \<Longrightarrow> \<exists>d \<in> D.
          pp_t_eqv pp_t_one_context_unary_type [] X d"
    and equivariant:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    and generic:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_root_unary_recombination
          (pp_b_operator_of d) G"
  shows
    "pp_t_unary_recombines_at S
      (pp_zf_of_b (pp_b_pair_boundary_graft A G)) []"
  unfolding pp_t_unary_recombines_at_def
proof (intro allI impI)
  fix X q
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and X_stock: "S [] X"
    and necessary:
      "\<forall>v. prefix [] v \<longrightarrow>
        pp_t_holds
          (X \<acute> pp_zf_of_b (pp_b_pair_boundary_graft A G)) v"
    and q: "Elem q (pp_t_domain Prop)"
  obtain d where dD: "d \<in> D"
    and Xd:
      "pp_t_eqv pp_t_one_context_unary_type [] X d"
    using represented[OF X X_stock] by blast
  have d:
      "Elem d (pp_t_domain pp_t_one_context_unary_type)"
    by (rule D_domain[OF dD])
  have X_eq_d: "X = d"
    by (rule pp_t_root_eqv_imp_eq[OF X d Xd])
  have d_necessary:
      "\<forall>v.
        pp_t_holds
          (d \<acute> pp_zf_of_b (pp_b_pair_boundary_graft A G)) v"
    using necessary unfolding X_eq_d by simp
  have graft_recombines:
      "pp_b_root_unary_recombination
        (pp_b_operator_of d) (pp_b_pair_boundary_graft A G)"
    by (rule pp_b_pair_boundary_graft_recombination[
      OF equivariant[OF dD] generic[OF dD]])
  have universal_d:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (d \<acute> q) []"
    by (rule pp_b_recombination_transfers_to_zf[
      OF graft_recombines d_necessary])
  show "pp_t_holds (X \<acute> q) []"
    using universal_d q unfolding X_eq_d by blast
qed

section \<open>The graft is a fundamental boundary for its left cone\<close>

definition pp_t_pair_boundary_graft :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_pair_boundary_graft a g =
    pp_zf_of_b
      (pp_b_pair_boundary_graft (pp_b_of_zf a) (pp_b_of_zf g))"

lemma pp_t_pair_boundary_graft_in_domain:
  "Elem (pp_t_pair_boundary_graft a g) (pp_t_domain Prop)"
  unfolding pp_t_pair_boundary_graft_def
  by (rule pp_zf_of_b_in_domain)

lemma pp_t_zf_of_b_eqv_iff_views:
  "pp_t_eqv Prop s (pp_zf_of_b P) (pp_zf_of_b Q)
    \<longleftrightarrow>
   pp_b_view s P = pp_b_view s Q"
proof
  assume equivalent:
      "pp_t_eqv Prop s (pp_zf_of_b P) (pp_zf_of_b Q)"
  show "pp_b_view s P = pp_b_view s Q"
  proof (rule set_eqI)
    fix u
    have future: "prefix s (s @ u)" by simp
    show "u \<in> pp_b_view s P
        \<longleftrightarrow> u \<in> pp_b_view s Q"
      using equivalent future
      unfolding pp_t_eqv.simps pp_b_view_def
      by simp
  qed
next
  assume views: "pp_b_view s P = pp_b_view s Q"
  show "pp_t_eqv Prop s (pp_zf_of_b P) (pp_zf_of_b Q)"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix s z"
    obtain u where z: "z = s @ u"
      using future unfolding prefix_def by blast
    have member:
        "(u \<in> pp_b_view s P) = (u \<in> pp_b_view s Q)"
      using arg_cong[OF views, of "\<lambda>X. u \<in> X"] .
    show "pp_t_holds (pp_zf_of_b P) z
        = pp_t_holds (pp_zf_of_b Q) z"
      using member
      unfolding z
      by (simp add: pp_b_view_def)
  qed
qed

corollary pp_t_zf_of_b_locally_distinct_iff:
  "pp_b_locally_distinct P Q
    \<longleftrightarrow>
   (\<forall>s.
      \<not> pp_t_eqv Prop s (pp_zf_of_b P) (pp_zf_of_b Q))"
  unfolding pp_b_locally_distinct_def
  using pp_t_zf_of_b_eqv_iff_views by blast

lemma pp_t_cone_lift_eqv_iff_relative_view:
  "pp_t_eqv Prop (w @ u) (pp_t_cone_lift w s) p
    \<longleftrightarrow>
   pp_t_eqv Prop u s (pp_t_cone_view w p)"
proof
  assume left:
      "pp_t_eqv Prop (w @ u) (pp_t_cone_lift w s) p"
  show "pp_t_eqv Prop u s (pp_t_cone_view w p)"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume uz: "prefix u z"
    have future: "prefix (w @ u) (w @ z)"
      using uz unfolding prefix_def
      by (auto simp: append_assoc)
    have equality:
        "pp_t_holds (pp_t_cone_lift w s) (w @ z)
          = pp_t_holds p (w @ z)"
      using left future unfolding pp_t_eqv.simps by blast
    show "pp_t_holds s z
        = pp_t_holds (pp_t_cone_view w p) z"
      using equality
      by (simp add: pp_t_cone_lift_holds)
  qed
next
  assume right:
      "pp_t_eqv Prop u s (pp_t_cone_view w p)"
  show "pp_t_eqv Prop (w @ u) (pp_t_cone_lift w s) p"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix (w @ u) z"
    obtain t where z: "z = (w @ u) @ t"
      using future unfolding prefix_def by blast
    have ut: "prefix u (u @ t)" by simp
    have equality:
        "pp_t_holds s (u @ t)
          = pp_t_holds (pp_t_cone_view w p) (u @ t)"
      using right ut unfolding pp_t_eqv.simps by blast
    show "pp_t_holds (pp_t_cone_lift w s) z
        = pp_t_holds p z"
      using equality
      unfolding z
      by (simp add: pp_t_cone_lift_holds append_assoc)
  qed
qed

lemma pp_t_fundamental_boundary_transports_from_relative_cone:
  assumes p: "Elem p (pp_t_domain Prop)"
    and local:
      "pp_t_fundamental_boundary s []
        (pp_t_cone_view w p)"
  shows
    "pp_t_fundamental_boundary (pp_t_cone_lift w s) w p"
proof -
  have local_target:
      "Elem (pp_t_cone_view w p) (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have not_local:
      "\<not> pp_t_eqv Prop [] s (pp_t_cone_view w p)"
    using local
    unfolding pp_t_fundamental_boundary_def by blast
  obtain u where recovered:
      "pp_t_eqv Prop u s (pp_t_cone_view w p)"
    using local
    unfolding pp_t_fundamental_boundary_def by blast
  have not_world:
      "\<not> pp_t_eqv Prop w (pp_t_cone_lift w s) p"
    using not_local
      pp_t_cone_lift_eqv_iff_relative_view[
        of w "[]" s p]
    by simp
  have recovered_world:
      "pp_t_eqv Prop (w @ u) (pp_t_cone_lift w s) p"
    using recovered
      pp_t_cone_lift_eqv_iff_relative_view[
        of w u s p]
    by blast
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem p (pp_t_domain Prop)" by (rule p)
    show "\<not> pp_t_eqv Prop w (pp_t_cone_lift w s) p"
      by (rule not_world)
    show
        "\<exists>v. prefix w v
          \<and> pp_t_eqv Prop v (pp_t_cone_lift w s) p"
      using recovered_world
      by (intro exI[of _ "w @ u"]) simp
  qed
qed

lemma pp_t_local_distinctness_transports_to_future_cone:
  assumes local:
      "\<And>u. \<not> pp_t_eqv Prop u s (pp_t_cone_view w p)"
    and wx: "prefix w x"
  shows
    "\<not> pp_t_eqv Prop x (pp_t_cone_lift w s) p"
proof -
  obtain u where x: "x = w @ u"
    using wx unfolding prefix_def by blast
  show ?thesis
    using local[of u]
      pp_t_cone_lift_eqv_iff_relative_view[
        of w u s p]
    unfolding x by blast
qed

theorem pp_t_pair_boundary_graft_is_boundary:
  assumes a: "Elem a (pp_t_domain Prop)"
  shows
    "pp_t_fundamental_boundary
      (pp_t_pair_boundary_graft a g) [] a"
proof -
  let ?A = "pp_b_of_zf a"
  let ?G = "pp_b_of_zf g"
  let ?S = "pp_t_pair_boundary_graft a g"
  have exact: "pp_zf_of_b ?A = a"
    by (rule pp_zf_of_b_of_zf[OF a])
  have not_equivalent: "\<not> pp_t_eqv Prop [] ?S a"
  proof
    assume equivalent: "pp_t_eqv Prop [] ?S a"
    have at_root:
        "pp_t_holds ?S [] = pp_t_holds a []"
      using pp_t_prop_eqv_at[OF equivalent, of "[]"] by simp
    show False
      using at_root
      unfolding pp_t_pair_boundary_graft_def
        pp_b_of_zf_def
      by simp
  qed
  have recovered_raw:
      "pp_t_eqv Prop [False] ?S (pp_zf_of_b ?A)"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix z
    assume future: "prefix [False] z"
    obtain u where z: "z = [False] @ u"
      using future unfolding prefix_def by blast
    show "pp_t_holds ?S z = pp_t_holds (pp_zf_of_b ?A) z"
      unfolding z pp_t_pair_boundary_graft_def
        pp_b_of_zf_def
      by (simp add: pp_b_pair_boundary_graft_def
        pp_b_view_def pp_b_lift_def)
  qed
  have recovered: "pp_t_eqv Prop [False] ?S a"
    using recovered_raw unfolding exact .
  show ?thesis
    unfolding pp_t_fundamental_boundary_def
  proof (intro conjI)
    show "Elem a (pp_t_domain Prop)" by (rule a)
    show "\<not> pp_t_eqv Prop [] ?S a"
      by (rule not_equivalent)
    show "\<exists>v. prefix [] v \<and> pp_t_eqv Prop v ?S a"
      using recovered by (intro exI[of _ "[False]"]) simp
  qed
qed

section \<open>The local three-way package\<close>

theorem pp_t_pair_boundary_graft_package:
  fixes D :: "ZF set"
  assumes D_domain:
      "\<And>d. d \<in> D
        \<Longrightarrow> Elem d
          (pp_t_domain pp_t_one_context_unary_type)"
    and represented:
      "\<And>X.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S [] X
        \<Longrightarrow> \<exists>d \<in> D.
          pp_t_eqv pp_t_one_context_unary_type [] X d"
    and equivariant:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    and generic:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_root_unary_recombination
          (pp_b_operator_of d) G"
    and root_distinct:
      "pp_b_pair_boundary_graft A G \<noteq> B"
    and left_distinct:
      "pp_b_locally_distinct
        (pp_b_view [False] A) (pp_b_view [False] B)"
    and right_distinct:
      "pp_b_locally_distinct G (pp_b_view [True] B)"
  shows
    "\<exists>s.
      Elem s (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at S s []
      \<and> pp_t_fundamental_boundary s [] (pp_zf_of_b A)
      \<and> (\<forall>u.
        \<not> pp_t_eqv Prop u s (pp_zf_of_b B))"
proof -
  let ?S = "pp_b_pair_boundary_graft A G"
  let ?s = "pp_zf_of_b ?S"
  have s: "Elem ?s (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have recombines: "pp_t_unary_recombines_at S ?s []"
    by (rule
      pp_t_pair_boundary_graft_recombines_for_represented_stock[
        OF D_domain represented equivariant generic])
  have graft_eq:
      "pp_t_pair_boundary_graft (pp_zf_of_b A) (pp_zf_of_b G)
        = ?s"
    unfolding pp_t_pair_boundary_graft_def by simp
  have boundary_raw:
      "pp_t_fundamental_boundary
        (pp_t_pair_boundary_graft (pp_zf_of_b A) (pp_zf_of_b G))
        [] (pp_zf_of_b A)"
    by (rule pp_t_pair_boundary_graft_is_boundary[
      OF pp_zf_of_b_in_domain])
  have boundary:
      "pp_t_fundamental_boundary ?s [] (pp_zf_of_b A)"
    using boundary_raw unfolding graft_eq .
  have locally_distinct:
      "pp_b_locally_distinct ?S B"
    by (rule pp_b_pair_boundary_graft_locally_distinct[
      OF root_distinct left_distinct right_distinct])
  have unreachable:
      "\<forall>u. \<not> pp_t_eqv Prop u ?s (pp_zf_of_b B)"
    using locally_distinct
      pp_t_zf_of_b_locally_distinct_iff[of ?S B]
    by blast
  show ?thesis
    using s recombines boundary unreachable by blast
qed

theorem pp_t_world_relative_pair_boundary_graft_package:
  fixes D :: "ZF set"
  assumes a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and D_domain:
      "\<And>d. d \<in> D
        \<Longrightarrow> Elem d
          (pp_t_domain pp_t_one_context_unary_type)"
    and represented:
      "\<And>X.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> S [] X
        \<Longrightarrow> \<exists>d \<in> D.
          pp_t_eqv pp_t_one_context_unary_type [] X d"
    and equivariant:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    and generic:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_root_unary_recombination
          (pp_b_operator_of d) G"
    and cone_stock:
      "\<And>s u X Y.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_one_context_unary_type s X Y
        \<Longrightarrow>
        (S (s @ u) X \<longleftrightarrow> S u Y)"
    and root_distinct:
      "pp_b_pair_boundary_graft
          (pp_b_of_zf (pp_t_cone_view w a)) G
        \<noteq>
       pp_b_of_zf (pp_t_cone_view w b)"
    and left_distinct:
      "pp_b_locally_distinct
        (pp_b_view [False]
          (pp_b_of_zf (pp_t_cone_view w a)))
        (pp_b_view [False]
          (pp_b_of_zf (pp_t_cone_view w b)))"
    and right_distinct:
      "pp_b_locally_distinct G
        (pp_b_view [True]
          (pp_b_of_zf (pp_t_cone_view w b)))"
  shows
    "\<exists>r.
      Elem r (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at S r w
      \<and> pp_t_fundamental_boundary r w a
      \<and> (\<forall>x. prefix w x
        \<longrightarrow> \<not> pp_t_eqv Prop x r b)"
proof -
  let ?A = "pp_b_of_zf (pp_t_cone_view w a)"
  let ?B = "pp_b_of_zf (pp_t_cone_view w b)"
  obtain s where s: "Elem s (pp_t_domain Prop)"
    and root_recombines: "pp_t_unary_recombines_at S s []"
    and local_boundary:
      "pp_t_fundamental_boundary s [] (pp_zf_of_b ?A)"
    and local_distinct:
      "\<forall>u. \<not> pp_t_eqv Prop u s (pp_zf_of_b ?B)"
    using pp_t_pair_boundary_graft_package[
      OF D_domain represented equivariant generic
        root_distinct left_distinct right_distinct]
    by blast
  have A_exact:
      "pp_zf_of_b ?A = pp_t_cone_view w a"
    by (rule pp_zf_of_b_of_zf[OF pp_t_cone_view_in_domain])
  have B_exact:
      "pp_zf_of_b ?B = pp_t_cone_view w b"
    by (rule pp_zf_of_b_of_zf[OF pp_t_cone_view_in_domain])
  let ?r = "pp_t_cone_lift w s"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_cone_lift_in_domain)
  have recombines: "pp_t_unary_recombines_at S ?r w"
    by (rule pp_t_unary_stock_root_recombination_transports_to_cone[
      OF s root_recombines cone_stock])
  have boundary: "pp_t_fundamental_boundary ?r w a"
    by (rule pp_t_fundamental_boundary_transports_from_relative_cone[
      OF a])
      (use local_boundary in \<open>simp add: A_exact\<close>)
  have unreachable:
      "\<forall>x. prefix w x
        \<longrightarrow> \<not> pp_t_eqv Prop x ?r b"
  proof (intro allI impI)
    fix x
    assume wx: "prefix w x"
    have local:
        "\<And>u.
          \<not> pp_t_eqv Prop u s (pp_t_cone_view w b)"
      using local_distinct unfolding B_exact by blast
    show "\<not> pp_t_eqv Prop x ?r b"
      by (rule pp_t_local_distinctness_transports_to_future_cone[
        OF local wx])
  qed
  show ?thesis
    using r recombines boundary unreachable by blast
qed

section \<open>From a graft package to a generated-section distinction\<close>

abbreviation pp_t_generated_full_section ::
    "(bool list \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_generated_full_section R F \<equiv>
    pp_t_unary_output_disjunction
      (pp_t_recurrent_modal_component F)
      (pp_t_moving_boundary_operator_probe R \<acute> F)"

lemma pp_t_generated_full_section_in_domain:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
  shows
    "Elem (pp_t_generated_full_section R F)
      (pp_t_domain pp_t_one_context_unary_type)"
  by (rule pp_t_unary_output_disjunction_in_domain[
    OF pp_t_recurrent_modal_component_in_domain[OF F]
      pp_t_app_closed[
        OF pp_t_moving_boundary_operator_probe_in_domain F]])

lemma pp_t_generated_full_section_holds_iff:
  assumes R: "Elem (R w) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds (pp_t_generated_full_section R F \<acute> p) w
      \<longleftrightarrow>
     pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))
      \<or>
     pp_t_fundamental_boundary (R w) w (F \<acute> p)"
proof -
  let ?X = "pp_t_recurrent_modal_component F"
  let ?B = "pp_t_moving_boundary_operator_probe R \<acute> F"
  have X:
      "Elem ?X (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_recurrent_modal_component_in_domain[OF F])
  have B:
      "Elem ?B (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_moving_boundary_operator_probe_in_domain F])
  have component:
      "pp_t_holds (?X \<acute> p) w
        \<longleftrightarrow>
       pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))"
    by (rule pp_t_modal_singleton_operator_probe_apply_holds[OF F p])
  have boundary:
      "pp_t_holds (?B \<acute> p) w
        \<longleftrightarrow>
       pp_t_fundamental_boundary (R w) w (F \<acute> p)"
    by (rule pp_t_moving_boundary_operator_probe_apply_holds[
      where R=R and w=w and F=F and p=p,
      OF R F p])
  show ?thesis
    using pp_t_unary_output_disjunction_apply_holds[
      OF X B p, of w]
      component boundary by blast
qed

lemma pp_t_modal_singleton_impure_if_fundamental_omits:
  assumes r: "Elem r (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and recombines:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock r w"
    and unreachable:
      "\<And>v. prefix w v
        \<Longrightarrow> \<not> pp_t_eqv Prop v r p"
  shows
    "\<not> pp_t_probe_modal_boolean_stock w
      (pp_t_singleton_family_at p)"
proof
  let ?S = "pp_t_singleton_family_at p"
  assume singleton:
      "pp_t_probe_modal_boolean_stock w ?S"
  have S:
      "Elem ?S (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF p])
  have complement:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_pointwise_complement ?S)"
    unfolding pp_t_pointwise_complement_eq_unary_complement
    by (rule
      pp_t_probe_modal_boolean_stock_unary_complement_closed[
        OF S singleton])
  obtain v where wv: "prefix w v"
    and reached: "pp_t_eqv Prop v r p"
    using pp_t_pure_singleton_parameter_must_reach_fundamental[
      OF r p singleton complement recombines]
    by blast
  show False using unreachable[OF wv] reached by blast
qed

theorem pp_t_generated_sections_distinguished_by_boundary_and_omission:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and wv: "prefix w v"
    and recombines:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock (R v) v"
    and G_boundary:
      "pp_t_fundamental_boundary (R v) v (G \<acute> p)"
    and F_omitted:
      "\<And>x. prefix v x
        \<Longrightarrow> \<not> pp_t_eqv Prop x (R v) (F \<acute> p)"
  shows
    "\<exists>x. prefix w x
      \<and> \<not> pp_t_holds
        (pp_t_generated_full_section R F \<acute> p) x
      \<and> pp_t_holds
        (pp_t_generated_full_section R G \<acute> p) x"
proof -
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have F_impure:
      "\<not> pp_t_probe_modal_boolean_stock v
        (pp_t_singleton_family_at (F \<acute> p))"
    by (rule pp_t_modal_singleton_impure_if_fundamental_omits[
      OF R Fp recombines F_omitted])
  have F_not_boundary:
      "\<not> pp_t_fundamental_boundary (R v) v (F \<acute> p)"
  proof
    assume boundary:
        "pp_t_fundamental_boundary (R v) v (F \<acute> p)"
    obtain x where vx: "prefix v x"
      and reached:
        "pp_t_eqv Prop x (R v) (F \<acute> p)"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    show False using F_omitted[OF vx] reached by blast
  qed
  have F_false:
      "\<not> pp_t_holds
        (pp_t_generated_full_section R F \<acute> p) v"
    using pp_t_generated_full_section_holds_iff[
      where R=R and w=v and F=F and p=p,
      OF R F p]
      F_impure F_not_boundary by blast
  have G_true:
      "pp_t_holds
        (pp_t_generated_full_section R G \<acute> p) v"
    using pp_t_generated_full_section_holds_iff[
      where R=R and w=v and F=G and p=p,
      OF R G p]
      G_boundary by blast
  show ?thesis
    using wv F_false G_true
    by (intro exI[of _ v]) blast
qed

theorem
    pp_t_generated_mixed_disjunction_safe_if_boundary_and_omission:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and wv: "prefix w v"
    and recombines:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock (R v) v"
    and G_boundary:
      "pp_t_fundamental_boundary (R v) v (G \<acute> p)"
    and F_omitted:
      "\<And>x. prefix v x
        \<Longrightarrow> \<not> pp_t_eqv Prop x (R v) (F \<acute> p)"
  shows
    "pp_t_recombination_safe_unary_operator
      (pp_t_unary_output_disjunction
        (pp_t_generated_full_section R F)
        (pp_t_pointwise_complement
          (pp_t_generated_full_section R G)))
      p w"
proof -
  let ?SF = "pp_t_generated_full_section R F"
  let ?SG = "pp_t_generated_full_section R G"
  obtain x where wx: "prefix w x"
    and F_false: "\<not> pp_t_holds (?SF \<acute> p) x"
    and G_true: "pp_t_holds (?SG \<acute> p) x"
    using
      pp_t_generated_sections_distinguished_by_boundary_and_omission[
        where R=R and F=F and G=G and p=p and w=w and v=v,
        OF R F G p wv recombines G_boundary F_omitted]
    by blast
  have transport:
      "pp_t_operator_distinction_transport ?SF ?SG p w"
    unfolding pp_t_operator_distinction_transport_def
    using wx F_false G_true by blast
  have joint:
      "pp_t_joint_operator_antipatching
        ?SF (pp_t_pointwise_complement ?SG) p w"
    using pp_t_mixed_joint_antipatching_iff_distinction_transport[
      OF p, of ?SF ?SG w]
      transport by blast
  have SF:
      "Elem ?SF (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_generated_full_section_in_domain[OF F])
  have SG:
      "Elem ?SG (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_generated_full_section_in_domain[OF G])
  have NSG:
      "Elem (pp_t_pointwise_complement ?SG)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF SG])
  show ?thesis
    using pp_t_disjunction_recombination_safe_iff_joint_antipatching[
      OF SF NSG p]
      joint by blast
qed

theorem pp_t_grafted_mixed_generated_disjunction_exists:
  fixes D :: "ZF set"
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and wv: "prefix w v"
    and D_domain:
      "\<And>d. d \<in> D
        \<Longrightarrow> Elem d
          (pp_t_domain pp_t_one_context_unary_type)"
    and represented:
      "\<And>X.
        Elem X (pp_t_domain pp_t_one_context_unary_type)
        \<Longrightarrow> pp_t_probe_modal_boolean_stock [] X
        \<Longrightarrow> \<exists>d \<in> D.
          pp_t_eqv pp_t_one_context_unary_type [] X d"
    and equivariant:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_equivariant (pp_b_operator_of d)"
    and generic:
      "\<And>d. d \<in> D
        \<Longrightarrow> pp_b_root_unary_recombination
          (pp_b_operator_of d) H"
    and root_distinct:
      "pp_b_pair_boundary_graft
          (pp_b_of_zf (pp_t_cone_view v (G \<acute> p))) H
        \<noteq>
       pp_b_of_zf (pp_t_cone_view v (F \<acute> p))"
    and left_distinct:
      "pp_b_locally_distinct
        (pp_b_view [False]
          (pp_b_of_zf (pp_t_cone_view v (G \<acute> p))))
        (pp_b_view [False]
          (pp_b_of_zf (pp_t_cone_view v (F \<acute> p))))"
    and right_distinct:
      "pp_b_locally_distinct H
        (pp_b_view [True]
          (pp_b_of_zf (pp_t_cone_view v (F \<acute> p))))"
  shows
    "\<exists>R.
      (\<forall>x. Elem (R x) (pp_t_domain Prop))
      \<and> pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock (R v) v
      \<and> pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R F)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R G)))
        p w"
proof -
  have Fp: "Elem (F \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have Gp: "Elem (G \<acute> p) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF G p])
  obtain r where r: "Elem r (pp_t_domain Prop)"
    and recombines:
      "pp_t_unary_recombines_at
        pp_t_probe_modal_boolean_stock r v"
    and G_boundary:
      "pp_t_fundamental_boundary r v (G \<acute> p)"
    and F_omitted:
      "\<forall>x. prefix v x
        \<longrightarrow> \<not> pp_t_eqv Prop x r (F \<acute> p)"
    using pp_t_world_relative_pair_boundary_graft_package[
      where D=D and S=pp_t_probe_modal_boolean_stock
        and G=H and w=v and a="G \<acute> p" and b="F \<acute> p",
      OF Gp Fp D_domain represented equivariant generic
        pp_t_probe_modal_boolean_stock_cone_iff
        root_distinct left_distinct right_distinct]
    by blast
  let ?R = "\<lambda>x. if x = v then r else pp_zf_truth False"
  have R: "\<And>x. Elem (?R x) (pp_t_domain Prop)"
    using r pp_t_truth_in_domain by simp
  have Rv: "?R v = r" by simp
  have safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section ?R F)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section ?R G)))
        p w"
    by (rule
      pp_t_generated_mixed_disjunction_safe_if_boundary_and_omission[
        where R="?R" and F=F and G=G and p=p and w=w and v=v,
        OF R F G p wv])
      (use recombines G_boundary F_omitted in
        \<open>simp_all add: Rv\<close>)
  show ?thesis
    by (intro exI[of _ ?R]) (use R recombines safe in simp)
qed

theorem pp_t_distinct_world_grafts_combine:
  fixes I :: "'i set"
    and V :: "'i \<Rightarrow> bool list"
    and seed :: "'i \<Rightarrow> ZF"
    and F :: "'i \<Rightarrow> ZF"
    and G :: "'i \<Rightarrow> ZF"
    and p :: "'i \<Rightarrow> ZF"
    and W :: "'i \<Rightarrow> bool list"
  assumes injective: "inj_on V I"
    and seed_domain:
      "\<And>i. Elem (seed i) (pp_t_domain Prop)"
    and F_domain:
      "\<And>i. i \<in> I
        \<Longrightarrow> Elem (F i)
          (pp_t_domain pp_t_one_context_unary_type)"
    and G_domain:
      "\<And>i. i \<in> I
        \<Longrightarrow> Elem (G i)
          (pp_t_domain pp_t_one_context_unary_type)"
    and p_domain:
      "\<And>i. i \<in> I
        \<Longrightarrow> Elem (p i) (pp_t_domain Prop)"
    and future:
      "\<And>i. i \<in> I \<Longrightarrow> prefix (W i) (V i)"
    and recombines:
      "\<And>i. i \<in> I
        \<Longrightarrow>
        pp_t_unary_recombines_at
          pp_t_probe_modal_boolean_stock (seed i) (V i)"
    and boundary:
      "\<And>i. i \<in> I
        \<Longrightarrow>
        pp_t_fundamental_boundary
          (seed i) (V i) (G i \<acute> p i)"
    and omitted:
      "\<And>i x. i \<in> I
        \<Longrightarrow> prefix (V i) x
        \<Longrightarrow>
        \<not> pp_t_eqv Prop x (seed i) (F i \<acute> p i)"
  shows
    "\<exists>R.
      (\<forall>x. Elem (R x) (pp_t_domain Prop))
      \<and> (\<forall>i \<in> I.
        pp_t_recombination_safe_unary_operator
          (pp_t_unary_output_disjunction
            (pp_t_generated_full_section R (F i))
            (pp_t_pointwise_complement
              (pp_t_generated_full_section R (G i))))
          (p i) (W i))"
proof -
  let ?R =
    "\<lambda>x.
      if x \<in> V ` I
      then seed (inv_into I V x)
      else pp_zf_truth False"
  have R_domain: "\<And>x. Elem (?R x) (pp_t_domain Prop)"
    using seed_domain pp_t_truth_in_domain by simp
  have R_at: "?R (V i) = seed i" if iI: "i \<in> I" for i
    using inv_into_f_f[OF injective iI] iI by simp
  have safe:
      "\<And>i. i \<in> I
        \<Longrightarrow>
        pp_t_recombination_safe_unary_operator
          (pp_t_unary_output_disjunction
            (pp_t_generated_full_section ?R (F i))
            (pp_t_pointwise_complement
              (pp_t_generated_full_section ?R (G i))))
          (p i) (W i)"
  proof -
    fix i
    assume iI: "i \<in> I"
    have recombines_i:
        "pp_t_unary_recombines_at
          pp_t_probe_modal_boolean_stock (?R (V i)) (V i)"
      using recombines[OF iI] R_at[OF iI] by simp
    have boundary_i:
        "pp_t_fundamental_boundary
          (?R (V i)) (V i) (G i \<acute> p i)"
      using boundary[OF iI] R_at[OF iI] by simp
    have omitted_i:
        "\<And>x. prefix (V i) x
          \<Longrightarrow>
          \<not> pp_t_eqv Prop x (?R (V i)) (F i \<acute> p i)"
      using omitted[OF iI] R_at[OF iI] by simp
    show
        "pp_t_recombination_safe_unary_operator
          (pp_t_unary_output_disjunction
            (pp_t_generated_full_section ?R (F i))
            (pp_t_pointwise_complement
              (pp_t_generated_full_section ?R (G i))))
          (p i) (W i)"
      by (rule
        pp_t_generated_mixed_disjunction_safe_if_boundary_and_omission[
          where R="?R" and F="F i" and G="G i"
            and p="p i" and w="W i" and v="V i",
          OF R_domain F_domain[OF iI] G_domain[OF iI]
            p_domain[OF iI] future[OF iI]
            recombines_i boundary_i omitted_i])
  qed
  show ?thesis
    by (intro exI[of _ ?R] conjI)
      (use R_domain safe in blast)+
qed

section \<open>Limits of independent pair grafting\<close>

definition pp_b_dense_stock_diagonal ::
    "pp_b_prop \<Rightarrow> (nat \<Rightarrow> pp_b_prop) \<Rightarrow> pp_b_prop"
where
  "pp_b_dense_stock_diagonal R B =
    {x.
      (\<exists>v. x = v @ [False, False])
      \<or>
      (\<exists>v. x = v @ [False, True] \<and> x \<notin> R)
      \<or>
      (\<exists>n. x = pp_b_code n @ [True, True] \<and> x \<notin> B n)}"

lemma pp_b_FF_not_FT:
  "v @ [False, False] \<noteq> u @ [False, True]"
proof
  assume equality: "v @ [False, False] = u @ [False, True]"
  have "rev (v @ [False, False]) = rev (u @ [False, True])"
    using equality by simp
  then show False by simp
qed

lemma pp_b_FF_not_TT:
  "v @ [False, False] \<noteq> u @ [True, True]"
proof
  assume equality: "v @ [False, False] = u @ [True, True]"
  have
      "rev (v @ [False, False]) = rev (u @ [True, True])"
    using equality by simp
  then show False by simp
qed

lemma pp_b_FT_not_TT:
  "v @ [False, True] \<noteq> u @ [True, True]"
proof
  assume equality: "v @ [False, True] = u @ [True, True]"
  have
      "rev (v @ [False, True]) = rev (u @ [True, True])"
    using equality by simp
  then show False by simp
qed

lemma pp_b_dense_stock_diagonal_FF[simp]:
  "v @ [False, False] \<in> pp_b_dense_stock_diagonal R B"
  unfolding pp_b_dense_stock_diagonal_def by blast

lemma pp_b_dense_stock_diagonal_FT[simp]:
  "v @ [False, True] \<in> pp_b_dense_stock_diagonal R B
    \<longleftrightarrow> v @ [False, True] \<notin> R"
proof -
  have no_FF:
      "\<nexists>u. v @ [False, True] = u @ [False, False]"
    by (metis pp_b_FF_not_FT)
  have no_TT:
      "\<nexists>u. v @ [False, True] = u @ [True, True]"
    by (metis pp_b_FT_not_TT)
  show ?thesis
    unfolding pp_b_dense_stock_diagonal_def
    using no_FF no_TT by blast
qed

lemma pp_b_dense_stock_diagonal_marker[simp]:
  "pp_b_code n @ [True, True]
      \<in> pp_b_dense_stock_diagonal R B
    \<longleftrightarrow>
   pp_b_code n @ [True, True] \<notin> B n"
proof -
  have no_FF:
      "\<nexists>u.
        pp_b_code n @ [True, True] = u @ [False, False]"
    by (metis pp_b_FF_not_TT)
  have no_FT:
      "\<nexists>u.
        pp_b_code n @ [True, True] = u @ [False, True]"
    by (metis pp_b_FT_not_TT)
  have marker_unique:
      "\<And>m. pp_b_code n @ [True, True]
          = pp_b_code m @ [True, True]
        \<longleftrightarrow> n = m"
    using pp_b_code_append_eq by blast
  show ?thesis
    unfolding pp_b_dense_stock_diagonal_def
  proof
    assume member:
        "pp_b_code n @ [True, True]
          \<in>
          {x.
            (\<exists>v. x = v @ [False, False])
            \<or>
            (\<exists>v. x = v @ [False, True] \<and> x \<notin> R)
            \<or>
            (\<exists>m.
              x = pp_b_code m @ [True, True] \<and> x \<notin> B m)}"
    then obtain m where equality:
        "pp_b_code n @ [True, True]
          = pp_b_code m @ [True, True]"
      and omitted:
        "pp_b_code n @ [True, True] \<notin> B m"
      using no_FF no_FT by blast
    have "m = n"
      using marker_unique[of m] equality by simp
    then show "pp_b_code n @ [True, True] \<notin> B n"
      using omitted by simp
  next
    assume omitted:
        "pp_b_code n @ [True, True] \<notin> B n"
    show
        "pp_b_code n @ [True, True]
          \<in>
          {x.
            (\<exists>v. x = v @ [False, False])
            \<or>
            (\<exists>v. x = v @ [False, True] \<and> x \<notin> R)
            \<or>
            (\<exists>m.
              x = pp_b_code m @ [True, True] \<and> x \<notin> B m)}"
      using omitted by blast
  qed
qed

theorem pp_b_dense_stock_diagonal_is_dense:
  "\<exists>u. prefix v u
    \<and> u \<in> pp_b_dense_stock_diagonal R B"
proof (intro exI[of _ "v @ [False, False]"] conjI)
  show "prefix v (v @ [False, False])"
    by simp
  show "v @ [False, False] \<in> pp_b_dense_stock_diagonal R B"
    by simp
qed

theorem pp_b_dense_stock_diagonal_locally_distinct:
  "pp_b_locally_distinct
    (pp_b_dense_stock_diagonal R B) R"
  unfolding pp_b_locally_distinct_def
proof
  fix v
  have different:
      "v @ [False, True]
          \<in> pp_b_dense_stock_diagonal R B
        \<longleftrightarrow>
       v @ [False, True] \<notin> R"
    by simp
  show
      "pp_b_view v (pp_b_dense_stock_diagonal R B)
        \<noteq> pp_b_view v R"
  proof
    assume equality:
        "pp_b_view v (pp_b_dense_stock_diagonal R B)
          = pp_b_view v R"
    have
        "[False, True]
            \<in> pp_b_view v (pp_b_dense_stock_diagonal R B)
          \<longleftrightarrow>
         [False, True] \<in> pp_b_view v R"
      using equality by simp
    then show False
      using different
      by (simp add: pp_b_view_def)
  qed
qed

theorem pp_b_dense_stock_diagonal_avoids_sequence:
  "pp_b_dense_stock_diagonal R B \<noteq> B n"
proof
  assume equality: "pp_b_dense_stock_diagonal R B = B n"
  have
      "pp_b_code n @ [True, True]
          \<in> pp_b_dense_stock_diagonal R B
        \<longleftrightarrow>
       pp_b_code n @ [True, True] \<in> B n"
    using equality by simp
  then show False by simp
qed

theorem pp_t_dense_stock_diagonal_package:
  assumes r: "Elem r (pp_t_domain Prop)"
    and covers:
      "\<And>P.
        pp_t_probe_modal_boolean_stock w
          (pp_t_singleton_family_at (pp_zf_of_b P))
        \<Longrightarrow> \<exists>n. P = B n"
  defines
    "D \<equiv> pp_b_dense_stock_diagonal (pp_b_of_zf r) B"
    and
      "p \<equiv>
        pp_zf_of_b
          (pp_b_dense_stock_diagonal (pp_b_of_zf r) B)"
  shows
    "Elem p (pp_t_domain Prop)
    \<and>
     (\<forall>v.
       prefix w v
       \<longrightarrow> (\<exists>u. prefix v u \<and> pp_t_holds p u))
    \<and>
     \<not> pp_t_probe_modal_boolean_stock w
       (pp_t_singleton_family_at p)
    \<and>
     \<not> pp_t_fundamental_boundary r w p"
proof -
  have p_domain: "Elem p (pp_t_domain Prop)"
    unfolding p_def by (rule pp_zf_of_b_in_domain)
  have dense:
      "\<forall>v.
        prefix w v
        \<longrightarrow> (\<exists>u. prefix v u \<and> pp_t_holds p u)"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    obtain u where vu: "prefix v u"
      and uD: "u \<in> D"
      unfolding D_def
      using pp_b_dense_stock_diagonal_is_dense[
        where v=v and R="pp_b_of_zf r" and B=B]
      by blast
    have pu: "pp_t_holds p u"
      using uD unfolding p_def D_def by simp
    show "\<exists>u. prefix v u \<and> pp_t_holds p u"
      using vu pu by blast
  qed
  have impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at p)"
  proof
    assume pure:
        "pp_t_probe_modal_boolean_stock w
          (pp_t_singleton_family_at p)"
    obtain n where equality: "D = B n"
      using covers[where P=D]
      pure unfolding p_def D_def by blast
    have avoided: "D \<noteq> B n"
      unfolding D_def
      by (rule pp_b_dense_stock_diagonal_avoids_sequence)
    show False
      using equality avoided by blast
  qed
  have r_exact: "pp_zf_of_b (pp_b_of_zf r) = r"
    by (rule pp_zf_of_b_of_zf[OF r])
  have local_sets:
      "pp_b_locally_distinct D (pp_b_of_zf r)"
    unfolding D_def
    by (rule pp_b_dense_stock_diagonal_locally_distinct)
  have local:
      "\<And>s. \<not> pp_t_eqv Prop s p r"
    using pp_t_zf_of_b_locally_distinct_iff[
      where P=D and Q="pp_b_of_zf r"]
      local_sets
    unfolding p_def D_def r_exact by blast
  have not_boundary:
      "\<not> pp_t_fundamental_boundary r w p"
  proof
    assume boundary: "pp_t_fundamental_boundary r w p"
    obtain v where wp: "prefix w v"
      and equivalent: "pp_t_eqv Prop v r p"
      using boundary
      unfolding pp_t_fundamental_boundary_def by blast
    have reverse: "pp_t_eqv Prop v p r"
      by (rule pp_t_eqv_symmetric[OF r p_domain equivalent])
    show False using local[of v] reverse by blast
  qed
  show ?thesis
    using p_domain dense impure not_boundary by blast
qed

definition pp_b_root_modal_singleton_parameters :: "pp_b_prop set"
where
  "pp_b_root_modal_singleton_parameters =
    {P.
      pp_t_probe_modal_boolean_stock []
        (pp_t_singleton_family_at (pp_zf_of_b P))}"

definition pp_b_singleton_parameter_family ::
    "pp_b_prop \<Rightarrow> ZF"
where
  "pp_b_singleton_parameter_family P =
    pp_t_singleton_family_at (pp_zf_of_b P)"

lemma pp_b_singleton_parameter_family_injective:
  "inj pp_b_singleton_parameter_family"
proof (rule injI)
  fix P Q
  assume families:
      "pp_b_singleton_parameter_family P
        = pp_b_singleton_parameter_family Q"
  have P: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have Q: "Elem (pp_zf_of_b Q) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have SP:
      "Elem (pp_t_singleton_family_at (pp_zf_of_b P))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF P])
  have SQ:
      "Elem (pp_t_singleton_family_at (pp_zf_of_b Q))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF Q])
  have direct:
      "pp_t_singleton_family_at (pp_zf_of_b P)
        = pp_t_singleton_family_at (pp_zf_of_b Q)"
    using families
    unfolding pp_b_singleton_parameter_family_def .
  have family_eqv:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_singleton_family_at (pp_zf_of_b P))
        (pp_t_singleton_family_at (pp_zf_of_b Q))"
    unfolding direct
    by (rule pp_t_eqv_reflexive[OF SQ])
  have parameter_eqv:
      "pp_t_eqv Prop [] (pp_zf_of_b P) (pp_zf_of_b Q)"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF P Q, of "[]"]
      family_eqv by blast
  have parameters: "pp_zf_of_b P = pp_zf_of_b Q"
    by (rule pp_t_root_eqv_imp_eq[OF P Q parameter_eqv])
  show "P = Q"
    using arg_cong[OF parameters, of pp_b_of_zf]
    by simp
qed

lemma pp_b_root_modal_singleton_parameter_families_subset:
  "pp_b_singleton_parameter_family `
      pp_b_root_modal_singleton_parameters
    \<subseteq> pp_t_probe_modal_boolean_representatives"
proof
  fix X
  assume
      "X \<in>
        pp_b_singleton_parameter_family `
          pp_b_root_modal_singleton_parameters"
  then obtain P where P:
      "P \<in> pp_b_root_modal_singleton_parameters"
    and X:
      "X = pp_b_singleton_parameter_family P"
    by blast
  have stock:
      "pp_t_probe_modal_boolean_stock []
        (pp_t_singleton_family_at (pp_zf_of_b P))"
    using P unfolding pp_b_root_modal_singleton_parameters_def
    by simp
  then obtain d where d:
      "d \<in> pp_t_probe_modal_boolean_representatives"
    and equivalent:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_singleton_family_at (pp_zf_of_b P)) d"
    unfolding pp_t_probe_modal_boolean_stock_def by blast
  have parameter: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  have singleton:
      "Elem (pp_t_singleton_family_at (pp_zf_of_b P))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF parameter])
  have d_domain:
      "Elem d (pp_t_domain pp_t_one_context_unary_type)"
    by (rule
      pp_t_probe_modal_boolean_representative_in_domain[OF d])
  have equality:
      "pp_t_singleton_family_at (pp_zf_of_b P) = d"
    by (rule pp_t_root_eqv_imp_eq[
      OF singleton d_domain equivalent])
  show "X \<in> pp_t_probe_modal_boolean_representatives"
    using X d equality
    unfolding pp_b_singleton_parameter_family_def by simp
qed

lemma pp_b_root_modal_singleton_parameters_countable:
  "countable pp_b_root_modal_singleton_parameters"
proof -
  have image_countable:
      "countable
        (pp_b_singleton_parameter_family `
          pp_b_root_modal_singleton_parameters)"
    by (rule countable_subset[
      OF pp_b_root_modal_singleton_parameter_families_subset
        pp_t_probe_modal_boolean_representatives_countable])
  have injective:
      "inj_on pp_b_singleton_parameter_family
        pp_b_root_modal_singleton_parameters"
    using pp_b_singleton_parameter_family_injective
    unfolding inj_def inj_on_def by blast
  show ?thesis
    by (rule countable_image_inj_on[
      where f=pp_b_singleton_parameter_family,
      OF image_countable injective])
qed

lemma pp_zf_of_b_UNIV:
  "pp_zf_of_b UNIV = pp_zf_truth True"
proof (rule pp_t_prop_ext)
  show "Elem (pp_zf_of_b UNIV) (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
  show "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  fix w
  show
      "pp_t_holds (pp_zf_of_b UNIV) w
        = pp_t_holds (pp_zf_truth True) w"
    by simp
qed

lemma pp_b_root_modal_singleton_parameters_nonempty:
  "pp_b_root_modal_singleton_parameters \<noteq> {}"
proof -
  have
      "pp_t_probe_modal_boolean_stock []
        (pp_t_singleton_family_at (pp_zf_of_b UNIV))"
    unfolding pp_zf_of_b_UNIV
    by (rule pp_t_modal_stock_contains_truth_singleton)
  then have
      "UNIV \<in> pp_b_root_modal_singleton_parameters"
    unfolding pp_b_root_modal_singleton_parameters_def by simp
  then show ?thesis by blast
qed

definition pp_b_root_modal_singleton_parameter_enumerator ::
    "nat \<Rightarrow> pp_b_prop"
where
  "pp_b_root_modal_singleton_parameter_enumerator =
    from_nat_into pp_b_root_modal_singleton_parameters"

lemma pp_b_root_modal_singleton_parameter_enumerator_range:
  "range pp_b_root_modal_singleton_parameter_enumerator
    = pp_b_root_modal_singleton_parameters"
  unfolding pp_b_root_modal_singleton_parameter_enumerator_def
  by (rule range_from_nat_into[
    OF pp_b_root_modal_singleton_parameters_nonempty
      pp_b_root_modal_singleton_parameters_countable])

lemma pp_b_root_modal_singleton_parameter_enumerator_covers:
  assumes
    "pp_t_probe_modal_boolean_stock []
      (pp_t_singleton_family_at (pp_zf_of_b P))"
  shows
    "\<exists>n.
      P = pp_b_root_modal_singleton_parameter_enumerator n"
proof -
  have "P \<in> pp_b_root_modal_singleton_parameters"
    using assms
    unfolding pp_b_root_modal_singleton_parameters_def by simp
  then have
      "P \<in> range pp_b_root_modal_singleton_parameter_enumerator"
    unfolding
      pp_b_root_modal_singleton_parameter_enumerator_range .
  then show ?thesis by blast
qed

lemma pp_b_not_box_not_root_universal:
  "\<not> (\<forall>P. [] \<in> pp_b_not_box P)"
proof
  assume universal: "\<forall>P. [] \<in> pp_b_not_box P"
  have "[] \<in> pp_b_not_box UNIV"
    using universal by blast
  then show False
    by (simp add: pp_b_not_box_def pp_b_box_def)
qed

theorem pp_b_not_box_recombination_forces_a_truth_cone:
  assumes recombines:
      "pp_b_root_unary_recombination pp_b_not_box H"
  shows "\<exists>s. pp_b_view s H = UNIV"
proof -
  have not_necessary:
      "\<not> (\<forall>w. w \<in> pp_b_not_box H)"
    using recombines pp_b_not_box_not_root_universal
    unfolding pp_b_root_unary_recombination_def by blast
  then obtain s where not_not_box:
      "s \<notin> pp_b_not_box H"
    by blast
  have box: "s \<in> pp_b_box H"
    using not_not_box
    unfolding pp_b_not_box_def by simp
  have view: "pp_b_view s H = UNIV"
    using box
    by (auto simp: pp_b_box_def pp_b_view_def)
  show ?thesis
    using view by blast
qed

corollary pp_b_not_box_recombination_precludes_local_distinctness_from_truth:
  assumes recombines:
      "pp_b_root_unary_recombination pp_b_not_box H"
  shows "\<not> pp_b_locally_distinct H UNIV"
proof -
  obtain s where view: "pp_b_view s H = UNIV"
    using pp_b_not_box_recombination_forces_a_truth_cone[
      OF recombines] by blast
  have "pp_b_view s H = pp_b_view s UNIV"
    using view by (simp add: pp_b_view_def)
  then show ?thesis
    unfolding pp_b_locally_distinct_def by blast
qed

theorem pp_t_mixed_disjunction_at_necessary_anchor_forces_implication:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and t: "Elem t (pp_t_domain Prop)"
    and X_necessary:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds (X \<acute> t) v"
    and safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          X (pp_t_pointwise_complement Y))
        t w"
  shows
    "\<And>q.
      Elem q (pp_t_domain Prop)
      \<Longrightarrow> pp_t_holds (Y \<acute> q) w
      \<Longrightarrow> pp_t_holds (X \<acute> q) w"
proof -
  have NY:
      "Elem (pp_t_pointwise_complement Y)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_pointwise_complement_in_domain[OF Y])
  have mixed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_t_holds
          (pp_t_unary_output_disjunction
            X (pp_t_pointwise_complement Y) \<acute> t) v"
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have Xt: "pp_t_holds (X \<acute> t) v"
      by (rule X_necessary[OF wv])
    show
        "pp_t_holds
          (pp_t_unary_output_disjunction
            X (pp_t_pointwise_complement Y) \<acute> t) v"
      using pp_t_unary_output_disjunction_apply_holds[
        OF X NY t, of v]
        Xt by blast
  qed
  have universal:
      "\<forall>q.
        Elem q (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_holds
          (pp_t_unary_output_disjunction
            X (pp_t_pointwise_complement Y) \<acute> q) w"
    using safe mixed_necessary
    unfolding pp_t_recombination_safe_unary_operator_def
    by blast
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
    and Yq: "pp_t_holds (Y \<acute> q) w"
  have mixed:
      "pp_t_holds
        (pp_t_unary_output_disjunction
          X (pp_t_pointwise_complement Y) \<acute> q) w"
    using universal q by blast
  have alternatives:
      "pp_t_holds (X \<acute> q) w
        \<or>
       pp_t_holds
        (pp_t_pointwise_complement Y \<acute> q) w"
    using pp_t_unary_output_disjunction_apply_holds[
      OF X NY q, of w]
      mixed by blast
  have complement:
      "pp_t_holds
        (pp_t_pointwise_complement Y \<acute> q) w
        \<longleftrightarrow>
       \<not> pp_t_holds (Y \<acute> q) w"
    by (rule pp_t_pointwise_complement_holds[OF q])
  show "pp_t_holds (X \<acute> q) w"
    using alternatives complement Yq by blast
qed

corollary
    pp_t_two_mixed_disjunctions_at_necessary_anchor_force_agreement:
  assumes X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and t: "Elem t (pp_t_domain Prop)"
    and X_necessary:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds (X \<acute> t) v"
    and Y_necessary:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds (Y \<acute> t) v"
    and XY_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          X (pp_t_pointwise_complement Y))
        t w"
    and YX_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          Y (pp_t_pointwise_complement X))
        t w"
  shows
    "\<And>q.
      Elem q (pp_t_domain Prop)
      \<Longrightarrow>
      (pp_t_holds (X \<acute> q) w
        \<longleftrightarrow> pp_t_holds (Y \<acute> q) w)"
proof -
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  have Y_if_X:
      "pp_t_holds (X \<acute> q) w
        \<Longrightarrow> pp_t_holds (Y \<acute> q) w"
    by (rule
      pp_t_mixed_disjunction_at_necessary_anchor_forces_implication[
        where X=Y and Y=X and t=t and w=w,
        OF Y X t Y_necessary YX_safe q])
  have X_if_Y:
      "pp_t_holds (Y \<acute> q) w
        \<Longrightarrow> pp_t_holds (X \<acute> q) w"
    by (rule
      pp_t_mixed_disjunction_at_necessary_anchor_forces_implication[
        where X=X and Y=Y and t=t and w=w,
        OF X Y t X_necessary XY_safe q])
  show
      "pp_t_holds (X \<acute> q) w
        \<longleftrightarrow> pp_t_holds (Y \<acute> q) w"
    using Y_if_X X_if_Y by blast
qed

lemma pp_t_generated_full_section_true_on_truth:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and preserves: "pp_t_preserves_truth_cones F"
  shows
    "pp_t_holds
      (pp_t_generated_full_section R F \<acute> pp_zf_truth True) w"
proof -
  let ?T = "pp_zf_truth True"
  have T: "Elem ?T (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have FT: "Elem (F \<acute> ?T) (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F T])
  have FT_truth:
      "pp_t_eqv Prop w (F \<acute> ?T) ?T"
    unfolding pp_t_prop_eqv_truth_iff
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have all_true:
        "\<forall>u. prefix w u \<longrightarrow> pp_t_holds ?T u"
      by simp
    show "pp_t_holds (F \<acute> ?T) v"
      using preserves T all_true wv
      unfolding pp_t_preserves_truth_cones_def by blast
  qed
  have SFT:
      "Elem (pp_t_singleton_family_at (F \<acute> ?T))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF FT])
  have ST:
      "Elem (pp_t_singleton_family_at ?T)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF T])
  have families:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at (F \<acute> ?T))
        (pp_t_singleton_family_at ?T)"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF FT T, of w]
      FT_truth by blast
  have truth_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?T)"
    by (rule pp_t_modal_stock_contains_truth_singleton)
  have FT_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> ?T))"
  proof -
    have reverse:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at ?T)
          (pp_t_singleton_family_at (F \<acute> ?T))"
      by (rule pp_t_eqv_symmetric[OF SFT ST families])
    show ?thesis
      using pp_t_probe_modal_boolean_stock_admissible
        ST SFT reverse truth_pure
      unfolding pp_t_predicate_admissible_def
      by blast
  qed
  show ?thesis
    using pp_t_generated_full_section_holds_iff[
      where R=R and w=w and F=F and p="?T",
      OF R F T]
      FT_pure by blast
qed

theorem
    pp_t_full_boolean_closure_forces_positive_modal_section_agreement:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
    and FG_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R F)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R G)))
        (pp_zf_truth True) w"
    and GF_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R G)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R F)))
        (pp_zf_truth True) w"
  shows
    "\<And>q.
      Elem q (pp_t_domain Prop)
      \<Longrightarrow>
      (pp_t_holds
          (pp_t_generated_full_section R F \<acute> q) w
        \<longleftrightarrow>
       pp_t_holds
          (pp_t_generated_full_section R G \<acute> q) w)"
proof -
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF F])
  have G_domain:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF G])
  let ?SF = "pp_t_generated_full_section R F"
  let ?SG = "pp_t_generated_full_section R G"
  have SF:
      "Elem ?SF (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_generated_full_section_in_domain[OF F_domain])
  have SG:
      "Elem ?SG (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_generated_full_section_in_domain[OF G_domain])
  have T: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have F_necessary:
      "\<And>v. prefix w v
        \<Longrightarrow> pp_t_holds (?SF \<acute> pp_zf_truth True) v"
    by (rule pp_t_generated_full_section_true_on_truth[
      OF R F_domain
        pp_t_positive_modal_normal_form_preserves_truth_cones[OF F]])
  have G_necessary:
      "\<And>v. prefix w v
        \<Longrightarrow> pp_t_holds (?SG \<acute> pp_zf_truth True) v"
    by (rule pp_t_generated_full_section_true_on_truth[
      OF R G_domain
        pp_t_positive_modal_normal_form_preserves_truth_cones[OF G]])
  show
    "\<And>q.
      Elem q (pp_t_domain Prop)
      \<Longrightarrow>
      (pp_t_holds (?SF \<acute> q) w
        \<longleftrightarrow> pp_t_holds (?SG \<acute> q) w)"
    by (rule
      pp_t_two_mixed_disjunctions_at_necessary_anchor_force_agreement[
        where X="?SF" and Y="?SG" and t="pp_zf_truth True" and w=w,
        OF SF SG T F_necessary G_necessary FG_safe GF_safe])
qed

lemma pp_t_generated_section_agreement_forces_boundary_absorption:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and G: "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
    and agreement:
      "pp_t_holds (pp_t_generated_full_section R F \<acute> p) w
        \<longleftrightarrow>
       pp_t_holds (pp_t_generated_full_section R G \<acute> p) w"
    and F_impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))"
    and G_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (G \<acute> p))"
  shows
    "pp_t_fundamental_boundary (R w) w (F \<acute> p)"
proof -
  have G_true:
      "pp_t_holds (pp_t_generated_full_section R G \<acute> p) w"
    using pp_t_generated_full_section_holds_iff[
      where R=R and w=w and F=G and p=p,
      OF R G p]
      G_pure by blast
  have F_true:
      "pp_t_holds (pp_t_generated_full_section R F \<acute> p) w"
    using agreement G_true by blast
  show ?thesis
    using pp_t_generated_full_section_holds_iff[
      where R=R and w=w and F=F and p=p,
      OF R F p]
      F_true F_impure by blast
qed

corollary
    pp_t_full_boolean_closure_forces_positive_modal_boundary_absorption:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and F: "pp_t_positive_modal_normal_form F"
    and G: "pp_t_positive_modal_normal_form G"
    and p: "Elem p (pp_t_domain Prop)"
    and FG_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R F)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R G)))
        (pp_zf_truth True) w"
    and GF_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R G)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R F)))
        (pp_zf_truth True) w"
    and F_impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (F \<acute> p))"
    and G_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (G \<acute> p))"
  shows
    "pp_t_fundamental_boundary (R w) w (F \<acute> p)"
proof -
  have F_domain:
      "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF F])
  have G_domain:
      "Elem G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_positive_modal_normal_form_in_domain[OF G])
  have agreement:
      "pp_t_holds (pp_t_generated_full_section R F \<acute> p) w
        \<longleftrightarrow>
       pp_t_holds (pp_t_generated_full_section R G \<acute> p) w"
    by (rule
      pp_t_full_boolean_closure_forces_positive_modal_section_agreement[
        where R=R and F=F and G=G and w=w,
        OF R F G FG_safe GF_safe p])
  show ?thesis
    by (rule
      pp_t_generated_section_agreement_forces_boundary_absorption[
        where R=R and F=F and G=G and p=p and w=w,
        OF R F_domain G_domain p agreement F_impure G_pure])
qed

corollary
    pp_t_full_boolean_closure_forces_possibility_preimage_absorption:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and identity_possibility_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R (pp_t_closed_den prop_id))
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R pp_t_possibility_operator)))
        (pp_zf_truth True) w"
    and possibility_identity_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R pp_t_possibility_operator)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R (pp_t_closed_den prop_id))))
        (pp_zf_truth True) w"
    and p_impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at p)"
    and possibility_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at
          (pp_t_possibility_operator \<acute> p))"
  shows "pp_t_fundamental_boundary (R w) w p"
proof -
  have identity_normal:
      "pp_t_positive_modal_normal_form (pp_t_closed_den prop_id)"
    unfolding pp_t_positive_modal_normal_form_def by blast
  have possibility_normal:
      "pp_t_positive_modal_normal_form pp_t_possibility_operator"
    unfolding pp_t_positive_modal_normal_form_def by blast
  have boundary:
      "pp_t_fundamental_boundary (R w) w
        (pp_t_closed_den prop_id \<acute> p)"
    by (rule
      pp_t_full_boolean_closure_forces_positive_modal_boundary_absorption[
        where R=R and F="pp_t_closed_den prop_id"
          and G=pp_t_possibility_operator and p=p and w=w,
        OF R identity_normal possibility_normal p
          identity_possibility_safe possibility_identity_safe])
      (use p_impure possibility_pure
        in \<open>simp_all add: pp_t_closed_identity_apply[OF p]\<close>)
  show ?thesis
    using boundary
    unfolding pp_t_closed_identity_apply[OF p] .
qed

corollary
    pp_t_full_boolean_closure_forces_dense_impure_boundary:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
    and dense:
      "\<And>v.
        prefix w v
        \<Longrightarrow> \<exists>u. prefix v u \<and> pp_t_holds p u"
    and identity_possibility_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R (pp_t_closed_den prop_id))
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R pp_t_possibility_operator)))
        (pp_zf_truth True) w"
    and possibility_identity_safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R pp_t_possibility_operator)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R (pp_t_closed_den prop_id))))
        (pp_zf_truth True) w"
    and p_impure:
      "\<not> pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at p)"
  shows "pp_t_fundamental_boundary (R w) w p"
proof -
  let ?M = "pp_t_possibility_operator \<acute> p"
  have M: "Elem ?M (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF pp_t_modal_operators_in_domain(2) p])
  have T: "Elem (pp_zf_truth True) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  have M_truth:
      "pp_t_eqv Prop w ?M (pp_zf_truth True)"
    unfolding pp_t_prop_eqv_truth_iff
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    obtain u where vu: "prefix v u"
      and pu: "pp_t_holds p u"
      using dense[OF wv] by blast
    show "pp_t_holds ?M v"
      using pp_t_possibility_operator_apply_holds[OF p, of v]
        vu pu by blast
  qed
  have SM:
      "Elem (pp_t_singleton_family_at ?M)
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF M])
  have ST:
      "Elem (pp_t_singleton_family_at (pp_zf_truth True))
        (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF T])
  have families:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_singleton_family_at ?M)
        (pp_t_singleton_family_at (pp_zf_truth True))"
    using pp_t_singleton_family_equivalent_iff_parameters_equivalent[
      OF M T, of w]
      M_truth by blast
  have truth_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at (pp_zf_truth True))"
    by (rule pp_t_modal_stock_contains_truth_singleton)
  have possibility_pure:
      "pp_t_probe_modal_boolean_stock w
        (pp_t_singleton_family_at ?M)"
  proof -
    have reverse:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_singleton_family_at (pp_zf_truth True))
          (pp_t_singleton_family_at ?M)"
      by (rule pp_t_eqv_symmetric[OF SM ST families])
    show ?thesis
      using pp_t_probe_modal_boolean_stock_admissible
        ST SM reverse truth_pure
      unfolding pp_t_predicate_admissible_def
      by blast
  qed
  show ?thesis
    by (rule
      pp_t_full_boolean_closure_forces_possibility_preimage_absorption[
        where R=R and p=p and w=w,
        OF R p identity_possibility_safe possibility_identity_safe
          p_impure possibility_pure])
qed

theorem
    pp_t_generated_boundary_stock_cannot_close_both_identity_possibility_mixes:
  assumes R: "\<And>x. Elem (R x) (pp_t_domain Prop)"
  shows
    "\<not>
      (pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R (pp_t_closed_den prop_id))
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R pp_t_possibility_operator)))
        (pp_zf_truth True) []
      \<and>
       pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R pp_t_possibility_operator)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R (pp_t_closed_den prop_id))))
        (pp_zf_truth True) [])"
proof
  assume safe:
      "pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R (pp_t_closed_den prop_id))
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R pp_t_possibility_operator)))
        (pp_zf_truth True) []
      \<and>
       pp_t_recombination_safe_unary_operator
        (pp_t_unary_output_disjunction
          (pp_t_generated_full_section R pp_t_possibility_operator)
          (pp_t_pointwise_complement
            (pp_t_generated_full_section R (pp_t_closed_den prop_id))))
        (pp_zf_truth True) []"
  let ?B = "pp_b_root_modal_singleton_parameter_enumerator"
  let ?D = "pp_b_dense_stock_diagonal (pp_b_of_zf (R [])) ?B"
  let ?p = "pp_zf_of_b ?D"
  have root: "Elem (R []) (pp_t_domain Prop)"
    by (rule R)
  have covers:
      "\<And>P.
        pp_t_probe_modal_boolean_stock []
          (pp_t_singleton_family_at (pp_zf_of_b P))
        \<Longrightarrow> \<exists>n. P = ?B n"
    by (rule
      pp_b_root_modal_singleton_parameter_enumerator_covers)
  have package:
      "Elem ?p (pp_t_domain Prop)
      \<and>
       (\<forall>v.
         prefix [] v
         \<longrightarrow>
           (\<exists>u. prefix v u \<and> pp_t_holds ?p u))
      \<and>
       \<not> pp_t_probe_modal_boolean_stock []
         (pp_t_singleton_family_at ?p)
      \<and>
       \<not> pp_t_fundamental_boundary (R []) [] ?p"
    by (rule pp_t_dense_stock_diagonal_package[
      where r="R []" and B="?B" and w="[]",
      OF root covers])
      simp_all
  have p: "Elem ?p (pp_t_domain Prop)"
    using package by blast
  have dense:
      "\<And>v.
        prefix [] v
        \<Longrightarrow> \<exists>u. prefix v u \<and> pp_t_holds ?p u"
    using package by blast
  have impure:
      "\<not> pp_t_probe_modal_boolean_stock []
        (pp_t_singleton_family_at ?p)"
    using package by blast
  have not_boundary:
      "\<not> pp_t_fundamental_boundary (R []) [] ?p"
    using package by blast
  have boundary:
      "pp_t_fundamental_boundary (R []) [] ?p"
    by (rule
      pp_t_full_boolean_closure_forces_dense_impure_boundary[
        where R=R and p="?p" and w="[]",
        OF R p dense safe[THEN conjunct1]
          safe[THEN conjunct2] impure])
  show False using boundary not_boundary by blast
qed

text \<open>
  A single graft supplies one directed distinction while preserving the
  Recombination obligations already met by its reserved cone.  These results
  delimit that construction.  Recombination for negated necessity forces
  every reserved cone to have a constant-true relative view, so such a cone
  cannot be locally distinct from truth.  More generally, if two classifier
  sections are necessarily true at a common argument, closure under both
  mixed Boolean combinations forces the sections to agree on every argument
  at the base world.  At the root, the singleton parameters represented by
  the modal-Boolean stock are countable.  The dense stock diagonal avoids all
  of them and every relative view of the proposed fundamental proposition,
  while its possibility is constant true.  Hence the generated-boundary
  construction cannot make both the identity/possibility and the
  possibility/identity mixed Boolean operators Recombination-safe.
  Independent directed grafts therefore cannot be the final stabilization
  of the full Boolean stock.
\<close>

end
