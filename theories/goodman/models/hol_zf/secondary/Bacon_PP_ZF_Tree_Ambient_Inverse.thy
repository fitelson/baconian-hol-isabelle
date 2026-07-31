theory Bacon_PP_ZF_Tree_Ambient_Inverse
  imports Bacon_PP_ZF_Tree_Range_Term_Basis
begin

section \<open>Cone-profile automorphisms\<close>

definition pp_b_node ::
    "bool \<Rightarrow> pp_b_prop \<Rightarrow> pp_b_prop \<Rightarrow> pp_b_prop"
where
  "pp_b_node b P Q =
    (if b then {[]} else {}) \<union>
    pp_b_lift [False] P \<union>
    pp_b_lift [True] Q"

lemma pp_b_node_root[simp]:
  "[] \<in> pp_b_node b P Q \<longleftrightarrow> b"
  by (auto simp: pp_b_node_def pp_b_lift_def)

lemma pp_b_node_view_False[simp]:
  "pp_b_view [False] (pp_b_node b P Q) = P"
  by (auto simp: pp_b_node_def pp_b_view_def pp_b_lift_def)

lemma pp_b_node_view_True[simp]:
  "pp_b_view [True] (pp_b_node b P Q) = Q"
  by (auto simp: pp_b_node_def pp_b_view_def pp_b_lift_def)

lemma pp_b_node_decompose:
  "pp_b_node ([] \<in> P)
      (pp_b_view [False] P) (pp_b_view [True] P) = P"
proof (rule set_eqI)
  fix x
  show "x \<in> pp_b_node ([] \<in> P)
      (pp_b_view [False] P) (pp_b_view [True] P)
    \<longleftrightarrow> x \<in> P"
  proof (cases x)
    case Nil
    then show ?thesis by simp
  next
    case (Cons c xs)
    then show ?thesis
      by (cases c)
        (auto simp: pp_b_node_def pp_b_view_def pp_b_lift_def)
  qed
qed

lemma pp_b_node_eq_iff:
  "pp_b_node b P Q = pp_b_node c R S
    \<longleftrightarrow> b = c \<and> P = R \<and> Q = S"
proof
  assume eq: "pp_b_node b P Q = pp_b_node c R S"
  have "b = c"
    using arg_cong[OF eq, of "\<lambda>X. [] \<in> X"] by simp
  moreover have "P = R"
    using arg_cong[OF eq, of "pp_b_view [False]"] by simp
  moreover have "Q = S"
    using arg_cong[OF eq, of "pp_b_view [True]"] by simp
  ultimately show "b = c \<and> P = R \<and> Q = S"
    by blast
next
  assume "b = c \<and> P = R \<and> Q = S"
  then show "pp_b_node b P Q = pp_b_node c R S"
    by simp
qed

lemma pp_b_prop_eqI:
  assumes root: "([] \<in> P) = ([] \<in> Q)"
    and false_view:
      "pp_b_view [False] P = pp_b_view [False] Q"
    and true_view:
      "pp_b_view [True] P = pp_b_view [True] Q"
  shows "P = Q"
proof -
  have nodes:
      "pp_b_node ([] \<in> P)
          (pp_b_view [False] P) (pp_b_view [True] P) =
        pp_b_node ([] \<in> Q)
          (pp_b_view [False] Q) (pp_b_view [True] Q)"
    using root false_view true_view by simp
  show ?thesis
    using pp_b_node_decompose[of P]
      pp_b_node_decompose[of Q] nodes
    by metis
qed

lemma pp_b_prop_eqI_children:
  assumes root: "([] \<in> P) = ([] \<in> Q)"
    and child: "pp_b_view [c] P = pp_b_view [c] Q"
    and sibling:
      "pp_b_view [\<not> c] P = pp_b_view [\<not> c] Q"
  shows "P = Q"
proof (cases c)
  case False
  have false_view:
      "pp_b_view [False] P = pp_b_view [False] Q"
    using child False by simp
  have true_view:
      "pp_b_view [True] P = pp_b_view [True] Q"
    using sibling False by simp
  show ?thesis
    using pp_b_prop_eqI[OF root false_view true_view] .
next
  case True
  have false_view:
      "pp_b_view [False] P = pp_b_view [False] Q"
    using sibling True by simp
  have true_view:
      "pp_b_view [True] P = pp_b_view [True] Q"
    using child True by simp
  show ?thesis
    using pp_b_prop_eqI[OF root false_view true_view] .
qed

definition pp_b_respects_views :: "pp_b_operator \<Rightarrow> bool" where
  "pp_b_respects_views F \<longleftrightarrow>
    (\<forall>w P Q.
      pp_b_view w P = pp_b_view w Q \<longrightarrow>
      pp_b_view w (F P) = pp_b_view w (F Q))"

definition pp_b_induced ::
    "pp_b_operator \<Rightarrow> bool list \<Rightarrow> pp_b_operator"
where
  "pp_b_induced F w P =
    pp_b_view w (F (pp_b_lift w P))"

lemma pp_b_lift_root[simp]:
  "pp_b_lift [] P = P"
  by (auto simp: pp_b_lift_def)

lemma pp_b_induced_root[simp]:
  "pp_b_induced F [] = F"
  by (rule ext) (simp add: pp_b_induced_def)

lemma pp_b_lift_node_child:
  "pp_b_view (w @ [c])
      (pp_b_lift w (pp_b_node b P Q)) =
    (if c then Q else P)"
  by (cases c)
    (auto simp: pp_b_view_def pp_b_lift_def pp_b_node_def)

lemma pp_b_induced_node_child:
  assumes respects: "pp_b_respects_views F"
  shows "pp_b_view [c]
      (pp_b_induced F w (pp_b_node b P Q)) =
    pp_b_induced F (w @ [c]) (if c then Q else P)"
proof -
  have inputs:
      "pp_b_view (w @ [c])
          (pp_b_lift w (pp_b_node b P Q)) =
        pp_b_view (w @ [c])
          (pp_b_lift (w @ [c]) (if c then Q else P))"
    by (simp add: pp_b_lift_node_child)
  have outputs:
      "pp_b_view (w @ [c])
          (F (pp_b_lift w (pp_b_node b P Q))) =
        pp_b_view (w @ [c])
          (F (pp_b_lift (w @ [c]) (if c then Q else P)))"
    using respects inputs
    unfolding pp_b_respects_views_def by blast
  show ?thesis
    using outputs
    by (simp add: pp_b_induced_def pp_b_view_compose)
qed

lemma pp_b_induced_child:
  assumes respects: "pp_b_respects_views F"
  shows "pp_b_view [c] (pp_b_induced F w P) =
    pp_b_induced F (w @ [c]) (pp_b_view [c] P)"
proof -
  have decomposition:
      "P = pp_b_node ([] \<in> P)
        (pp_b_view [False] P) (pp_b_view [True] P)"
    using pp_b_node_decompose[of P] by simp
  have node:
      "pp_b_view [c]
          (pp_b_induced F w
            (pp_b_node ([] \<in> P)
              (pp_b_view [False] P)
              (pp_b_view [True] P))) =
        pp_b_induced F (w @ [c])
          (if c then pp_b_view [True] P
           else pp_b_view [False] P)"
    by (rule pp_b_induced_node_child[OF respects])
  show ?thesis
    using node decomposition
    by (cases c) simp_all
qed

lemma pp_b_induced_child_surj:
  assumes respects: "pp_b_respects_views F"
    and parent: "surj (pp_b_induced F w)"
  shows "surj (pp_b_induced F (w @ [c]))"
unfolding surj_def
proof (intro allI)
  fix T
  let ?Target =
    "if c then pp_b_node False {} T
     else pp_b_node False T {}"
  obtain P where image:
      "pp_b_induced F w P = ?Target"
    using surjD[OF parent, of ?Target] by blast
  let ?Preimage = "pp_b_view [c] P"
  have child:
      "pp_b_induced F (w @ [c]) ?Preimage =
        pp_b_view [c] (pp_b_induced F w P)"
    using pp_b_induced_child[
      OF respects, where c=c and w=w and P=P]
    by simp
  have result:
      "pp_b_induced F (w @ [c]) ?Preimage = T"
  proof (cases c)
    case False
    show ?thesis using child image False by simp
  next
    case True
    show ?thesis using child image True by simp
  qed
  show "\<exists>P. T = pp_b_induced F (w @ [c]) P"
    using result by blast
qed

lemma pp_b_induced_child_inj:
  assumes respects: "pp_b_respects_views F"
    and parent: "inj (pp_b_induced F w)"
  shows "inj (pp_b_induced F (w @ [c]))"
proof (rule injI)
  fix P Q
  assume images:
      "pp_b_induced F (w @ [c]) P =
        pp_b_induced F (w @ [c]) Q"
  show "P = Q"
  proof (rule ccontr)
    assume distinct: "P \<noteq> Q"
    let ?S = "{}"
    let ?X0 =
      "if c then pp_b_node False ?S P
       else pp_b_node False P ?S"
    let ?X1 =
      "if c then pp_b_node True ?S P
       else pp_b_node True P ?S"
    let ?Y0 =
      "if c then pp_b_node False ?S Q
       else pp_b_node False Q ?S"
    let ?A = "pp_b_induced F w ?X0"
    let ?B = "pp_b_induced F w ?X1"
    let ?C = "pp_b_induced F w ?Y0"
    have X0_X1: "?X0 \<noteq> ?X1"
      by (cases c) (simp_all add: pp_b_node_eq_iff)
    have X0_Y0: "?X0 \<noteq> ?Y0"
      using distinct by (cases c)
        (simp_all add: pp_b_node_eq_iff)
    have X1_Y0: "?X1 \<noteq> ?Y0"
      by (cases c) (simp_all add: pp_b_node_eq_iff)
    have A_B: "?A \<noteq> ?B"
      using parent X0_X1 unfolding inj_def by blast
    have A_C: "?A \<noteq> ?C"
      using parent X0_Y0 unfolding inj_def by blast
    have B_C: "?B \<noteq> ?C"
      using parent X1_Y0 unfolding inj_def by blast
    have target_A_C:
        "pp_b_view [c] ?A = pp_b_view [c] ?C"
      using images
      by (cases c)
        (simp_all add: pp_b_induced_node_child[OF respects])
    have target_A_B:
        "pp_b_view [c] ?A = pp_b_view [c] ?B"
      by (cases c)
        (simp_all add: pp_b_induced_node_child[OF respects])
    have target_B_C:
        "pp_b_view [c] ?B = pp_b_view [c] ?C"
      using target_A_B target_A_C by simp
    have sibling_A_B:
        "pp_b_view [\<not> c] ?A = pp_b_view [\<not> c] ?B"
      by (cases c)
        (simp_all add: pp_b_induced_node_child[OF respects])
    have sibling_A_C:
        "pp_b_view [\<not> c] ?A = pp_b_view [\<not> c] ?C"
      by (cases c)
        (simp_all add: pp_b_induced_node_child[OF respects])
    have sibling_B_C:
        "pp_b_view [\<not> c] ?B = pp_b_view [\<not> c] ?C"
      using sibling_A_B sibling_A_C by simp
    have root_A_B: "([] \<in> ?A) \<noteq> ([] \<in> ?B)"
    proof
      assume root: "([] \<in> ?A) = ([] \<in> ?B)"
      have "?A = ?B"
        using root target_A_B sibling_A_B
        by (rule pp_b_prop_eqI_children)
      then show False using A_B by contradiction
    qed
    have root_A_C: "([] \<in> ?A) \<noteq> ([] \<in> ?C)"
    proof
      assume root: "([] \<in> ?A) = ([] \<in> ?C)"
      have "?A = ?C"
        using root target_A_C sibling_A_C
        by (rule pp_b_prop_eqI_children)
      then show False using A_C by contradiction
    qed
    have root_B_C: "([] \<in> ?B) \<noteq> ([] \<in> ?C)"
    proof
      assume root: "([] \<in> ?B) = ([] \<in> ?C)"
      have "?B = ?C"
        using root target_B_C sibling_B_C
        by (rule pp_b_prop_eqI_children)
      then show False using B_C by contradiction
    qed
    show False
      using root_A_B root_A_C root_B_C by blast
  qed
qed

lemma pp_b_induced_child_bij:
  assumes respects: "pp_b_respects_views F"
    and parent: "bij (pp_b_induced F w)"
  shows "bij (pp_b_induced F (w @ [c]))"
proof (unfold bij_def, intro conjI)
  have parent_inj: "inj (pp_b_induced F w)"
    using parent unfolding bij_def by blast
  show "inj (pp_b_induced F (w @ [c]))"
    using pp_b_induced_child_inj[OF respects parent_inj] .
next
  have parent_surj: "surj (pp_b_induced F w)"
    using parent unfolding bij_def by blast
  show "surj (pp_b_induced F (w @ [c]))"
    using pp_b_induced_child_surj[OF respects parent_surj] .
qed

theorem pp_b_induced_bij:
  assumes respects: "pp_b_respects_views F"
    and bijective: "bij F"
  shows "bij (pp_b_induced F w)"
proof (induction w rule: rev_induct)
  case Nil
  then show ?case using bijective by simp
next
  case (snoc c w)
  show ?case
    using pp_b_induced_child_bij[OF respects snoc.IH, of c]
    by simp
qed

theorem pp_b_inv_respects_views:
  assumes respects: "pp_b_respects_views F"
    and bijective: "bij F"
  shows "pp_b_respects_views (inv F)"
proof (unfold pp_b_respects_views_def, intro allI impI)
  fix w P Q
  assume views: "pp_b_view w P = pp_b_view w Q"
  have induced_inj: "inj (pp_b_induced F w)"
    using pp_b_induced_bij[OF respects bijective, of w]
    unfolding bij_def by blast
  have surj_F: "surj F"
    using bijective unfolding bij_def by blast
  have canonical:
      "pp_b_induced F w (pp_b_view w (inv F X)) =
        pp_b_view w X" for X
  proof -
    have input_views:
        "pp_b_view w
            (pp_b_lift w (pp_b_view w (inv F X))) =
          pp_b_view w (inv F X)"
      by simp
    have output_views:
        "pp_b_view w
            (F (pp_b_lift w (pp_b_view w (inv F X)))) =
          pp_b_view w (F (inv F X))"
      using respects input_views
      unfolding pp_b_respects_views_def by blast
    show ?thesis
      using output_views surj_f_inv_f[OF surj_F, of X]
      by (simp add: pp_b_induced_def)
  qed
  show "pp_b_view w (inv F P) = pp_b_view w (inv F Q)"
    using induced_inj
      canonical[of P] canonical[of Q] views
    unfolding inj_def by blast
qed

lemma pp_b_induced_canonical:
  assumes respects: "pp_b_respects_views F"
  shows "pp_b_induced F w (pp_b_view w P) =
    pp_b_view w (F P)"
proof -
  have inputs:
      "pp_b_view w (pp_b_lift w (pp_b_view w P)) =
        pp_b_view w P"
    by simp
  have outputs:
      "pp_b_view w (F (pp_b_lift w (pp_b_view w P))) =
        pp_b_view w (F P)"
    using respects inputs
    unfolding pp_b_respects_views_def by blast
  show ?thesis
    using outputs by (simp add: pp_b_induced_def)
qed

theorem pp_b_inverse_exists_iff:
  assumes respects: "pp_b_respects_views F"
    and bijective: "bij F"
  shows "(\<exists>Q.
      pp_b_view w (F Q) = pp_b_view w P \<and> w \<in> Q)
    \<longleftrightarrow> w \<in> inv F P"
proof
  assume exists:
      "\<exists>Q.
        pp_b_view w (F Q) = pp_b_view w P \<and> w \<in> Q"
  then obtain Q where outputs:
      "pp_b_view w (F Q) = pp_b_view w P"
    and Q_at: "w \<in> Q"
    by blast
  have induced_inj: "inj (pp_b_induced F w)"
    using pp_b_induced_bij[OF respects bijective, of w]
    unfolding bij_def by blast
  have inverse_output: "F (inv F P) = P"
    using surj_f_inv_f[OF bij_is_surj[OF bijective], of P] .
  have inputs:
      "pp_b_view w Q = pp_b_view w (inv F P)"
  proof (rule induced_inj[THEN injD])
    show "pp_b_induced F w (pp_b_view w Q) =
        pp_b_induced F w (pp_b_view w (inv F P))"
      using pp_b_induced_canonical[OF respects, of w Q]
        pp_b_induced_canonical[OF respects, of w "inv F P"]
        outputs inverse_output
      by simp
  qed
  have root_membership:
      "[] \<in> pp_b_view w Q
        \<longleftrightarrow> [] \<in> pp_b_view w (inv F P)"
    using inputs by simp
  show "w \<in> inv F P"
    using root_membership Q_at by simp
next
  assume inverse_at: "w \<in> inv F P"
  have inverse_output: "F (inv F P) = P"
    using surj_f_inv_f[OF bij_is_surj[OF bijective], of P] .
  show "\<exists>Q.
      pp_b_view w (F Q) = pp_b_view w P \<and> w \<in> Q"
    by (rule exI[of _ "inv F P"])
      (simp add: inverse_at inverse_output)
qed

section \<open>Transfer to the HOL-ZF proposition domain\<close>

lemma pp_t_zf_of_b_eqv_iff_view:
  "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_of_b Q)
    \<longleftrightarrow> pp_b_view w P = pp_b_view w Q"
proof
  assume eqv:
      "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_of_b Q)"
  show "pp_b_view w P = pp_b_view w Q"
  proof (rule set_eqI)
    fix u
    have future: "prefix w (w @ u)"
      by (simp add: prefix_def)
    have at_future:
        "pp_t_holds (pp_zf_of_b P) (w @ u)
          \<longleftrightarrow>
         pp_t_holds (pp_zf_of_b Q) (w @ u)"
      using eqv future by simp
    show "u \<in> pp_b_view w P \<longleftrightarrow>
        u \<in> pp_b_view w Q"
      using at_future by (simp add: pp_b_view_def)
  qed
next
  assume views: "pp_b_view w P = pp_b_view w Q"
  show "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_of_b Q)"
  proof (simp only: pp_t_eqv.simps, intro allI impI)
    fix v
    assume future: "prefix w v"
    then obtain u where v: "v = w @ u"
      by (auto simp: prefix_def)
    have at_u:
        "(u \<in> pp_b_view w P) = (u \<in> pp_b_view w Q)"
      using arg_cong[OF views, of "\<lambda>X. u \<in> X"] .
    show "pp_t_holds (pp_zf_of_b P) v =
        pp_t_holds (pp_zf_of_b Q) v"
      using at_u by (simp add: pp_b_view_def v)
  qed
qed

lemma pp_t_member_operator_respects_views:
  assumes X:
      "Elem X (pp_t_domain pp_t_unary_type)"
  shows "pp_b_respects_views (pp_b_operator_of X)"
proof (unfold pp_b_respects_views_def, intro allI impI)
  fix w P Q
  assume views: "pp_b_view w P = pp_b_view w Q"
  have inputs:
      "pp_t_eqv Prop w (pp_zf_of_b P) (pp_zf_of_b Q)"
    using views pp_t_zf_of_b_eqv_iff_view by blast
  have outputs:
      "pp_t_eqv Prop w
        (X \<acute> pp_zf_of_b P) (X \<acute> pp_zf_of_b Q)"
    using pp_t_arrow_member_respects[
      OF X pp_zf_of_b_in_domain pp_zf_of_b_in_domain inputs] .
  show "pp_b_view w (pp_b_operator_of X P) =
      pp_b_view w (pp_b_operator_of X Q)"
    using outputs
    unfolding pp_b_operator_of_def
    by (simp add: pp_b_of_zf_def pp_b_view_def
        pp_t_eqv.simps prefix_def)
qed

theorem pp_t_ambient_bijection_induces_cone_bijections:
  assumes X:
      "Elem X (pp_t_domain pp_t_unary_type)"
    and bijective: "bij (pp_b_operator_of X)"
  shows "bij (pp_b_induced (pp_b_operator_of X) w)"
  using pp_b_induced_bij[
    OF pp_t_member_operator_respects_views[OF X] bijective] .

theorem pp_t_ambient_inverse_respects_views:
  assumes X:
      "Elem X (pp_t_domain pp_t_unary_type)"
    and bijective: "bij (pp_b_operator_of X)"
  shows "pp_b_respects_views (inv (pp_b_operator_of X))"
  using pp_b_inv_respects_views[
    OF pp_t_member_operator_respects_views[OF X] bijective] .

section \<open>The logical inverse-builder\<close>

definition pp_ambient_inverse_builder :: oterm where
  "pp_ambient_inverse_builder =
    Lam pp_t_unary_type
      (Lam Prop
        (Exists Prop
          (Conj
            (Eq Prop
              (App (Var 2) (Var 0))
              (Var 1))
            (Var 0))))"

lemma pp_ambient_inverse_builder_typed:
  "[] \<turnstile> pp_ambient_inverse_builder :
    pp_t_unary_type \<rightarrow>\<^sub>o pp_t_unary_type"
  unfolding pp_ambient_inverse_builder_def
  by (intro has_type.Lam has_type.Exists has_type.Conj
      has_type.Eq has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma pp_ambient_inverse_builder_logical:
  "pp_logical_vocabulary pp_ambient_inverse_builder"
  unfolding pp_ambient_inverse_builder_def
    pp_logical_vocabulary_def by simp

abbreviation pp_t_ambient_inverse :: "ZF \<Rightarrow> ZF" where
  "pp_t_ambient_inverse X \<equiv>
    pp_t_closed_den pp_ambient_inverse_builder \<acute> X"

lemma pp_t_ambient_inverse_in_domain:
  assumes X: "Elem X (pp_t_domain pp_t_unary_type)"
  shows "Elem (pp_t_ambient_inverse X)
    (pp_t_domain pp_t_unary_type)"
proof -
  have builder:
      "Elem (pp_t_closed_den pp_ambient_inverse_builder)
        (pp_t_domain
          (pp_t_unary_type \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_closed_den_in_domain[
      OF pp_ambient_inverse_builder_typed] .
  show ?thesis
    using pp_t_app_closed[OF builder X] .
qed

lemma pp_t_ambient_inverse_apply_holds:
  assumes X: "Elem X (pp_t_domain pp_t_unary_type)"
    and P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_holds ((pp_t_ambient_inverse X) \<acute> P) w
    \<longleftrightarrow>
    (\<exists>Q.
      Elem Q (pp_t_domain Prop) \<and>
      pp_t_eqv Prop w (X \<acute> Q) P \<and>
      pp_t_holds Q w)"
  unfolding pp_t_closed_den_def
    pp_ambient_inverse_builder_def
  using X P
  by (simp add: Lambda_app pp_t_default_constants_def
      pp_t_closed_env_def extend_env.simps pp_t_app_closed)

definition pp_t_raw_inverse :: "ZF \<Rightarrow> ZF" where
  "pp_t_raw_inverse X =
    Lambda (pp_t_domain Prop)
      (\<lambda>P. pp_zf_of_b
        (inv (pp_b_operator_of X) (pp_b_of_zf P)))"

lemma pp_t_raw_inverse_in_domain:
  assumes X: "Elem X (pp_t_domain pp_t_unary_type)"
    and bijective: "bij (pp_b_operator_of X)"
  shows "Elem (pp_t_raw_inverse X)
    (pp_t_domain pp_t_unary_type)"
proof (unfold pp_t_raw_inverse_def, rule pp_t_lambda_closed)
  show "\<And>P. Elem P (pp_t_domain Prop) \<Longrightarrow>
      Elem
        (pp_zf_of_b
          (inv (pp_b_operator_of X) (pp_b_of_zf P)))
        (pp_t_domain Prop)"
    by (rule pp_zf_of_b_in_domain)
next
  fix w P Q
  assume P: "Elem P (pp_t_domain Prop)"
    and Q: "Elem Q (pp_t_domain Prop)"
    and PQ: "pp_t_eqv Prop w P Q"
  have views:
      "pp_b_view w (pp_b_of_zf P) =
        pp_b_view w (pp_b_of_zf Q)"
    using PQ
    by (auto simp: pp_b_view_def pp_b_of_zf_def
        pp_t_eqv.simps prefix_def)
  have inverse_respects:
      "pp_b_respects_views (inv (pp_b_operator_of X))"
    using pp_t_ambient_inverse_respects_views[OF X bijective] .
  have inverse_views:
      "pp_b_view w
          (inv (pp_b_operator_of X) (pp_b_of_zf P)) =
        pp_b_view w
          (inv (pp_b_operator_of X) (pp_b_of_zf Q))"
    using inverse_respects views
    unfolding pp_b_respects_views_def by blast
  show "pp_t_eqv Prop w
      (pp_zf_of_b
        (inv (pp_b_operator_of X) (pp_b_of_zf P)))
      (pp_zf_of_b
        (inv (pp_b_operator_of X) (pp_b_of_zf Q)))"
    using inverse_views pp_t_zf_of_b_eqv_iff_view by blast
qed

lemma pp_t_raw_inverse_apply:
  assumes P: "Elem P (pp_t_domain Prop)"
  shows "pp_t_raw_inverse X \<acute> P =
    pp_zf_of_b
      (inv (pp_b_operator_of X) (pp_b_of_zf P))"
  using P by (simp add: pp_t_raw_inverse_def Lambda_app)

lemma pp_t_ambient_inverse_exists_iff:
  assumes X: "Elem X (pp_t_domain pp_t_unary_type)"
    and bijective: "bij (pp_b_operator_of X)"
    and P: "Elem P (pp_t_domain Prop)"
  shows "(\<exists>Q.
      Elem Q (pp_t_domain Prop) \<and>
      pp_t_eqv Prop w (X \<acute> Q) P \<and>
      pp_t_holds Q w)
    \<longleftrightarrow>
    w \<in> inv (pp_b_operator_of X) (pp_b_of_zf P)"
proof -
  let ?F = "pp_b_operator_of X"
  have respects: "pp_b_respects_views ?F"
    using pp_t_member_operator_respects_views[OF X] .
  have abstract:
      "(\<exists>B.
        pp_b_view w (?F B) =
          pp_b_view w (pp_b_of_zf P) \<and> w \<in> B)
      \<longleftrightarrow>
      w \<in> inv ?F (pp_b_of_zf P)"
    using pp_b_inverse_exists_iff[
      OF respects bijective, of w "pp_b_of_zf P"] .
  have representation:
      "(\<exists>Q.
        Elem Q (pp_t_domain Prop) \<and>
        pp_t_eqv Prop w (X \<acute> Q) P \<and>
        pp_t_holds Q w)
      \<longleftrightarrow>
      (\<exists>B.
        pp_b_view w (?F B) =
          pp_b_view w (pp_b_of_zf P) \<and> w \<in> B)"
  proof
    assume left:
        "\<exists>Q.
          Elem Q (pp_t_domain Prop) \<and>
          pp_t_eqv Prop w (X \<acute> Q) P \<and>
          pp_t_holds Q w"
    then obtain Q where Q: "Elem Q (pp_t_domain Prop)"
      and outputs: "pp_t_eqv Prop w (X \<acute> Q) P"
      and Q_at: "pp_t_holds Q w"
      by blast
    let ?B = "pp_b_of_zf Q"
    have Q_exact: "pp_zf_of_b ?B = Q"
      using pp_zf_of_b_of_zf[OF Q] .
    have output_views:
        "pp_b_view w (?F ?B) =
          pp_b_view w (pp_b_of_zf P)"
      using outputs
      unfolding pp_b_operator_of_def Q_exact
      by (auto simp: pp_b_of_zf_def pp_b_view_def
          pp_t_eqv.simps prefix_def)
    have "w \<in> ?B"
      using Q_at by (simp add: pp_b_of_zf_def)
    then show "\<exists>B.
        pp_b_view w (?F B) =
          pp_b_view w (pp_b_of_zf P) \<and> w \<in> B"
      using output_views by blast
  next
    assume right:
        "\<exists>B.
          pp_b_view w (?F B) =
            pp_b_view w (pp_b_of_zf P) \<and> w \<in> B"
    then obtain B where output_views:
        "pp_b_view w (?F B) =
          pp_b_view w (pp_b_of_zf P)"
      and B_at: "w \<in> B"
      by blast
    let ?Q = "pp_zf_of_b B"
    have Q: "Elem ?Q (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have outputs:
        "pp_t_eqv Prop w (X \<acute> ?Q) P"
      using output_views P
      unfolding pp_b_operator_of_def
      by (auto simp: pp_b_of_zf_def pp_b_view_def
          pp_t_eqv.simps prefix_def)
    have "pp_t_holds ?Q w"
      using B_at by simp
    then show "\<exists>Q.
        Elem Q (pp_t_domain Prop) \<and>
        pp_t_eqv Prop w (X \<acute> Q) P \<and>
        pp_t_holds Q w"
      using Q outputs by blast
  qed
  show ?thesis
    using representation abstract by blast
qed

end
