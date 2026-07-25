theory Bacon_PP_TreeAut_Functions
  imports Bacon_PP_TreeAut Bacon_PP_Orbit_Stability
begin

section \<open>Tree conjugation preserves Bacon's unary function domain\<close>

text \<open>
  The frame calculation alone does not justify a claim about the full
  higher-order Pure-free language.  The first necessary higher-order check is
  that tree conjugation preserves Bacon's local unary function space.  This
  section proves that check, together with preservation of application.
\<close>

definition pp_cone_equal ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool"
  where
  "pp_cone_equal i P Q \<longleftrightarrow> pp_view i P = pp_view i Q"

lemma pp_cone_equal_iff:
  "pp_cone_equal i P Q \<longleftrightarrow>
    (\<forall>w. pp_accessible i w \<longrightarrow> (w \<in> P \<longleftrightarrow> w \<in> Q))"
  by (auto simp: pp_cone_equal_def pp_accessible_def pp_view_def)

theorem pp_img_cone_equal_iff:
  "pp_cone_equal i (pp_img P) (pp_img Q) \<longleftrightarrow>
    pp_cone_equal (pp_tw i) P Q"
proof
  assume images: "pp_cone_equal i (pp_img P) (pp_img Q)"
  show "pp_cone_equal (pp_tw i) P Q"
    unfolding pp_cone_equal_iff
  proof (intro allI impI)
    fix w
    assume accessible: "pp_accessible (pp_tw i) w"
    have pulled_accessible:
        "pp_accessible i (pp_tw w)"
      using accessible
      by (metis pp_tw_accessible pp_tw_tw)
    have "pp_tw w \<in> pp_img P \<longleftrightarrow>
          pp_tw w \<in> pp_img Q"
      using images pulled_accessible
      unfolding pp_cone_equal_iff by blast
    then show "w \<in> P \<longleftrightarrow> w \<in> Q"
      by simp
  qed
next
  assume originals: "pp_cone_equal (pp_tw i) P Q"
  show "pp_cone_equal i (pp_img P) (pp_img Q)"
    unfolding pp_cone_equal_iff
  proof (intro allI impI)
    fix w
    assume accessible: "pp_accessible i w"
    have image_accessible:
        "pp_accessible (pp_tw i) (pp_tw w)"
      using accessible by simp
    have "pp_tw w \<in> P \<longleftrightarrow> pp_tw w \<in> Q"
      using originals image_accessible
      unfolding pp_cone_equal_iff by blast
    then show "w \<in> pp_img P \<longleftrightarrow> w \<in> pp_img Q"
      by simp
  qed
qed

definition pp_tree_conjugate ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop"
  where
  "pp_tree_conjugate F P = pp_img (F (pp_img P))"

lemma pp_tree_conjugate_involution[simp]:
  "pp_tree_conjugate (pp_tree_conjugate F) = F"
  by (rule ext) (simp add: pp_tree_conjugate_def)

lemma pp_tree_conjugate_application:
  "pp_tree_conjugate F (pp_img P) = pp_img (F P)"
  by (simp add: pp_tree_conjugate_def)

theorem pp_tree_conjugate_member:
  assumes member: "pp_function_space_member F"
  shows "pp_function_space_member (pp_tree_conjugate F)"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix i P Q
  assume views: "pp_view i P = pp_view i Q"
  have input_cones:
      "pp_cone_equal (pp_tw i) (pp_img P) (pp_img Q)"
    using views pp_img_cone_equal_iff[of "pp_tw i" P Q]
    by (simp add: pp_cone_equal_def)
  have output_cones:
      "pp_cone_equal (pp_tw i)
        (F (pp_img P)) (F (pp_img Q))"
    using member input_cones
    unfolding pp_function_space_member_def pp_cone_equal_def
    by blast
  have "pp_cone_equal i
      (pp_img (F (pp_img P)))
      (pp_img (F (pp_img Q)))"
    using output_cones pp_img_cone_equal_iff[
        of i "F (pp_img P)" "F (pp_img Q)"]
    by blast
  then show
      "pp_view i (pp_tree_conjugate F P) =
       pp_view i (pp_tree_conjugate F Q)"
    by (simp add: pp_tree_conjugate_def pp_cone_equal_def)
qed

theorem pp_tree_conjugate_member_iff:
  "pp_function_space_member (pp_tree_conjugate F) \<longleftrightarrow>
    pp_function_space_member F"
proof
  assume "pp_function_space_member (pp_tree_conjugate F)"
  then have
      "pp_function_space_member
        (pp_tree_conjugate (pp_tree_conjugate F))"
    by (rule pp_tree_conjugate_member)
  then show "pp_function_space_member F" by simp
next
  assume "pp_function_space_member F"
  then show "pp_function_space_member (pp_tree_conjugate F)"
    by (rule pp_tree_conjugate_member)
qed

corollary pp_tree_conjugate_bijects_function_space:
  "bij_betw pp_tree_conjugate
    {F. pp_function_space_member F}
    {F. pp_function_space_member F}"
  unfolding bij_betw_def
proof (intro conjI)
  show "inj_on pp_tree_conjugate
      {F. pp_function_space_member F}"
    unfolding inj_on_def by (metis pp_tree_conjugate_involution)
  show "pp_tree_conjugate `
      {F. pp_function_space_member F} =
      {F. pp_function_space_member F}"
  proof
    show "pp_tree_conjugate `
        {F. pp_function_space_member F} \<subseteq>
        {F. pp_function_space_member F}"
      using pp_tree_conjugate_member by blast
  next
    show "{F. pp_function_space_member F} \<subseteq>
        pp_tree_conjugate `
          {F. pp_function_space_member F}"
    proof
      fix F
      assume F: "F \<in> {F. pp_function_space_member F}"
      have conjugate_member:
          "pp_tree_conjugate F \<in>
           {F. pp_function_space_member F}"
        using F pp_tree_conjugate_member by blast
      have "F = pp_tree_conjugate (pp_tree_conjugate F)"
        by simp
      then show "F \<in> pp_tree_conjugate `
          {F. pp_function_space_member F}"
        using conjugate_member by blast
    qed
  qed
qed

theorem pp_tree_conjugate_can_destroy_invariance_inside_domain:
  "\<exists>F.
    pp_function_space_member F \<and>
    pp_fun_invariant F \<and>
    pp_function_space_member (pp_tree_conjugate F) \<and>
    \<not> pp_fun_invariant (pp_tree_conjugate F)"
proof (intro exI[of _ pp_zero_op] conjI)
  show "pp_function_space_member pp_zero_op"
    using pp_zero_op_equivariant
      pp_equivariant_operator_member by blast
  show "pp_fun_invariant pp_zero_op"
    using pp_zero_op_equivariant
      pp_equivariant_operator_invariant by blast
  show "pp_function_space_member
      (pp_tree_conjugate pp_zero_op)"
    using pp_zero_op_equivariant
      pp_equivariant_operator_member
      pp_tree_conjugate_member by blast
  have conjugate:
      "pp_tree_conjugate pp_zero_op = pp_tw_zero_op"
    by (rule ext)
      (simp add: pp_tree_conjugate_def pp_tw_zero_op_conjugate)
  show "\<not> pp_fun_invariant
      (pp_tree_conjugate pp_zero_op)"
  proof
    assume invariant:
        "pp_fun_invariant
          (pp_tree_conjugate pp_zero_op)"
    have equivariant:
        "pp_equivariant_operator
          (pp_tree_conjugate pp_zero_op)"
      using invariant
        pp_fun_invariant_iff_equivariant[
          OF pp_tree_conjugate_member[
            OF pp_equivariant_operator_member[
              OF pp_zero_op_equivariant]]]
      by blast
    then show False
      using conjugate pp_tw_zero_op_not_equivariant by simp
  qed
qed

text \<open>
  The bijection theorem is the exact domain condition needed for universal and
  existential quantification over \<open>t \<rightarrow> t\<close> to survive tree conjugation.
  To turn the final non-stability theorem into a full non-definability theorem,
  one must still prove that higher-type equality and every logical constant are
  preserved by the recursively induced conjugations.  That remaining coherence
  diagram is now explicit; it is not being assumed here.
\<close>

end
