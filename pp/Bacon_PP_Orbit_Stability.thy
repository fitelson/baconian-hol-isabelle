theory Bacon_PP_Orbit_Stability
  imports Bacon_PP_Uniform_Index
begin

section \<open>The general orbit-stability reduction\<close>

text \<open>
  Every closed Pure-free term of type
  \<open>t \<rightarrow> (t \<rightarrow> t)\<close> denotes an equivariant binary family.  This theory
  separates the semantic consequence of that fact from the still-open
  syntactic definability question.
\<close>

definition pp_equivariant_binary_family ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool"
  where
  "pp_equivariant_binary_family Y \<longleftrightarrow>
    (\<forall>i b c.
      pp_view i (Y b c) =
      Y (pp_view i b) (pp_view i c))"

definition pp_parameter_orbit_stable ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> bool"
  where
  "pp_parameter_orbit_stable Y b \<longleftrightarrow>
    (\<forall>i. Y (pp_view i b) = Y b)"

definition pp_binary_root_relation ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool"
  where
  "pp_binary_root_relation Y b c \<longleftrightarrow>
    pp_root_true (Y b c)"

lemma pp_equivariant_binary_family_member:
  assumes equivariant: "pp_equivariant_binary_family Y"
  shows "pp_function_space_member (Y b)"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix i P Q
  assume views: "pp_view i P = pp_view i Q"
  have "pp_view i (Y b P) =
      Y (pp_view i b) (pp_view i P)"
    using equivariant
    unfolding pp_equivariant_binary_family_def by blast
  also have "... =
      Y (pp_view i b) (pp_view i Q)"
    using views by simp
  also have "... = pp_view i (Y b Q)"
    using equivariant
    unfolding pp_equivariant_binary_family_def by blast
  finally show "pp_view i (Y b P) = pp_view i (Y b Q)" .
qed

theorem pp_binary_family_invariant_iff_parameter_orbit_stable:
  assumes family: "pp_equivariant_binary_family Y"
  shows "pp_fun_invariant (Y b) \<longleftrightarrow>
    pp_parameter_orbit_stable Y b"
proof
  assume invariant: "pp_fun_invariant (Y b)"
  have unary_equivariant:
      "pp_equivariant_operator (Y b)"
    using pp_fun_invariant_iff_equivariant[
        OF pp_equivariant_binary_family_member[OF family]]
      invariant by blast
  show "pp_parameter_orbit_stable Y b"
    unfolding pp_parameter_orbit_stable_def
  proof (intro allI, rule ext)
    fix i c
    let ?preimage = "pp_lift i c"
    have binary_action:
        "pp_view i (Y b ?preimage) =
         Y (pp_view i b) c"
      using family
      unfolding pp_equivariant_binary_family_def by simp
    have unary_action:
        "pp_view i (Y b ?preimage) = Y b c"
      using unary_equivariant
      unfolding pp_equivariant_operator_def by simp
    show "Y (pp_view i b) c = Y b c"
      using binary_action unary_action by simp
  qed
next
  assume stable: "pp_parameter_orbit_stable Y b"
  have unary_equivariant:
      "pp_equivariant_operator (Y b)"
  proof (unfold pp_equivariant_operator_def, intro allI)
    fix i c
    have "pp_view i (Y b c) =
        Y (pp_view i b) (pp_view i c)"
      using family
      unfolding pp_equivariant_binary_family_def by blast
    also have "... = Y b (pp_view i c)"
    proof -
      have "Y (pp_view i b) = Y b"
        using stable
        unfolding pp_parameter_orbit_stable_def by blast
      then show ?thesis by simp
    qed
    finally show
        "pp_view i (Y b c) = Y b (pp_view i c)" .
  qed
  show "pp_fun_invariant (Y b)"
    using pp_fun_invariant_iff_equivariant[
        OF pp_equivariant_binary_family_member[OF family]]
      unary_equivariant by blast
qed

lemma pp_equivariant_binary_family_reconstruction:
  assumes family: "pp_equivariant_binary_family Y"
  shows "Y b c =
    {i. pp_binary_root_relation Y
      (pp_view i b) (pp_view i c)}"
proof (rule set_eqI)
  fix i
  have "i \<in> Y b c \<longleftrightarrow>
      pp_root_true (pp_view i (Y b c))"
    by (simp add: pp_root_true_def pp_view_membership_at_root)
  also have "... \<longleftrightarrow>
      pp_root_true
        (Y (pp_view i b) (pp_view i c))"
  proof -
    have "pp_view i (Y b c) =
        Y (pp_view i b) (pp_view i c)"
      using family
      unfolding pp_equivariant_binary_family_def by blast
    then show ?thesis by simp
  qed
  also have "... \<longleftrightarrow>
      pp_binary_root_relation Y
        (pp_view i b) (pp_view i c)"
    by (simp add: pp_binary_root_relation_def)
  finally show
      "i \<in> Y b c \<longleftrightarrow>
       i \<in> {i. pp_binary_root_relation Y
        (pp_view i b) (pp_view i c)}"
    by simp
qed

theorem pp_parameter_orbit_stable_iff_root_fibre_stable:
  assumes family: "pp_equivariant_binary_family Y"
  shows "pp_parameter_orbit_stable Y b \<longleftrightarrow>
    (\<forall>i c.
      pp_binary_root_relation Y (pp_view i b) c =
      pp_binary_root_relation Y b c)"
proof
  assume stable: "pp_parameter_orbit_stable Y b"
  show "\<forall>i c.
      pp_binary_root_relation Y (pp_view i b) c =
      pp_binary_root_relation Y b c"
  proof (intro allI)
    fix i c
    have "Y (pp_view i b) = Y b"
      using stable
      unfolding pp_parameter_orbit_stable_def by blast
    then show
        "pp_binary_root_relation Y (pp_view i b) c =
         pp_binary_root_relation Y b c"
      by (simp add: pp_binary_root_relation_def)
  qed
next
  assume root_stable:
      "\<forall>i c.
        pp_binary_root_relation Y (pp_view i b) c =
        pp_binary_root_relation Y b c"
  show "pp_parameter_orbit_stable Y b"
    unfolding pp_parameter_orbit_stable_def
  proof (intro allI, rule ext, rule set_eqI)
    fix i c j
    have left:
        "j \<in> Y (pp_view i b) c \<longleftrightarrow>
         pp_binary_root_relation Y
           (pp_view j (pp_view i b)) (pp_view j c)"
      using pp_equivariant_binary_family_reconstruction[
          OF family, of "pp_view i b" c]
      by simp
    have left_to_root:
        "pp_binary_root_relation Y
           (pp_view j (pp_view i b)) (pp_view j c) =
         pp_binary_root_relation Y b (pp_view j c)"
      using root_stable
      by (simp add: pp_view_compose)
    have right:
        "j \<in> Y b c \<longleftrightarrow>
         pp_binary_root_relation Y
           (pp_view j b) (pp_view j c)"
      using pp_equivariant_binary_family_reconstruction[
          OF family, of b c]
      by simp
    have right_to_root:
        "pp_binary_root_relation Y
           (pp_view j b) (pp_view j c) =
         pp_binary_root_relation Y b (pp_view j c)"
      using root_stable by blast
    show "j \<in> Y (pp_view i b) c \<longleftrightarrow> j \<in> Y b c"
      using left left_to_root right right_to_root by blast
  qed
qed

corollary pp_binary_family_invariant_iff_root_fibre_stable:
  assumes family: "pp_equivariant_binary_family Y"
  shows "pp_fun_invariant (Y b) \<longleftrightarrow>
    (\<forall>i c.
      pp_binary_root_relation Y (pp_view i b) c =
      pp_binary_root_relation Y b c)"
  using pp_binary_family_invariant_iff_parameter_orbit_stable[
      OF family, of b]
    pp_parameter_orbit_stable_iff_root_fibre_stable[
      OF family, of b]
  by blast

text \<open>
  The last equivalence is the exact residual obstruction.  For a Pure-free
  family \<open>Y\<close>, its root relation is Pure-free definable by the matrix
  \<open>Y b c\<close>.  But the displayed condition compares the current root fibre
  with the root fibre after moving only the parameter \<open>b\<close>.  Ordinary modal
  evaluation moves every free parameter together.  Thus the missing step is
  a uniform Pure-free way to freeze or name the current fibre; a range formula
  does not provide one, as \<open>pp_naive_IDX_base_counterexample\<close> shows.
\<close>

end
