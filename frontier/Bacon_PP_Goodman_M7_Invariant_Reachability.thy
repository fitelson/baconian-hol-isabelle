theory Bacon_PP_Goodman_M7_Invariant_Reachability
  imports Bacon_PP_Goodman_M6
begin

section \<open>Goodman M7: reachability by invariant operators\<close>

definition pp_M7_invariant_reachable ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_M7_invariant_reachable r q \<longleftrightarrow>
    (\<exists>F.
      pp_function_space_member F
      \<and> pp_fun_invariant F
      \<and> F r = q)"

lemma pp_M7_invariant_reachable_iff_classifier:
  "pp_M7_invariant_reachable r q
    \<longleftrightarrow> (\<exists>S. pp_classifier S r = q)"
proof
  assume "pp_M7_invariant_reachable r q"
  then obtain F where
      member: "pp_function_space_member F"
      and invariant: "pp_fun_invariant F"
      and F_value: "F r = q"
    unfolding pp_M7_invariant_reachable_def by blast
  have representation: "F = pp_classifier (pp_operator_index F)"
    using member invariant by (rule pp_fun_invariant_is_classifier)
  then show "\<exists>S. pp_classifier S r = q"
  proof (intro exI[of _ "pp_operator_index F"])
    show "pp_classifier (pp_operator_index F) r = q"
      using representation F_value by simp
  qed
next
  assume "\<exists>S. pp_classifier S r = q"
  then obtain S where classifier_value: "pp_classifier S r = q" by blast
  have certified:
      "pp_function_space_member (pp_classifier S)
       \<and> pp_fun_invariant (pp_classifier S)"
    by (rule pp_classifier_is_function_space_invariant)
  show "pp_M7_invariant_reachable r q"
    unfolding pp_M7_invariant_reachable_def
    using certified classifier_value by blast
qed

theorem pp_M7_all_invariant_reachable_iff_orbit_map_injective:
  "(\<forall>q. pp_M7_invariant_reachable r q)
    \<longleftrightarrow> inj (\<lambda>i. pp_view i r)"
proof
  assume all_reachable:
      "\<forall>q. pp_M7_invariant_reachable r q"
  show "inj (\<lambda>i. pp_view i r)"
    unfolding inj_def
  proof (intro allI impI)
    fix i j
    assume same_view: "pp_view i r = pp_view j r"
    obtain S where singleton:
        "pp_classifier S r = {i}"
      using all_reachable[rule_format, of "{i}"]
      unfolding pp_M7_invariant_reachable_iff_classifier by blast
    have i_in_classifier: "i \<in> pp_classifier S r"
      using singleton by simp
    have i_mem: "pp_view i r \<in> S"
      using i_in_classifier by (simp add: pp_classifier_def)
    have j_mem: "pp_view j r \<in> S"
      using same_view i_mem by simp
    have "j \<in> pp_classifier S r"
      using j_mem by (simp add: pp_classifier_def)
    then show "i = j"
      using singleton by simp
  qed
next
  assume injective: "inj (\<lambda>i. pp_view i r)"
  show "\<forall>q. pp_M7_invariant_reachable r q"
  proof
    fix q
    let ?S = "(\<lambda>i. pp_view i r) ` q"
    have classifier_value: "pp_classifier ?S r = q"
    proof (rule set_eqI)
      fix i
      show "i \<in> pp_classifier ?S r \<longleftrightarrow> i \<in> q"
      proof
        assume "i \<in> pp_classifier ?S r"
        then obtain j where j: "j \<in> q"
          and same: "pp_view i r = pp_view j r"
          by (auto simp: pp_classifier_def)
        have "i = j"
          using injective same unfolding inj_def by blast
        then show "i \<in> q"
          using j by simp
      next
        assume "i \<in> q"
        then show "i \<in> pp_classifier ?S r"
          by (auto simp: pp_classifier_def)
      qed
    qed
    show "pp_M7_invariant_reachable r q"
      unfolding pp_M7_invariant_reachable_iff_classifier
      using classifier_value by blast
  qed
qed

text \<open>
  Thus every proposition is reachable from \<open>r\<close> by an invariant unary
  function-space element exactly when distinct substitution worlds give
  distinct views of \<open>r\<close>.  This establishes the equivalence asserted in M7;
  whether Bacon's particular glued fundamental witness has this injectivity
  property remains construction-sensitive and open.
\<close>

end
