theory Bacon_PP_Goodman_Heredity_Obstruction
  imports Bacon_PP_Goodman_Heredity
begin

section \<open>The modal obstruction in Goodman's T3 argument\<close>

text \<open>
  This is deliberately a model of the modal skeleton of the proposed T3
  derivation, not a model of the complete higher-order PP axiom package.  It
  isolates the disputed inference.  At the root, two pure operators are
  distinct but possibly identical.  Their applications agree necessarily,
  and the fundamental-role predicate is possible.  QSS holds necessarily,
  Persistence holds, and the relevant instance of Necessity of Identity
  holds.  Nevertheless evaluation at the candidate is not injective at the
  root.

  Thus the advertised route reaches only possible operator identity.  To
  recover actual operator identity one needs the converse rigidity principle
  \<open>\<diamond>(X = Y) \<longrightarrow> X = Y\<close>, equivalently the relevant instance of
  Necessity of Distinctness.
\<close>

datatype pp_T3_world = pp_T3_root | pp_T3_tip

datatype pp_T3_operator = pp_T3_X | pp_T3_Y

definition pp_T3_accessible ::
    "pp_T3_world \<Rightarrow> pp_T3_world \<Rightarrow> bool" where
  "pp_T3_accessible w v \<longleftrightarrow>
    (w = pp_T3_root \<or> v = pp_T3_tip)"

definition pp_T3_box ::
    "pp_T3_world \<Rightarrow> (pp_T3_world \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_T3_box w A \<longleftrightarrow>
    (\<forall>v. pp_T3_accessible w v \<longrightarrow> A v)"

definition pp_T3_diamond ::
    "pp_T3_world \<Rightarrow> (pp_T3_world \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_T3_diamond w A \<longleftrightarrow>
    (\<exists>v. pp_T3_accessible w v \<and> A v)"

definition pp_T3_skel_pure ::
    "pp_T3_world \<Rightarrow> pp_T3_operator \<Rightarrow> bool" where
  "pp_T3_skel_pure w X \<longleftrightarrow> True"

definition pp_T3_skel_fun :: "pp_T3_world \<Rightarrow> bool" where
  "pp_T3_skel_fun w \<longleftrightarrow> (w = pp_T3_tip)"

definition pp_T3_skel_application_identity ::
    "pp_T3_world \<Rightarrow> pp_T3_operator \<Rightarrow> pp_T3_operator \<Rightarrow> bool" where
  "pp_T3_skel_application_identity w X Y \<longleftrightarrow> True"

definition pp_T3_skel_operator_identity ::
    "pp_T3_world \<Rightarrow> pp_T3_operator \<Rightarrow> pp_T3_operator \<Rightarrow> bool" where
  "pp_T3_skel_operator_identity w X Y \<longleftrightarrow>
    (X = Y \<or> w = pp_T3_tip)"

definition pp_T3_skel_QSS :: "pp_T3_world \<Rightarrow> bool" where
  "pp_T3_skel_QSS w \<longleftrightarrow>
    (\<forall>X Y.
      pp_T3_skel_pure w X \<longrightarrow>
      pp_T3_skel_pure w Y \<longrightarrow>
      pp_T3_skel_fun w \<longrightarrow>
      pp_T3_skel_application_identity w X Y \<longrightarrow>
      pp_T3_skel_operator_identity w X Y)"

definition pp_T3_skel_fun_prime :: "pp_T3_world \<Rightarrow> bool" where
  "pp_T3_skel_fun_prime w \<longleftrightarrow>
    (\<forall>X Y.
      pp_T3_skel_pure w X \<longrightarrow>
      pp_T3_skel_pure w Y \<longrightarrow>
      pp_T3_skel_application_identity w X Y \<longrightarrow>
      pp_T3_skel_operator_identity w X Y)"

lemma pp_T3_skel_frame_reflexive:
  "pp_T3_accessible w w"
  by (cases w) (simp_all add: pp_T3_accessible_def)

lemma pp_T3_skel_frame_transitive:
  assumes "pp_T3_accessible u v"
    and "pp_T3_accessible v w"
  shows "pp_T3_accessible u w"
  using assms
  by (cases u; cases v; cases w)
    (simp_all add: pp_T3_accessible_def)

lemma pp_T3_skel_persistence:
  "pp_T3_skel_pure w X \<longrightarrow>
    pp_T3_box w (\<lambda>v. pp_T3_skel_pure v X)"
  by (simp add: pp_T3_skel_pure_def pp_T3_box_def)

lemma pp_T3_skel_application_identity_rigid:
  "pp_T3_skel_application_identity w X Y \<longrightarrow>
    pp_T3_box w
      (\<lambda>v. pp_T3_skel_application_identity v X Y)"
  by (simp add: pp_T3_skel_application_identity_def pp_T3_box_def)

lemma pp_T3_skel_necessity_of_identity:
  "pp_T3_skel_operator_identity w X Y \<longrightarrow>
    pp_T3_box w
      (\<lambda>v. pp_T3_skel_operator_identity v X Y)"
  by (cases w; cases X; cases Y)
    (simp_all add: pp_T3_skel_operator_identity_def pp_T3_box_def
      pp_T3_accessible_def)

lemma pp_T3_skel_necessitated_QSS:
  "pp_T3_box pp_T3_root pp_T3_skel_QSS"
  by (simp add: pp_T3_box_def pp_T3_accessible_def
      pp_T3_skel_QSS_def pp_T3_skel_pure_def pp_T3_skel_fun_def
      pp_T3_skel_application_identity_def
      pp_T3_skel_operator_identity_def)

lemma pp_T3_skel_possible_fun:
  "pp_T3_diamond pp_T3_root pp_T3_skel_fun"
  by (simp add: pp_T3_diamond_def pp_T3_accessible_def
      pp_T3_skel_fun_def)

lemma pp_T3_skel_not_fun_prime:
  "\<not> pp_T3_skel_fun_prime pp_T3_root"
  unfolding pp_T3_skel_fun_prime_def
    pp_T3_skel_pure_def pp_T3_skel_application_identity_def
    pp_T3_skel_operator_identity_def
  by (metis pp_T3_operator.distinct(1) pp_T3_world.distinct(1))

lemma pp_T3_skel_possible_identity_not_actual:
  "pp_T3_diamond pp_T3_root
      (\<lambda>w. pp_T3_skel_operator_identity w pp_T3_X pp_T3_Y)
    \<and>
    \<not> pp_T3_skel_operator_identity
      pp_T3_root pp_T3_X pp_T3_Y"
  by (simp add: pp_T3_diamond_def pp_T3_accessible_def
      pp_T3_skel_operator_identity_def)

theorem Goodman_T3_modal_skeleton_countermodel:
  "(\<forall>w. pp_T3_accessible w w)
    \<and> (\<forall>u v w.
      pp_T3_accessible u v \<longrightarrow>
      pp_T3_accessible v w \<longrightarrow>
      pp_T3_accessible u w)
    \<and> pp_T3_box pp_T3_root pp_T3_skel_QSS
    \<and> (\<forall>w X.
      pp_T3_skel_pure w X \<longrightarrow>
      pp_T3_box w (\<lambda>v. pp_T3_skel_pure v X))
    \<and> (\<forall>w X Y.
      pp_T3_skel_application_identity w X Y \<longrightarrow>
      pp_T3_box w
        (\<lambda>v. pp_T3_skel_application_identity v X Y))
    \<and> (\<forall>w X Y.
      pp_T3_skel_operator_identity w X Y \<longrightarrow>
      pp_T3_box w
        (\<lambda>v. pp_T3_skel_operator_identity v X Y))
    \<and> pp_T3_diamond pp_T3_root pp_T3_skel_fun
    \<and> \<not> pp_T3_skel_fun_prime pp_T3_root"
  using pp_T3_skel_frame_reflexive pp_T3_skel_frame_transitive
    pp_T3_skel_necessitated_QSS pp_T3_skel_persistence
    pp_T3_skel_application_identity_rigid
    pp_T3_skel_necessity_of_identity pp_T3_skel_possible_fun
    pp_T3_skel_not_fun_prime
  by blast

corollary Goodman_T3_modal_skeleton_implication_fails:
  "\<not> (pp_T3_diamond pp_T3_root pp_T3_skel_fun
    \<longrightarrow> pp_T3_skel_fun_prime pp_T3_root)"
  using pp_T3_skel_possible_fun pp_T3_skel_not_fun_prime
  by blast

end
