theory Bacon_PP_Goodman_Heredity_Advertised
  imports
    Bacon_PP_Goodman_Heredity_Sharp
    Bacon_PP_Goodman_Heredity_Obstruction
begin

section \<open>The exact advertised T3 stock\<close>

text \<open>
  Section 4 of Goodman's notes globally assumes the T6 core together with the
  existence of a \<open>fun\<acute>\<close> proposition.  T3 additionally flags necessitated QSS
  and Persistence.  The older name \<open>pp_T3_axioms\<close> contains the core, QSS, and
  Persistence, but omits the globally assumed existential because the proposed
  derivation never uses it.  The following name records the literal advertised
  stock without changing the sharper dependency results.
\<close>

definition pp_T3_advertised_axioms :: "oterm set" where
  "pp_T3_advertised_axioms =
    insert pp_exists_fun_prime pp_T3_axioms"

lemma pp_T3_advertised_axioms_typed:
  assumes "A \<in> pp_T3_advertised_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_T3_axioms_typed typed_pp_exists_fun_prime
  unfolding pp_T3_advertised_axioms_def by blast

lemma pp_T3_axioms_subset_advertised:
  "pp_T3_axioms \<subseteq> pp_T3_advertised_axioms"
  unfolding pp_T3_advertised_axioms_def by blast

lemma pp_T3_exists_fun_prime_advertised:
  "pp_exists_fun_prime \<in> pp_T3_advertised_axioms"
  unfolding pp_T3_advertised_axioms_def by simp

theorem CEV_Goodman_T3_advertised_with_exhaustion:
  "[] ; insert pp_zeroary_exhaustion pp_T3_advertised_axioms
     \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
proof (rule CEV_axiom_proves_mono[
    OF CEV_Goodman_T3_heredity_with_exhaustion])
  show "insert pp_zeroary_exhaustion pp_T3_axioms
      \<subseteq> insert pp_zeroary_exhaustion pp_T3_advertised_axioms"
    using pp_T3_axioms_subset_advertised by blast
qed

section \<open>A stronger finite obstruction with the Section 4 background\<close>

text \<open>
  The earlier two-world obstruction isolates the invalid modal inference but
  abstracts away from Goodman's global \<open>\<exists>fun\<acute>\<close> assumption and from the
  uniqueness of the fundamental role.  The finite structure below adds both.
  It also validates the proposition-valued unary instance of Modalized
  Functionality.

  This is still a model of the T3-relevant modal abstraction, not a model of
  every term and every instance of the unbounded purity and application
  schemas.  Its role is exact and limited: it proves that adding the omitted
  Section 4 existential, unique fundamentality, and Modalized Functionality
  does not repair the passage from possible operator identity to actual
  operator identity.
\<close>

datatype pp_T3_adv_world = pp_T3_adv_root | pp_T3_adv_tip
datatype pp_T3_adv_prop =
    pp_T3_adv_r | pp_T3_adv_x | pp_T3_adv_a | pp_T3_adv_b
datatype pp_T3_adv_op = pp_T3_adv_X | pp_T3_adv_Y

definition pp_T3_adv_accessible ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_world \<Rightarrow> bool" where
  "pp_T3_adv_accessible w v \<longleftrightarrow>
    (w = pp_T3_adv_root \<or> v = pp_T3_adv_tip)"

definition pp_T3_adv_box ::
    "pp_T3_adv_world \<Rightarrow> (pp_T3_adv_world \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_T3_adv_box w A \<longleftrightarrow>
    (\<forall>v. pp_T3_adv_accessible w v \<longrightarrow> A v)"

definition pp_T3_adv_diamond ::
    "pp_T3_adv_world \<Rightarrow> (pp_T3_adv_world \<Rightarrow> bool) \<Rightarrow> bool" where
  "pp_T3_adv_diamond w A \<longleftrightarrow>
    (\<exists>v. pp_T3_adv_accessible w v \<and> A v)"

definition pp_T3_adv_prop_eq ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_prop \<Rightarrow> pp_T3_adv_prop \<Rightarrow> bool" where
  "pp_T3_adv_prop_eq w p q \<longleftrightarrow>
    (p = q \<or> w = pp_T3_adv_tip)"

definition pp_T3_adv_op_eq ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_op \<Rightarrow> pp_T3_adv_op \<Rightarrow> bool" where
  "pp_T3_adv_op_eq w F G \<longleftrightarrow>
    (F = G \<or> w = pp_T3_adv_tip)"

definition pp_T3_adv_app ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_op \<Rightarrow>
      pp_T3_adv_prop \<Rightarrow> pp_T3_adv_prop" where
  "pp_T3_adv_app w F p =
    (if w = pp_T3_adv_root \<and> F = pp_T3_adv_Y
          \<and> p = pp_T3_adv_r
     then pp_T3_adv_b
     else pp_T3_adv_a)"

definition pp_T3_adv_app_eq ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_op \<Rightarrow>
      pp_T3_adv_op \<Rightarrow> pp_T3_adv_prop \<Rightarrow> bool" where
  "pp_T3_adv_app_eq w F G p \<longleftrightarrow>
    pp_T3_adv_prop_eq w
      (pp_T3_adv_app w F p) (pp_T3_adv_app w G p)"

definition pp_T3_adv_pure ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_op \<Rightarrow> bool" where
  "pp_T3_adv_pure w F \<longleftrightarrow> True"

definition pp_T3_adv_fundamental ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_prop \<Rightarrow> bool" where
  "pp_T3_adv_fundamental w p \<longleftrightarrow>
    (if w = pp_T3_adv_root
     then p = pp_T3_adv_r
     else p = pp_T3_adv_x)"

definition pp_T3_adv_fun_prime ::
    "pp_T3_adv_world \<Rightarrow> pp_T3_adv_prop \<Rightarrow> bool" where
  "pp_T3_adv_fun_prime w p \<longleftrightarrow>
    (\<forall>F G.
      pp_T3_adv_pure w F \<longrightarrow>
      pp_T3_adv_pure w G \<longrightarrow>
      pp_T3_adv_app_eq w F G p \<longrightarrow>
      pp_T3_adv_op_eq w F G)"

definition pp_T3_adv_QSS :: "pp_T3_adv_world \<Rightarrow> bool" where
  "pp_T3_adv_QSS w \<longleftrightarrow>
    (\<forall>F G p.
      pp_T3_adv_pure w F \<longrightarrow>
      pp_T3_adv_pure w G \<longrightarrow>
      pp_T3_adv_fundamental w p \<longrightarrow>
      pp_T3_adv_app_eq w F G p \<longrightarrow>
      pp_T3_adv_op_eq w F G)"

definition pp_T3_adv_modalized_functionality ::
    "pp_T3_adv_world \<Rightarrow> bool" where
  "pp_T3_adv_modalized_functionality w \<longleftrightarrow>
    (\<forall>F G.
      pp_T3_adv_box w
        (\<lambda>v. \<forall>p. pp_T3_adv_app_eq v F G p)
      \<longrightarrow> pp_T3_adv_op_eq w F G)"

lemma pp_T3_adv_frame_reflexive:
  "pp_T3_adv_accessible w w"
  by (cases w) (simp_all add: pp_T3_adv_accessible_def)

lemma pp_T3_adv_frame_transitive:
  assumes "pp_T3_adv_accessible u v"
    and "pp_T3_adv_accessible v w"
  shows "pp_T3_adv_accessible u w"
  using assms
  by (cases u; cases v; cases w)
    (simp_all add: pp_T3_adv_accessible_def)

lemma pp_T3_adv_prop_identity_necessary:
  "pp_T3_adv_prop_eq w p q \<longrightarrow>
    pp_T3_adv_box w (\<lambda>v. pp_T3_adv_prop_eq v p q)"
  by (cases w; cases p; cases q)
    (simp_all add: pp_T3_adv_prop_eq_def pp_T3_adv_box_def
      pp_T3_adv_accessible_def)

lemma pp_T3_adv_op_identity_necessary:
  "pp_T3_adv_op_eq w F G \<longrightarrow>
    pp_T3_adv_box w (\<lambda>v. pp_T3_adv_op_eq v F G)"
  by (cases w; cases F; cases G)
    (simp_all add: pp_T3_adv_op_eq_def pp_T3_adv_box_def
      pp_T3_adv_accessible_def)

lemma pp_T3_adv_application_identity_necessary:
  "pp_T3_adv_app_eq w F G p \<longrightarrow>
    pp_T3_adv_box w (\<lambda>v. pp_T3_adv_app_eq v F G p)"
  by (cases w; cases F; cases G; cases p)
    (simp_all add: pp_T3_adv_app_eq_def pp_T3_adv_prop_eq_def
      pp_T3_adv_app_def pp_T3_adv_box_def pp_T3_adv_accessible_def)

lemma pp_T3_adv_persistence:
  "pp_T3_adv_pure w F \<longrightarrow>
    pp_T3_adv_box w (\<lambda>v. pp_T3_adv_pure v F)"
  by (simp add: pp_T3_adv_pure_def pp_T3_adv_box_def)

lemma pp_T3_adv_QSS_everywhere:
  "\<forall>w. pp_T3_adv_QSS w"
proof (intro allI)
  fix w
  show "pp_T3_adv_QSS w"
    unfolding pp_T3_adv_QSS_def
  proof (intro allI impI)
    fix F G p
    assume "pp_T3_adv_pure w F"
      "pp_T3_adv_pure w G"
      "pp_T3_adv_fundamental w p"
      "pp_T3_adv_app_eq w F G p"
    then show "pp_T3_adv_op_eq w F G"
      by (cases w; cases F; cases G; cases p)
        (simp_all add: pp_T3_adv_pure_def pp_T3_adv_fundamental_def
          pp_T3_adv_app_eq_def pp_T3_adv_prop_eq_def
          pp_T3_adv_app_def pp_T3_adv_op_eq_def)
  qed
qed

lemma pp_T3_adv_unique_fundamental_everywhere:
  "\<forall>w. \<exists>p.
    pp_T3_adv_fundamental w p
    \<and> (\<forall>q. pp_T3_adv_fundamental w q
      \<longrightarrow> pp_T3_adv_prop_eq w q p)"
proof (intro allI)
  fix w
  show "\<exists>p.
      pp_T3_adv_fundamental w p
      \<and> (\<forall>q. pp_T3_adv_fundamental w q
        \<longrightarrow> pp_T3_adv_prop_eq w q p)"
  proof (cases w)
    case pp_T3_adv_root
    then show ?thesis
      by (intro exI[of _ pp_T3_adv_r])
        (simp add: pp_T3_adv_fundamental_def pp_T3_adv_prop_eq_def)
  next
    case pp_T3_adv_tip
    then show ?thesis
      by (intro exI[of _ pp_T3_adv_x])
        (simp add: pp_T3_adv_fundamental_def pp_T3_adv_prop_eq_def)
  qed
qed

lemma pp_T3_adv_fun_prime_witness:
  "pp_T3_adv_fun_prime pp_T3_adv_root pp_T3_adv_r"
proof (unfold pp_T3_adv_fun_prime_def, intro allI impI)
  fix F G
  assume "pp_T3_adv_pure pp_T3_adv_root F"
    "pp_T3_adv_pure pp_T3_adv_root G"
    "pp_T3_adv_app_eq pp_T3_adv_root F G pp_T3_adv_r"
  then show "pp_T3_adv_op_eq pp_T3_adv_root F G"
    by (cases F; cases G)
      (simp_all add: pp_T3_adv_pure_def pp_T3_adv_app_eq_def
        pp_T3_adv_prop_eq_def pp_T3_adv_app_def pp_T3_adv_op_eq_def)
qed

lemma pp_T3_adv_exists_fun_prime_everywhere:
  "\<forall>w. \<exists>p. pp_T3_adv_fun_prime w p"
proof (intro allI)
  fix w
  show "\<exists>p. pp_T3_adv_fun_prime w p"
  proof (cases w)
    case pp_T3_adv_root
    then show ?thesis
      using pp_T3_adv_fun_prime_witness by blast
  next
    case pp_T3_adv_tip
    then show ?thesis
      by (intro exI[of _ pp_T3_adv_x])
        (simp add: pp_T3_adv_fun_prime_def pp_T3_adv_op_eq_def)
  qed
qed

lemma pp_T3_adv_not_box_agreement_XY:
  "\<not> pp_T3_adv_box pp_T3_adv_root
    (\<lambda>v. \<forall>p.
      pp_T3_adv_app_eq v pp_T3_adv_X pp_T3_adv_Y p)"
proof
  assume boxed:
    "pp_T3_adv_box pp_T3_adv_root
      (\<lambda>v. \<forall>p.
        pp_T3_adv_app_eq v pp_T3_adv_X pp_T3_adv_Y p)"
  have all_at_root:
    "\<forall>p. pp_T3_adv_app_eq
      pp_T3_adv_root pp_T3_adv_X pp_T3_adv_Y p"
    using boxed
    by (simp add: pp_T3_adv_box_def pp_T3_adv_accessible_def)
  have "pp_T3_adv_app_eq
      pp_T3_adv_root pp_T3_adv_X pp_T3_adv_Y pp_T3_adv_r"
    using all_at_root by blast
  then show False
    by (simp add: pp_T3_adv_app_eq_def pp_T3_adv_prop_eq_def
      pp_T3_adv_app_def)
qed

lemma pp_T3_adv_not_box_agreement_YX:
  "\<not> pp_T3_adv_box pp_T3_adv_root
    (\<lambda>v. \<forall>p.
      pp_T3_adv_app_eq v pp_T3_adv_Y pp_T3_adv_X p)"
proof
  assume boxed:
    "pp_T3_adv_box pp_T3_adv_root
      (\<lambda>v. \<forall>p.
        pp_T3_adv_app_eq v pp_T3_adv_Y pp_T3_adv_X p)"
  have all_at_root:
    "\<forall>p. pp_T3_adv_app_eq
      pp_T3_adv_root pp_T3_adv_Y pp_T3_adv_X p"
    using boxed
    by (simp add: pp_T3_adv_box_def pp_T3_adv_accessible_def)
  have "pp_T3_adv_app_eq
      pp_T3_adv_root pp_T3_adv_Y pp_T3_adv_X pp_T3_adv_r"
    using all_at_root by blast
  then show False
    by (simp add: pp_T3_adv_app_eq_def pp_T3_adv_prop_eq_def
      pp_T3_adv_app_def)
qed

lemma pp_T3_adv_modalized_functionality_everywhere:
  "\<forall>w. pp_T3_adv_modalized_functionality w"
proof (intro allI)
  fix w
  show "pp_T3_adv_modalized_functionality w"
    unfolding pp_T3_adv_modalized_functionality_def
  proof (intro allI impI)
    fix F G
    assume boxed:
      "pp_T3_adv_box w
        (\<lambda>v. \<forall>p. pp_T3_adv_app_eq v F G p)"
    then show "pp_T3_adv_op_eq w F G"
      using pp_T3_adv_not_box_agreement_XY
        pp_T3_adv_not_box_agreement_YX
      by (cases w; cases F; cases G)
        (simp_all add: pp_T3_adv_op_eq_def)
  qed
qed

lemma pp_T3_adv_possible_fundamental_x:
  "pp_T3_adv_diamond pp_T3_adv_root
    (\<lambda>w. pp_T3_adv_fundamental w pp_T3_adv_x)"
  unfolding pp_T3_adv_diamond_def
  by (intro exI[of _ pp_T3_adv_tip])
    (simp add: pp_T3_adv_accessible_def pp_T3_adv_fundamental_def)

lemma pp_T3_adv_not_fun_prime_x:
  "\<not> pp_T3_adv_fun_prime pp_T3_adv_root pp_T3_adv_x"
proof
  assume fp:
    "pp_T3_adv_fun_prime pp_T3_adv_root pp_T3_adv_x"
  have pure_X:
    "pp_T3_adv_pure pp_T3_adv_root pp_T3_adv_X"
    by (simp add: pp_T3_adv_pure_def)
  have pure_Y:
    "pp_T3_adv_pure pp_T3_adv_root pp_T3_adv_Y"
    by (simp add: pp_T3_adv_pure_def)
  have applications_agree:
    "pp_T3_adv_app_eq
      pp_T3_adv_root pp_T3_adv_X pp_T3_adv_Y pp_T3_adv_x"
    by (simp add: pp_T3_adv_app_eq_def pp_T3_adv_prop_eq_def
      pp_T3_adv_app_def)
  have "pp_T3_adv_op_eq
      pp_T3_adv_root pp_T3_adv_X pp_T3_adv_Y"
    using fp pure_X pure_Y applications_agree
    unfolding pp_T3_adv_fun_prime_def by blast
  then show False
    by (simp add: pp_T3_adv_op_eq_def)
qed

theorem Goodman_T3_advertised_modal_abstraction_countermodel:
  "(\<forall>w. pp_T3_adv_accessible w w)
    \<and> (\<forall>u v w.
      pp_T3_adv_accessible u v \<longrightarrow>
      pp_T3_adv_accessible v w \<longrightarrow>
      pp_T3_adv_accessible u w)
    \<and> (\<forall>w F.
      pp_T3_adv_pure w F \<longrightarrow>
      pp_T3_adv_box w (\<lambda>v. pp_T3_adv_pure v F))
    \<and> (\<forall>w p q.
      pp_T3_adv_prop_eq w p q \<longrightarrow>
      pp_T3_adv_box w (\<lambda>v. pp_T3_adv_prop_eq v p q))
    \<and> (\<forall>w F G.
      pp_T3_adv_op_eq w F G \<longrightarrow>
      pp_T3_adv_box w (\<lambda>v. pp_T3_adv_op_eq v F G))
    \<and> (\<forall>w F G p.
      pp_T3_adv_app_eq w F G p \<longrightarrow>
      pp_T3_adv_box w (\<lambda>v. pp_T3_adv_app_eq v F G p))
    \<and> (\<forall>w. pp_T3_adv_QSS w)
    \<and> (\<forall>w. \<exists>p.
      pp_T3_adv_fundamental w p
      \<and> (\<forall>q. pp_T3_adv_fundamental w q
        \<longrightarrow> pp_T3_adv_prop_eq w q p))
    \<and> (\<forall>w. \<exists>p. pp_T3_adv_fun_prime w p)
    \<and> (\<forall>w. pp_T3_adv_modalized_functionality w)
    \<and> pp_T3_adv_diamond pp_T3_adv_root
      (\<lambda>w. pp_T3_adv_fundamental w pp_T3_adv_x)
    \<and> \<not> pp_T3_adv_fun_prime pp_T3_adv_root pp_T3_adv_x"
  using pp_T3_adv_frame_reflexive pp_T3_adv_frame_transitive
    pp_T3_adv_persistence pp_T3_adv_prop_identity_necessary
    pp_T3_adv_op_identity_necessary
    pp_T3_adv_application_identity_necessary
    pp_T3_adv_QSS_everywhere
    pp_T3_adv_unique_fundamental_everywhere
    pp_T3_adv_exists_fun_prime_everywhere
    pp_T3_adv_modalized_functionality_everywhere
    pp_T3_adv_possible_fundamental_x pp_T3_adv_not_fun_prime_x
  by blast

corollary Goodman_T3_advertised_modal_implication_fails:
  "\<not> (pp_T3_adv_diamond pp_T3_adv_root
      (\<lambda>w. pp_T3_adv_fundamental w pp_T3_adv_x)
    \<longrightarrow> pp_T3_adv_fun_prime pp_T3_adv_root pp_T3_adv_x)"
  using pp_T3_adv_possible_fundamental_x pp_T3_adv_not_fun_prime_x
  by blast

end
