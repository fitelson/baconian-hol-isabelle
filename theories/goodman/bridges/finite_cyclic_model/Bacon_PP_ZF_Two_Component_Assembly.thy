theory Bacon_PP_ZF_Two_Component_Assembly
  imports Bacon_PP_ZF_Finite_First_Cyclic_Package
begin

section \<open>Semantic assembly of a stabilized component and a successor\<close>

text \<open>
  The condensation graph schedules components, but a semantic construction
  must still use one interpretation of \<open>Pure\<close>.  We record a sufficient
  support condition under which adjoining a successor stock preserves the
  already stabilized component.

  The old application pairs can only acquire new premises when the successor
  adds pure objects at one of their argument or function types.  If the
  successor support avoids those source types, old application closure is
  inherited.  If it also avoids the unary-operator type and its classifier
  type, then both PP and the generic-seed Recombination condition are
  inherited.  Only application closure for the successor pairs remains as a
  new semantic obligation.
\<close>

definition pp_t_stock_union ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      (otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_stock_union Pure Added \<sigma> w x \<longleftrightarrow>
    Pure \<sigma> w x \<or> Added \<sigma> w x"

definition pp_t_stock_supported_on ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      otype set \<Rightarrow> bool"
where
  "pp_t_stock_supported_on Added S \<longleftrightarrow>
    (\<forall>\<sigma> w x. Added \<sigma> w x \<longrightarrow> \<sigma> \<in> S)"

definition pp_t_application_source_types ::
    "(otype \<times> otype) set \<Rightarrow> otype set"
where
  "pp_t_application_source_types E =
    {\<sigma>. \<exists>\<tau>. (\<sigma>, \<tau>) \<in> E}
    \<union> {\<sigma> \<rightarrow>\<^sub>o \<tau> |\<sigma> \<tau>. (\<sigma>, \<tau>) \<in> E}"

definition pp_t_stock_application_closed_on ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow> bool"
where
  "pp_t_stock_application_closed_on Pure E \<longleftrightarrow>
    (\<forall>\<sigma> \<tau>. (\<sigma>, \<tau>) \<in> E \<longrightarrow>
      (\<forall>w f x.
        Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        \<longrightarrow> Elem x (pp_t_domain \<sigma>)
        \<longrightarrow> Pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<longrightarrow> Pure \<sigma> w x
        \<longrightarrow> Pure \<tau> w (f \<acute> x)))"

definition pp_t_stock_self_classifies ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_t_stock_self_classifies Pure \<longleftrightarrow>
    (\<forall>w.
      Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_t_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (Pure (Prop \<rightarrow>\<^sub>o Prop))))"

definition pp_t_seed_recombines_stock ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      (bool list \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_t_seed_recombines_stock Pure seed \<longleftrightarrow>
    (\<forall>w.
      Elem (seed w) (pp_t_domain Prop)
      \<and> pp_t_unary_recombines_at
        (Pure (Prop \<rightarrow>\<^sub>o Prop)) (seed w) w)"

lemma pp_t_stock_union_admissible:
  assumes Pure:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Pure \<sigma>)"
    and Added:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Added \<sigma>)"
  shows "pp_t_predicate_admissible \<sigma>
    (pp_t_stock_union Pure Added \<sigma>)"
  using Pure[of \<sigma>] Added[of \<sigma>]
  unfolding pp_t_predicate_admissible_def
    pp_t_stock_union_def
  by blast

lemma pp_t_stock_supported_on_avoids:
  assumes support: "pp_t_stock_supported_on Added S"
    and outside: "\<sigma> \<notin> S"
  shows "\<not> Added \<sigma> w x"
  using support outside
  unfolding pp_t_stock_supported_on_def
  by blast

lemma pp_t_application_argument_is_source:
  assumes "(\<sigma>, \<tau>) \<in> E"
  shows "\<sigma> \<in> pp_t_application_source_types E"
  using assms
  unfolding pp_t_application_source_types_def
  by blast

lemma pp_t_application_function_is_source:
  assumes "(\<sigma>, \<tau>) \<in> E"
  shows "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
    \<in> pp_t_application_source_types E"
  using assms
  unfolding pp_t_application_source_types_def
  by blast

theorem pp_t_two_component_stock_assembly:
  fixes Pure Added ::
      "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
    and seed :: "bool list \<Rightarrow> ZF"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Pure \<sigma>)"
    and Added_admissible:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Added \<sigma>)"
    and support: "pp_t_stock_supported_on Added S"
    and old_sources:
      "S \<inter> pp_t_application_source_types E\<^sub>0 = {}"
    and avoids_unary: "(Prop \<rightarrow>\<^sub>o Prop) \<notin> S"
    and avoids_classifier:
      "((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) \<notin> S"
    and old_application:
      "pp_t_stock_application_closed_on Pure E\<^sub>0"
    and new_application:
      "pp_t_stock_application_closed_on
        (pp_t_stock_union Pure Added) E\<^sub>1"
    and old_PP: "pp_t_stock_self_classifies Pure"
    and old_recombination:
      "pp_t_seed_recombines_stock Pure seed"
  shows
    "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
        (pp_t_stock_union Pure Added \<sigma>))
    \<and> pp_t_stock_application_closed_on
        (pp_t_stock_union Pure Added) (E\<^sub>0 \<union> E\<^sub>1)
    \<and> pp_t_stock_self_classifies
        (pp_t_stock_union Pure Added)
    \<and> pp_t_seed_recombines_stock
        (pp_t_stock_union Pure Added) seed"
proof -
  have no_added_old_source:
      "\<sigma> \<in> pp_t_application_source_types E\<^sub>0
      \<Longrightarrow> \<not> Added \<sigma> w x"
    for \<sigma> w x
  proof -
    assume source:
        "\<sigma> \<in> pp_t_application_source_types E\<^sub>0"
    have "\<sigma> \<notin> S"
      using old_sources source by blast
    then show "\<not> Added \<sigma> w x"
      by (rule pp_t_stock_supported_on_avoids[OF support])
  qed
  have old_application_preserved:
      "pp_t_stock_application_closed_on
        (pp_t_stock_union Pure Added) E\<^sub>0"
    unfolding pp_t_stock_application_closed_on_def
  proof (intro allI impI)
    fix \<sigma> \<tau> w f x
    assume pair: "(\<sigma>, \<tau>) \<in> E\<^sub>0"
      and f: "Elem f (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      and x: "Elem x (pp_t_domain \<sigma>)"
      and pure_f:
        "pp_t_stock_union Pure Added
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
      and pure_x:
        "pp_t_stock_union Pure Added \<sigma> w x"
    have function_source:
        "(\<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<in> pp_t_application_source_types E\<^sub>0"
      by (rule pp_t_application_function_is_source[OF pair])
    have argument_source:
        "\<sigma> \<in> pp_t_application_source_types E\<^sub>0"
      by (rule pp_t_application_argument_is_source[OF pair])
    have base_f: "Pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f"
      using pure_f no_added_old_source[OF function_source]
      unfolding pp_t_stock_union_def by blast
    have base_x: "Pure \<sigma> w x"
      using pure_x no_added_old_source[OF argument_source]
      unfolding pp_t_stock_union_def by blast
    have base_output: "Pure \<tau> w (f \<acute> x)"
      using old_application pair f x base_f base_x
      unfolding pp_t_stock_application_closed_on_def
      by blast
    show "pp_t_stock_union Pure Added \<tau> w (f \<acute> x)"
      using base_output
      unfolding pp_t_stock_union_def by blast
  qed
  have application:
      "pp_t_stock_application_closed_on
        (pp_t_stock_union Pure Added) (E\<^sub>0 \<union> E\<^sub>1)"
    using old_application_preserved new_application
    unfolding pp_t_stock_application_closed_on_def
    by blast
  have unary_unchanged:
      "pp_t_stock_union Pure Added
          (Prop \<rightarrow>\<^sub>o Prop)
        = Pure (Prop \<rightarrow>\<^sub>o Prop)"
  proof (rule ext)+
    fix w x
    have "\<not> Added (Prop \<rightarrow>\<^sub>o Prop) w x"
      by (rule pp_t_stock_supported_on_avoids[
        OF support avoids_unary])
    then show
        "pp_t_stock_union Pure Added
            (Prop \<rightarrow>\<^sub>o Prop) w x
        = Pure (Prop \<rightarrow>\<^sub>o Prop) w x"
      unfolding pp_t_stock_union_def by blast
  qed
  have classifier_unchanged:
      "pp_t_stock_union Pure Added
          ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
        = Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)"
  proof (rule ext)+
    fix w x
    have "\<not> Added
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w x"
      by (rule pp_t_stock_supported_on_avoids[
        OF support avoids_classifier])
    then show
        "pp_t_stock_union Pure Added
            ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w x
        =
        Pure ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w x"
      unfolding pp_t_stock_union_def by blast
  qed
  have PP:
      "pp_t_stock_self_classifies
        (pp_t_stock_union Pure Added)"
    using old_PP
    unfolding pp_t_stock_self_classifies_def
      unary_unchanged classifier_unchanged .
  have recombination:
      "pp_t_seed_recombines_stock
        (pp_t_stock_union Pure Added) seed"
    using old_recombination
    unfolding pp_t_seed_recombines_stock_def
      unary_unchanged .
  show ?thesis
    using pp_t_stock_union_admissible[
        OF Pure_admissible Added_admissible]
      application PP recombination
    by blast
qed

subsection \<open>Finite successor rank\<close>

primrec pp_t_successor_stock ::
    "(otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      (nat \<Rightarrow> otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> nat \<Rightarrow>
      otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_successor_stock Pure Added 0 = Pure"
| "pp_t_successor_stock Pure Added (Suc n) =
    pp_t_stock_union
      (pp_t_successor_stock Pure Added n) (Added n)"

primrec pp_t_successor_application_pairs ::
    "(otype \<times> otype) set \<Rightarrow>
      (nat \<Rightarrow> (otype \<times> otype) set) \<Rightarrow>
      nat \<Rightarrow> (otype \<times> otype) set"
where
  "pp_t_successor_application_pairs E\<^sub>0 E 0 = E\<^sub>0"
| "pp_t_successor_application_pairs E\<^sub>0 E (Suc n) =
    pp_t_successor_application_pairs E\<^sub>0 E n \<union> E n"

theorem pp_t_finite_successor_rank_assembly:
  fixes Pure ::
      "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
    and Added ::
      "nat \<Rightarrow> otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
    and Supports :: "nat \<Rightarrow> otype set"
    and Pairs :: "nat \<Rightarrow> (otype \<times> otype) set"
    and seed :: "bool list \<Rightarrow> ZF"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma> (Pure \<sigma>)"
    and Added_admissible:
      "\<And>n \<sigma>. pp_t_predicate_admissible \<sigma> (Added n \<sigma>)"
    and support:
      "\<And>n. pp_t_stock_supported_on (Added n) (Supports n)"
    and old_sources:
      "\<And>n. Supports n \<inter> pp_t_application_source_types
        (pp_t_successor_application_pairs E\<^sub>0 Pairs n) = {}"
    and avoids_unary:
      "\<And>n. (Prop \<rightarrow>\<^sub>o Prop) \<notin> Supports n"
    and avoids_classifier:
      "\<And>n.
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
          \<notin> Supports n"
    and base_application:
      "pp_t_stock_application_closed_on Pure E\<^sub>0"
    and successor_application:
      "\<And>n. pp_t_stock_application_closed_on
        (pp_t_successor_stock Pure Added (Suc n)) (Pairs n)"
    and base_PP: "pp_t_stock_self_classifies Pure"
    and base_recombination:
      "pp_t_seed_recombines_stock Pure seed"
  shows
    "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
        (pp_t_successor_stock Pure Added n \<sigma>))
    \<and> pp_t_stock_application_closed_on
        (pp_t_successor_stock Pure Added n)
        (pp_t_successor_application_pairs E\<^sub>0 Pairs n)
    \<and> pp_t_stock_self_classifies
        (pp_t_successor_stock Pure Added n)
    \<and> pp_t_seed_recombines_stock
        (pp_t_successor_stock Pure Added n) seed"
proof (induction n)
  case 0
  show ?case
    using Pure_admissible base_application base_PP
      base_recombination
    by simp
next
  case (Suc n)
  have ih_admissible:
      "\<And>\<sigma>. pp_t_predicate_admissible \<sigma>
        (pp_t_successor_stock Pure Added n \<sigma>)"
    using Suc.IH by blast
  have ih_application:
      "pp_t_stock_application_closed_on
        (pp_t_successor_stock Pure Added n)
        (pp_t_successor_application_pairs E\<^sub>0 Pairs n)"
    using Suc.IH by blast
  have ih_PP:
      "pp_t_stock_self_classifies
        (pp_t_successor_stock Pure Added n)"
    using Suc.IH by blast
  have ih_recombination:
      "pp_t_seed_recombines_stock
        (pp_t_successor_stock Pure Added n) seed"
    using Suc.IH by blast
  have next_application:
      "pp_t_stock_application_closed_on
        (pp_t_stock_union
          (pp_t_successor_stock Pure Added n) (Added n))
        (Pairs n)"
    using successor_application[of n]
    by simp
  have assembled:
      "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
          (pp_t_stock_union
            (pp_t_successor_stock Pure Added n)
            (Added n) \<sigma>))
      \<and> pp_t_stock_application_closed_on
          (pp_t_stock_union
            (pp_t_successor_stock Pure Added n)
            (Added n))
          (pp_t_successor_application_pairs E\<^sub>0 Pairs n
            \<union> Pairs n)
      \<and> pp_t_stock_self_classifies
          (pp_t_stock_union
            (pp_t_successor_stock Pure Added n)
            (Added n))
      \<and> pp_t_seed_recombines_stock
          (pp_t_stock_union
            (pp_t_successor_stock Pure Added n)
            (Added n))
          seed"
    by (rule pp_t_two_component_stock_assembly[
      OF ih_admissible Added_admissible support old_sources
        avoids_unary avoids_classifier ih_application
        next_application ih_PP ih_recombination])
  show ?case
    using assembled by simp
qed

corollary pp_t_finite_successor_rank_preserves_PP:
  fixes Pure ::
      "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
    and Added ::
      "nat \<Rightarrow> otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
  assumes assembly:
    "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
        (pp_t_successor_stock Pure Added n \<sigma>))
    \<and> pp_t_stock_application_closed_on
        (pp_t_successor_stock Pure Added n)
        (pp_t_successor_application_pairs E\<^sub>0 Pairs n)
    \<and> pp_t_stock_self_classifies
        (pp_t_successor_stock Pure Added n)
    \<and> pp_t_seed_recombines_stock
        (pp_t_successor_stock Pure Added n) seed"
  shows "pp_t_stock_self_classifies
      (pp_t_successor_stock Pure Added n)"
    and "pp_t_seed_recombines_stock
      (pp_t_successor_stock Pure Added n) seed"
  using assembly by blast+

subsection \<open>Coverage boundary\<close>

lemma pp_t_component_separation_discharges_support_conditions:
  assumes sources:
      "pp_t_application_source_types E \<subseteq> Completed"
    and unary: "(Prop \<rightarrow>\<^sub>o Prop) \<in> Completed"
    and classifier:
      "((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
        \<in> Completed"
    and separate: "S \<inter> Completed = {}"
  shows "S \<inter> pp_t_application_source_types E = {}"
    and "(Prop \<rightarrow>\<^sub>o Prop) \<notin> S"
    and "((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
      \<notin> S"
  using assms by blast+

definition pp_t_successor_rank_covered ::
    "otype set \<Rightarrow> (otype \<times> otype) set \<Rightarrow> bool"
where
  "pp_t_successor_rank_covered S E \<longleftrightarrow>
    S \<inter> pp_t_application_source_types E = {}
    \<and> (Prop \<rightarrow>\<^sub>o Prop) \<notin> S
    \<and> ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
      \<notin> S"

lemma pp_t_successor_rank_covered_of_component_separation:
  assumes sources:
      "pp_t_application_source_types E \<subseteq> Completed"
    and unary: "(Prop \<rightarrow>\<^sub>o Prop) \<in> Completed"
    and classifier:
      "((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop)
        \<in> Completed"
    and separate: "S \<inter> Completed = {}"
  shows "pp_t_successor_rank_covered S E"
  using pp_t_component_separation_discharges_support_conditions[
    OF sources unary classifier separate]
  unfolding pp_t_successor_rank_covered_def
  by blast

theorem pp_t_classifier_component_not_successor_rank_covered:
  assumes "(Prop \<rightarrow>\<^sub>o Prop) \<in> S
    \<or> ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) \<in> S"
  shows "\<not> pp_t_successor_rank_covered S E"
  using assms
  unfolding pp_t_successor_rank_covered_def
  by blast

text \<open>
  Thus the rank theorem covers finite chains of strict successor components
  once each component has its own closure calculation.  It deliberately does
  not cover an enlargement of the classifier component itself: any such
  enlargement has support at \<open>U\<close> or \<open>C\<close> and violates the displayed
  side condition.  Internal stabilization of classifier-bearing cycles,
  including the \<open>fun\<acute>\<close>/T6 package, remains a separate obligation.
\<close>

section \<open>A finite collision-carrier rank for internal cycles\<close>

text \<open>
  Inside one classifier-bearing component, condensation rank is constant.
  A different finite rank is available when all successive pure-stock
  enlargements remain inside one finite carrier of semantic classes.  Each
  strict recomputation then removes at least one member from the complement
  of the current stock in that carrier.
\<close>

theorem pp_finite_collision_carrier_stabilizes:
  fixes F :: "'a set \<Rightarrow> 'a set"
  assumes finite: "finite V"
    and initial: "S \<subseteq> V"
    and closed: "\<And>X. X \<subseteq> V \<Longrightarrow> F X \<subseteq> V"
    and inflationary: "\<And>X. X \<subseteq> V \<Longrightarrow> X \<subseteq> F X"
  shows "\<exists>n.
    (F ^^ Suc n) S = (F ^^ n) S"
proof -
  have finite_complement: "finite (V - S)"
    using finite by simp
  have rank_claim:
      "\<And>(A :: 'a set). finite A \<Longrightarrow>
        \<forall>X. X \<subseteq> V \<longrightarrow> V - X = A
          \<longrightarrow> (\<exists>n.
            (F ^^ Suc n) X = (F ^^ n) X)"
  proof -
    fix A :: "'a set"
    assume "finite A"
    then show "\<forall>X. X \<subseteq> V \<longrightarrow> V - X = A
        \<longrightarrow> (\<exists>n.
          (F ^^ Suc n) X = (F ^^ n) X)"
    proof (induction rule: finite_psubset_induct)
      case (psubset A)
      show ?case
      proof (intro allI impI)
        fix X
        assume X: "X \<subseteq> V"
          and complement: "V - X = A"
        show "\<exists>n. (F ^^ Suc n) X = (F ^^ n) X"
        proof (cases "F X = X")
          case True
          show ?thesis
            by (rule exI[of _ 0]) (simp add: True)
        next
          case False
          have FX: "F X \<subseteq> V"
            by (rule closed[OF X])
          have X_FX: "X \<subseteq> F X"
            by (rule inflationary[OF X])
          have strict: "X \<subset> F X"
            using X_FX False by blast
          have complement_subset:
              "V - F X \<subseteq> V - X"
            using X_FX by blast
          obtain y where y_FX: "y \<in> F X"
              and y_not_X: "y \<notin> X"
            using strict by blast
          have y_V: "y \<in> V"
            using FX y_FX by blast
          have complement_not_subset:
              "\<not> V - X \<subseteq> V - F X"
            using y_V y_FX y_not_X by blast
          have smaller: "V - F X \<subset> A"
            using complement complement_subset
              complement_not_subset
            by blast
          obtain n where fixed:
              "(F ^^ Suc n) (F X) = (F ^^ n) (F X)"
            using psubset.IH[OF smaller, rule_format,
              OF FX refl]
            by metis
          have shifted:
              "(F ^^ Suc (Suc n)) X = (F ^^ Suc n) X"
            using fixed
            by (simp only: funpow_Suc_right comp_apply)
          show ?thesis
            by (rule exI[of _ "Suc n"]) (rule shifted)
        qed
      qed
    qed
  qed
  show ?thesis
    using rank_claim[OF finite_complement, rule_format,
      OF initial refl] .
qed

definition pp_finite_collision_carrier ::
    "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "pp_finite_collision_carrier V F \<longleftrightarrow>
    finite V
    \<and> (\<forall>X \<subseteq> V. F X \<subseteq> V)
    \<and> (\<forall>X \<subseteq> V. X \<subseteq> F X)"

corollary pp_finite_collision_carrier_has_finite_fixed_stage:
  assumes carrier: "pp_finite_collision_carrier V F"
    and initial: "S \<subseteq> V"
  shows "\<exists>n.
    (F ^^ Suc n) S = (F ^^ n) S"
proof -
  from carrier have finite: "finite V"
    and closed: "\<And>X. X \<subseteq> V \<Longrightarrow> F X \<subseteq> V"
    and inflationary:
      "\<And>X. X \<subseteq> V \<Longrightarrow> X \<subseteq> F X"
    unfolding pp_finite_collision_carrier_def
    by auto
  show ?thesis
    by (rule pp_finite_collision_carrier_stabilizes[
          OF finite initial closed inflationary])
qed

text \<open>
  This criterion covers the verified finite-family and two-stage examples:
  their collision characterizations exhibit a finite carrier closed under
  recomputation.  For the \<open>fun\<acute>\<close>/T6 cycle, the displayed ten classes
  are not yet known to form such a carrier.  Proving finite-carrier closure
  would give finite-stage stabilization; proving that every proposed finite
  carrier has a generated escape would refute this rank strategy without
  itself proving inconsistency.
\<close>

section \<open>A concrete two-component interpretation\<close>

text \<open>
  We now adjoin the proposition-result successor of the verified first
  classifier cycle.  The old component uses the application pair
  \<open>(C,U)\<close>, where \<open>U = Prop \<rightarrow> Prop\<close> and
  \<open>C = U \<rightarrow> Prop\<close>.  The successor uses \<open>(U,Prop)\<close>.
  Its function type is precisely \<open>C\<close>, so PP supplies a pure function;
  its arguments are the old pure unary operators.  We close the successor
  by making all proposition-domain outputs pure.  This changes neither the
  unary stock nor its classifier.
\<close>

definition pp_t_first_cyclic_proposition_successor ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_first_cyclic_proposition_successor \<sigma> w x \<longleftrightarrow>
    \<sigma> = Prop \<and> Elem x (pp_t_domain Prop)"

definition pp_t_first_cyclic_two_component_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_first_cyclic_two_component_pure =
    pp_t_stock_union pp_t_first_cyclic_pure
      pp_t_first_cyclic_proposition_successor"

lemma pp_t_first_cyclic_proposition_successor_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_first_cyclic_proposition_successor \<sigma>)"
  unfolding pp_t_predicate_admissible_def
    pp_t_first_cyclic_proposition_successor_def
  by blast

lemma pp_t_first_cyclic_proposition_successor_support:
  "pp_t_stock_supported_on
    pp_t_first_cyclic_proposition_successor {Prop}"
  unfolding pp_t_stock_supported_on_def
    pp_t_first_cyclic_proposition_successor_def
  by blast

lemma pp_t_first_cyclic_base_application_closed:
  "pp_t_stock_application_closed_on pp_t_first_cyclic_pure
    {(pp_t_first_cyclic_classifier_type,
      pp_t_first_cyclic_unary_type)}"
  unfolding pp_t_stock_application_closed_on_def
  using pp_t_first_cyclic_application_absorbed
  by blast

lemma pp_t_first_cyclic_successor_application_closed:
  "pp_t_stock_application_closed_on
    pp_t_first_cyclic_two_component_pure
    {(pp_t_first_cyclic_unary_type, Prop)}"
  unfolding pp_t_stock_application_closed_on_def
    pp_t_first_cyclic_two_component_pure_def
    pp_t_stock_union_def
    pp_t_first_cyclic_proposition_successor_def
  using pp_t_app_closed
  by blast

lemma pp_t_first_cyclic_stock_self_classifies:
  "pp_t_stock_self_classifies pp_t_first_cyclic_pure"
  unfolding pp_t_stock_self_classifies_def
    pp_t_first_cyclic_unary_classifier
  using pp_t_first_cyclic_classifier_is_pure
  by blast

lemma pp_t_first_cyclic_seed_recombines_stock:
  "pp_t_seed_recombines_stock pp_t_first_cyclic_pure
    pp_t_generic_seed_at"
  unfolding pp_t_seed_recombines_stock_def
    pp_t_first_cyclic_pure_unary
  using pp_t_generic_seed_at_in_domain
    pp_t_generic_seed_recombines_at_every_world
  by blast

theorem pp_t_first_cyclic_two_component_assembly:
  "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
      (pp_t_first_cyclic_two_component_pure \<sigma>))
  \<and> pp_t_stock_application_closed_on
      pp_t_first_cyclic_two_component_pure
      {(pp_t_first_cyclic_classifier_type,
          pp_t_first_cyclic_unary_type),
       (pp_t_first_cyclic_unary_type, Prop)}
  \<and> pp_t_stock_self_classifies
      pp_t_first_cyclic_two_component_pure
  \<and> pp_t_seed_recombines_stock
      pp_t_first_cyclic_two_component_pure
      pp_t_generic_seed_at"
proof -
  have source_disjoint:
      "{Prop} \<inter> pp_t_application_source_types
        {(pp_t_first_cyclic_classifier_type,
          pp_t_first_cyclic_unary_type)} = {}"
    unfolding pp_t_application_source_types_def
    by simp
  have successor_application:
      "pp_t_stock_application_closed_on
        (pp_t_stock_union pp_t_first_cyclic_pure
          pp_t_first_cyclic_proposition_successor)
        {(pp_t_first_cyclic_unary_type, Prop)}"
    using pp_t_first_cyclic_successor_application_closed
    unfolding pp_t_first_cyclic_two_component_pure_def .
  have pair_union:
      "{(pp_t_first_cyclic_classifier_type,
          pp_t_first_cyclic_unary_type),
        (pp_t_first_cyclic_unary_type, Prop)}
      =
      {(pp_t_first_cyclic_classifier_type,
          pp_t_first_cyclic_unary_type)}
      \<union> {(pp_t_first_cyclic_unary_type, Prop)}"
    by blast
  have assembled:
      "(\<forall>\<sigma>. pp_t_predicate_admissible \<sigma>
          (pp_t_stock_union pp_t_first_cyclic_pure
            pp_t_first_cyclic_proposition_successor \<sigma>))
      \<and> pp_t_stock_application_closed_on
          (pp_t_stock_union pp_t_first_cyclic_pure
            pp_t_first_cyclic_proposition_successor)
          ({(pp_t_first_cyclic_classifier_type,
              pp_t_first_cyclic_unary_type)}
           \<union> {(pp_t_first_cyclic_unary_type, Prop)})
      \<and> pp_t_stock_self_classifies
          (pp_t_stock_union pp_t_first_cyclic_pure
            pp_t_first_cyclic_proposition_successor)
      \<and> pp_t_seed_recombines_stock
          (pp_t_stock_union pp_t_first_cyclic_pure
            pp_t_first_cyclic_proposition_successor)
          pp_t_generic_seed_at"
    by (rule pp_t_two_component_stock_assembly[
      OF pp_t_first_cyclic_pure_admissible
        pp_t_first_cyclic_proposition_successor_admissible
        pp_t_first_cyclic_proposition_successor_support
        source_disjoint])
      (simp_all add:
        pp_t_first_cyclic_base_application_closed
        successor_application
        pp_t_first_cyclic_stock_self_classifies
        pp_t_first_cyclic_seed_recombines_stock)
  show ?thesis
    using assembled
    unfolding pp_t_first_cyclic_two_component_pure_def
      pair_union .
qed

section \<open>The corresponding finite application graph\<close>

definition pp_finite_first_cyclic_with_proposition_successor ::
    "oterm set"
where
  "pp_finite_first_cyclic_with_proposition_successor =
    pp_finite_first_cyclic_package
    \<union> {
      pp_application_closure
        pp_t_first_cyclic_unary_type Prop}"

lemma pp_finite_first_cyclic_with_proposition_successor_finite:
  "finite pp_finite_first_cyclic_with_proposition_successor"
  unfolding
    pp_finite_first_cyclic_with_proposition_successor_def
  using pp_finite_first_cyclic_package_finite
  by simp

lemma pp_finite_first_cyclic_with_proposition_successor_subset:
  "pp_finite_first_cyclic_with_proposition_successor
    \<subseteq> pp_recombination_PP_axioms"
proof -
  have application:
      "pp_application_closure
          pp_t_first_cyclic_unary_type Prop
        \<in> pp_application_closure_schema"
    unfolding pp_application_closure_schema_def
    by blast
  show ?thesis
    using pp_finite_first_cyclic_package_subset application
    unfolding
      pp_finite_first_cyclic_with_proposition_successor_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def
      pp_background_axioms_def
    by blast
qed

definition pp_t_first_cyclic_two_component_pairs ::
    "(otype \<times> otype) set"
where
  "pp_t_first_cyclic_two_component_pairs = {
    (pp_t_first_cyclic_classifier_type,
      pp_t_first_cyclic_unary_type),
    (pp_t_first_cyclic_unary_type, Prop)}"

theorem pp_t_first_cyclic_proposition_is_strict_successor:
  "(pp_t_first_cyclic_unary_type, Prop)
    \<in> pp_finite_component_precedes
      pp_t_first_cyclic_two_component_pairs"
proof -
  let ?R =
    "pp_finite_PP_dependency
      pp_t_first_cyclic_two_component_pairs"
  have dependency:
      "?R = {
        (pp_t_first_cyclic_unary_type,
          pp_t_first_cyclic_classifier_type),
        (pp_t_first_cyclic_classifier_type,
          pp_t_first_cyclic_unary_type),
        (pp_t_first_cyclic_builder_type,
          pp_t_first_cyclic_unary_type),
        (pp_t_first_cyclic_unary_type, Prop),
        (pp_t_first_cyclic_classifier_type, Prop)}"
    unfolding pp_finite_PP_dependency_def
      pp_finite_application_dependency_def
      pp_t_first_cyclic_two_component_pairs_def
    by auto
  have forward:
      "(pp_t_first_cyclic_unary_type, Prop) \<in> ?R\<^sup>*"
  proof -
    have "(pp_t_first_cyclic_unary_type, Prop) \<in> ?R"
      unfolding dependency by simp
    then show ?thesis by (rule r_into_rtrancl)
  qed
  have forward_strict:
      "(pp_t_first_cyclic_unary_type, Prop) \<in> ?R\<^sup>+"
  proof -
    have "(pp_t_first_cyclic_unary_type, Prop) \<in> ?R"
      unfolding dependency by simp
    then show ?thesis by (rule r_into_trancl)
  qed
  have proposition_reaches_only_itself:
      "(Prop, \<sigma>) \<in> ?R\<^sup>* \<Longrightarrow> \<sigma> = Prop"
    for \<sigma>
    unfolding dependency
  proof (induction rule: rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    then show ?case by auto
  qed
  have no_return:
      "(Prop, pp_t_first_cyclic_unary_type) \<notin> ?R\<^sup>*"
  proof
    assume "(Prop, pp_t_first_cyclic_unary_type) \<in> ?R\<^sup>*"
    then have "pp_t_first_cyclic_unary_type = Prop"
      by (rule proposition_reaches_only_itself)
    then show False by simp
  qed
  show ?thesis
    using forward forward_strict no_return
    unfolding pp_finite_component_precedes_def
      pp_finite_same_component_def
    by blast
qed

theorem pp_t_first_cyclic_two_component_checkpoint:
  "finite pp_finite_first_cyclic_with_proposition_successor
  \<and> pp_finite_first_cyclic_with_proposition_successor
      \<subseteq> pp_recombination_PP_axioms
  \<and> (pp_t_first_cyclic_unary_type, Prop)
      \<in> pp_finite_component_precedes
        pp_t_first_cyclic_two_component_pairs
  \<and> pp_t_stock_application_closed_on
      pp_t_first_cyclic_two_component_pure
      pp_t_first_cyclic_two_component_pairs
  \<and> pp_t_stock_self_classifies
      pp_t_first_cyclic_two_component_pure
  \<and> pp_t_seed_recombines_stock
      pp_t_first_cyclic_two_component_pure
      pp_t_generic_seed_at"
  using
    pp_finite_first_cyclic_with_proposition_successor_finite
    pp_finite_first_cyclic_with_proposition_successor_subset
    pp_t_first_cyclic_proposition_is_strict_successor
    pp_t_first_cyclic_two_component_assembly
  unfolding pp_t_first_cyclic_two_component_pairs_def
  by blast

end
