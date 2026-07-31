theory Bacon_PP_Finite_Application_Graph
  imports Bacon_PP_Fresh_Finite_Fragment
begin

section \<open>Finite application graphs and classifier feedback\<close>

abbreviation pp_finite_unary_type :: otype where
  "pp_finite_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_finite_classifier_type :: otype where
  "pp_finite_classifier_type \<equiv>
    pp_finite_unary_type \<rightarrow>\<^sub>o Prop"

text \<open>
  If application closure is required at the pair \<open>(\<sigma>,\<tau>)\<close>, then
  purity at the result type \<open>\<tau>\<close> can depend both on purity at the argument
  type \<open>\<sigma>\<close> and on purity at the function type \<open>\<sigma> \<rightarrow>\<^sub>o \<tau>\<close>.
  The following relation records exactly those two dependencies.
\<close>

definition pp_finite_application_dependency ::
    "(otype \<times> otype) set \<Rightarrow> (otype \<times> otype) set" where
  "pp_finite_application_dependency E =
    E \<union> ((\<lambda>p. (fst p \<rightarrow>\<^sub>o snd p, snd p)) ` E)"

lemma pp_finite_application_dependency_argument:
  assumes "(\<sigma>, \<tau>) \<in> E"
  shows "(\<sigma>, \<tau>) \<in> pp_finite_application_dependency E"
  using assms
  unfolding pp_finite_application_dependency_def by blast

lemma pp_finite_application_dependency_function:
  assumes "(\<sigma>, \<tau>) \<in> E"
  shows "(\<sigma> \<rightarrow>\<^sub>o \<tau>, \<tau>)
    \<in> pp_finite_application_dependency E"
  using assms
  unfolding pp_finite_application_dependency_def by force

lemma pp_finite_application_dependency_finite:
  assumes "finite E"
  shows "finite (pp_finite_application_dependency E)"
  using assms
  unfolding pp_finite_application_dependency_def by simp

text \<open>
  PP makes the purity classifier at the unary-operator type pure at the
  classifier type.  A feedback cycle is therefore present exactly when the
  application dependencies can carry purity from the classifier type back to
  the unary-operator type.  Other cycles in the finite application graph are
  harmless for this particular stabilization question.
\<close>

definition pp_finite_classifier_acyclic ::
    "(otype \<times> otype) set \<Rightarrow> bool" where
  "pp_finite_classifier_acyclic E \<longleftrightarrow>
    (pp_finite_classifier_type, pp_finite_unary_type)
      \<notin> (pp_finite_application_dependency E)\<^sup>*"

datatype pp_finite_stock_expr =
    PPFiniteLogical oterm
  | PPFiniteClassifier
  | PPFiniteApply pp_finite_stock_expr pp_finite_stock_expr

fun pp_finite_expr_has_classifier ::
    "pp_finite_stock_expr \<Rightarrow> bool" where
  "pp_finite_expr_has_classifier (PPFiniteLogical M) = False"
| "pp_finite_expr_has_classifier PPFiniteClassifier = True"
| "pp_finite_expr_has_classifier (PPFiniteApply F X) =
    (pp_finite_expr_has_classifier F
      \<or> pp_finite_expr_has_classifier X)"

inductive pp_finite_expr_typed ::
    "(otype \<times> oterm) set \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow>
      pp_finite_stock_expr \<Rightarrow> otype \<Rightarrow> bool"
where
  Logical:
    "\<lbrakk>(\<sigma>, M) \<in> L; [] \<turnstile> M : \<sigma>\<rbrakk>
      \<Longrightarrow> pp_finite_expr_typed L E
        (PPFiniteLogical M) \<sigma>"
| Classifier:
    "pp_finite_expr_typed L E PPFiniteClassifier
      pp_finite_classifier_type"
| Apply:
    "\<lbrakk>pp_finite_expr_typed L E F (\<sigma> \<rightarrow>\<^sub>o \<tau>);
      pp_finite_expr_typed L E X \<sigma>;
      (\<sigma>, \<tau>) \<in> E\<rbrakk>
      \<Longrightarrow> pp_finite_expr_typed L E
        (PPFiniteApply F X) \<tau>"

lemma pp_finite_classifier_occurrence_gives_dependency_path:
  assumes typed: "pp_finite_expr_typed L E T \<tau>"
    and occurrence: "pp_finite_expr_has_classifier T"
  shows "(pp_finite_classifier_type, \<tau>)
    \<in> (pp_finite_application_dependency E)\<^sup>*"
  using typed occurrence
proof (induction rule: pp_finite_expr_typed.induct)
  case (Logical \<sigma> M L E)
  then show ?case by simp
next
  case (Classifier L E)
  then show ?case by simp
next
  case (Apply L E F \<sigma> \<tau> X)
  let ?R = "pp_finite_application_dependency E"
  have function_step: "(\<sigma> \<rightarrow>\<^sub>o \<tau>, \<tau>) \<in> ?R"
    using Apply.hyps(3)
    by (rule pp_finite_application_dependency_function)
  have argument_step: "(\<sigma>, \<tau>) \<in> ?R"
    using Apply.hyps(3)
    by (rule pp_finite_application_dependency_argument)
  from Apply.prems consider
      (fun_side) "pp_finite_expr_has_classifier F"
    | (arg_side) "pp_finite_expr_has_classifier X"
    by auto
  then show ?case
  proof cases
    case fun_side
    have path:
        "(pp_finite_classifier_type, \<sigma> \<rightarrow>\<^sub>o \<tau>)
          \<in> ?R\<^sup>*"
      using Apply.IH(1)[OF fun_side] .
    show ?thesis
      using path function_step
      by (rule rtrancl_into_rtrancl)
  next
    case arg_side
    have path:
        "(pp_finite_classifier_type, \<sigma>) \<in> ?R\<^sup>*"
      using Apply.IH(2)[OF arg_side] .
    show ?thesis
      using path argument_step
      by (rule rtrancl_into_rtrancl)
  qed
qed

definition pp_finite_unary_expressions ::
    "(otype \<times> oterm) set \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow>
      pp_finite_stock_expr set" where
  "pp_finite_unary_expressions L E =
    {T. pp_finite_expr_typed L E T pp_finite_unary_type}"

definition pp_finite_classifier_free_unary_expressions ::
    "(otype \<times> oterm) set \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow>
      pp_finite_stock_expr set" where
  "pp_finite_classifier_free_unary_expressions L E =
    {T. pp_finite_expr_typed L E T pp_finite_unary_type
      \<and> \<not> pp_finite_expr_has_classifier T}"

theorem pp_finite_acyclic_unary_stabilization:
  assumes acyclic: "pp_finite_classifier_acyclic E"
  shows "pp_finite_unary_expressions L E =
    pp_finite_classifier_free_unary_expressions L E"
proof
  show "pp_finite_unary_expressions L E
      \<subseteq> pp_finite_classifier_free_unary_expressions L E"
  proof
    fix T
    assume T: "T \<in> pp_finite_unary_expressions L E"
    then have typed:
        "pp_finite_expr_typed L E T pp_finite_unary_type"
      unfolding pp_finite_unary_expressions_def by simp
    have "\<not> pp_finite_expr_has_classifier T"
    proof
      assume occurrence: "pp_finite_expr_has_classifier T"
      have "(pp_finite_classifier_type, pp_finite_unary_type)
          \<in> (pp_finite_application_dependency E)\<^sup>*"
        using pp_finite_classifier_occurrence_gives_dependency_path[
          OF typed occurrence] .
      then show False
        using acyclic
        unfolding pp_finite_classifier_acyclic_def by blast
    qed
    then show
        "T \<in> pp_finite_classifier_free_unary_expressions L E"
      using typed
      unfolding pp_finite_classifier_free_unary_expressions_def
      by simp
  qed
  show "pp_finite_classifier_free_unary_expressions L E
      \<subseteq> pp_finite_unary_expressions L E"
    unfolding pp_finite_classifier_free_unary_expressions_def
      pp_finite_unary_expressions_def
    by blast
qed

subsection \<open>Denotational stabilization\<close>

fun pp_finite_expr_den ::
    "(oterm \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      pp_finite_stock_expr \<Rightarrow> 'a" where
  "pp_finite_expr_den logical classifier app
      (PPFiniteLogical M) = logical M"
| "pp_finite_expr_den logical classifier app
      PPFiniteClassifier = classifier"
| "pp_finite_expr_den logical classifier app
      (PPFiniteApply F X) =
    app
      (pp_finite_expr_den logical classifier app F)
      (pp_finite_expr_den logical classifier app X)"

definition pp_finite_generated_unary_values ::
    "(oterm \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      (otype \<times> oterm) set \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow> 'a set" where
  "pp_finite_generated_unary_values logical classifier app L E =
    pp_finite_expr_den logical classifier app `
      pp_finite_unary_expressions L E"

definition pp_finite_classifier_free_unary_values ::
    "(oterm \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
      (otype \<times> oterm) set \<Rightarrow>
      (otype \<times> otype) set \<Rightarrow> 'a set" where
  "pp_finite_classifier_free_unary_values
      logical classifier app L E =
    pp_finite_expr_den logical classifier app `
      pp_finite_classifier_free_unary_expressions L E"

theorem pp_finite_acyclic_generated_unary_values_stabilize:
  assumes "pp_finite_classifier_acyclic E"
  shows "pp_finite_generated_unary_values
      logical classifier app L E
    = pp_finite_classifier_free_unary_values
      logical classifier app L E"
  unfolding pp_finite_generated_unary_values_def
    pp_finite_classifier_free_unary_values_def
  using pp_finite_acyclic_unary_stabilization[OF assms]
  by simp

corollary pp_finite_acyclic_unary_values_independent_of_classifier:
  assumes "pp_finite_classifier_acyclic E"
  shows "pp_finite_generated_unary_values
      logical classifier\<^sub>1 app L E
    = pp_finite_generated_unary_values
      logical classifier\<^sub>2 app L E"
proof -
  have expressions:
      "pp_finite_unary_expressions L E =
        pp_finite_classifier_free_unary_expressions L E"
    using assms by (rule pp_finite_acyclic_unary_stabilization)
  have classifier_free:
      "\<And>T c\<^sub>1 c\<^sub>2.
        \<not> pp_finite_expr_has_classifier T
        \<Longrightarrow>
        pp_finite_expr_den logical c\<^sub>1 app T =
          pp_finite_expr_den logical c\<^sub>2 app T"
  proof -
    fix T c\<^sub>1 c\<^sub>2
    assume "\<not> pp_finite_expr_has_classifier T"
    then show
        "pp_finite_expr_den logical c\<^sub>1 app T =
          pp_finite_expr_den logical c\<^sub>2 app T"
      by (induction T) simp_all
  qed
  show ?thesis
    unfolding pp_finite_generated_unary_values_def
    unfolding expressions
  proof
    show "pp_finite_expr_den logical classifier\<^sub>1 app `
        pp_finite_classifier_free_unary_expressions L E
      \<subseteq>
      pp_finite_expr_den logical classifier\<^sub>2 app `
        pp_finite_classifier_free_unary_expressions L E"
    proof
      fix y
      assume "y \<in> pp_finite_expr_den logical classifier\<^sub>1 app `
          pp_finite_classifier_free_unary_expressions L E"
      then obtain T where
          T: "T \<in> pp_finite_classifier_free_unary_expressions L E"
        and y: "y = pp_finite_expr_den logical classifier\<^sub>1 app T"
        by blast
      have no_classifier: "\<not> pp_finite_expr_has_classifier T"
        using T
        unfolding pp_finite_classifier_free_unary_expressions_def
        by blast
      have equality:
          "pp_finite_expr_den logical classifier\<^sub>1 app T =
            pp_finite_expr_den logical classifier\<^sub>2 app T"
        using classifier_free[OF no_classifier] .
      have y2: "y = pp_finite_expr_den logical classifier\<^sub>2 app T"
        using y equality by simp
      show "y \<in> pp_finite_expr_den logical classifier\<^sub>2 app `
          pp_finite_classifier_free_unary_expressions L E"
        using T y2 by blast
    qed
    show "pp_finite_expr_den logical classifier\<^sub>2 app `
        pp_finite_classifier_free_unary_expressions L E
      \<subseteq>
      pp_finite_expr_den logical classifier\<^sub>1 app `
        pp_finite_classifier_free_unary_expressions L E"
    proof
      fix y
      assume "y \<in> pp_finite_expr_den logical classifier\<^sub>2 app `
          pp_finite_classifier_free_unary_expressions L E"
      then obtain T where
          T: "T \<in> pp_finite_classifier_free_unary_expressions L E"
        and y: "y = pp_finite_expr_den logical classifier\<^sub>2 app T"
        by blast
      have no_classifier: "\<not> pp_finite_expr_has_classifier T"
        using T
        unfolding pp_finite_classifier_free_unary_expressions_def
        by blast
      have equality:
          "pp_finite_expr_den logical classifier\<^sub>1 app T =
            pp_finite_expr_den logical classifier\<^sub>2 app T"
        using classifier_free[OF no_classifier] .
      have y1: "y = pp_finite_expr_den logical classifier\<^sub>1 app T"
        using y equality by simp
      show "y \<in> pp_finite_expr_den logical classifier\<^sub>1 app `
          pp_finite_classifier_free_unary_expressions L E"
        using T y1 by blast
    qed
  qed
qed

section \<open>Strongly connected components\<close>

text \<open>
  The preceding dependency relation records application closure alone.  PP
  contributes one further dependency: the unary pure stock determines its
  classifier.  We therefore add the edge from the unary type to the
  classifier type before taking strongly connected components.
\<close>

definition pp_finite_PP_dependency ::
    "(otype \<times> otype) set \<Rightarrow> (otype \<times> otype) set" where
  "pp_finite_PP_dependency E =
    insert (pp_finite_unary_type, pp_finite_classifier_type)
      (pp_finite_application_dependency E)"

lemma pp_finite_PP_dependency_finite:
  assumes "finite E"
  shows "finite (pp_finite_PP_dependency E)"
  using pp_finite_application_dependency_finite[OF assms]
  unfolding pp_finite_PP_dependency_def by simp

definition pp_finite_same_component ::
    "(otype \<times> otype) set \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> bool"
where
  "pp_finite_same_component E \<sigma> \<tau> \<longleftrightarrow>
    (\<sigma>, \<tau>) \<in> (pp_finite_PP_dependency E)\<^sup>*
    \<and> (\<tau>, \<sigma>) \<in> (pp_finite_PP_dependency E)\<^sup>*"

lemma pp_finite_same_component_refl:
  "pp_finite_same_component E \<sigma> \<sigma>"
  unfolding pp_finite_same_component_def by simp

lemma pp_finite_same_component_sym:
  assumes "pp_finite_same_component E \<sigma> \<tau>"
  shows "pp_finite_same_component E \<tau> \<sigma>"
  using assms unfolding pp_finite_same_component_def by blast

lemma pp_finite_same_component_trans:
  assumes st: "pp_finite_same_component E \<sigma> \<tau>"
    and tu: "pp_finite_same_component E \<tau> \<upsilon>"
  shows "pp_finite_same_component E \<sigma> \<upsilon>"
  using st tu
  unfolding pp_finite_same_component_def
  by (blast intro: rtrancl_trans)

definition pp_finite_component ::
    "(otype \<times> otype) set \<Rightarrow> otype \<Rightarrow> otype set" where
  "pp_finite_component E \<sigma> =
    {\<tau>. pp_finite_same_component E \<sigma> \<tau>}"

definition pp_finite_components ::
    "(otype \<times> otype) set \<Rightarrow> otype set set" where
  "pp_finite_components E =
    pp_finite_component E ` Field (pp_finite_PP_dependency E)"

lemma pp_finite_component_self:
  "\<sigma> \<in> pp_finite_component E \<sigma>"
  unfolding pp_finite_component_def
  using pp_finite_same_component_refl by simp

lemma pp_finite_component_eq_if_same:
  assumes same: "pp_finite_same_component E \<sigma> \<tau>"
  shows "pp_finite_component E \<sigma> =
    pp_finite_component E \<tau>"
proof
  show "pp_finite_component E \<sigma>
      \<subseteq> pp_finite_component E \<tau>"
  proof
    fix \<upsilon>
    assume "\<upsilon> \<in> pp_finite_component E \<sigma>"
    then have sv:
        "pp_finite_same_component E \<sigma> \<upsilon>"
      unfolding pp_finite_component_def by simp
    have ts: "pp_finite_same_component E \<tau> \<sigma>"
      using pp_finite_same_component_sym[OF same] .
    have "pp_finite_same_component E \<tau> \<upsilon>"
      using pp_finite_same_component_trans[OF ts sv] .
    then show "\<upsilon> \<in> pp_finite_component E \<tau>"
      unfolding pp_finite_component_def by simp
  qed
  show "pp_finite_component E \<tau>
      \<subseteq> pp_finite_component E \<sigma>"
  proof
    fix \<upsilon>
    assume "\<upsilon> \<in> pp_finite_component E \<tau>"
    then have tv:
        "pp_finite_same_component E \<tau> \<upsilon>"
      unfolding pp_finite_component_def by simp
    have "pp_finite_same_component E \<sigma> \<upsilon>"
      using pp_finite_same_component_trans[OF same tv] .
    then show "\<upsilon> \<in> pp_finite_component E \<sigma>"
      unfolding pp_finite_component_def by simp
  qed
qed

lemma pp_finite_component_overlap_imp_eq:
  assumes overlap:
      "pp_finite_component E \<sigma>
        \<inter> pp_finite_component E \<tau> \<noteq> {}"
  shows "pp_finite_component E \<sigma> =
    pp_finite_component E \<tau>"
proof -
  obtain \<upsilon> where
      sv: "pp_finite_same_component E \<sigma> \<upsilon>"
    and tv: "pp_finite_same_component E \<tau> \<upsilon>"
    using overlap
    unfolding pp_finite_component_def by blast
  have vt: "pp_finite_same_component E \<upsilon> \<tau>"
    using pp_finite_same_component_sym[OF tv] .
  have st: "pp_finite_same_component E \<sigma> \<tau>"
    using pp_finite_same_component_trans[OF sv vt] .
  show ?thesis
    using pp_finite_component_eq_if_same[OF st] .
qed

theorem pp_finite_components_partition:
  assumes A: "A \<in> pp_finite_components E"
    and B: "B \<in> pp_finite_components E"
  shows "A = B \<or> A \<inter> B = {}"
proof -
  obtain \<sigma> where A_eq:
      "A = pp_finite_component E \<sigma>"
    using A unfolding pp_finite_components_def by blast
  obtain \<tau> where B_eq:
      "B = pp_finite_component E \<tau>"
    using B unfolding pp_finite_components_def by blast
  show ?thesis
  proof (cases "A \<inter> B = {}")
    case True
    then show ?thesis by blast
  next
    case False
    have "pp_finite_component E \<sigma> =
        pp_finite_component E \<tau>"
      using pp_finite_component_overlap_imp_eq[of E \<sigma> \<tau>]
        False
      unfolding A_eq B_eq .
    then show ?thesis
      unfolding A_eq B_eq by blast
  qed
qed

lemma pp_finite_components_cover:
  assumes "\<sigma> \<in> Field (pp_finite_PP_dependency E)"
  shows "\<exists>A \<in> pp_finite_components E. \<sigma> \<in> A"
  using assms pp_finite_component_self[of \<sigma> E]
  unfolding pp_finite_components_def by blast

theorem pp_finite_components_finite:
  assumes "finite E"
  shows "finite (pp_finite_components E)"
  unfolding pp_finite_components_def
  using finite_Field[
    OF pp_finite_PP_dependency_finite[OF assms]]
  by simp

definition pp_finite_component_precedes ::
    "(otype \<times> otype) set \<Rightarrow> (otype \<times> otype) set"
where
  "pp_finite_component_precedes E =
    {(\<sigma>, \<tau>).
      (\<sigma>, \<tau>) \<in> (pp_finite_PP_dependency E)\<^sup>+
      \<and> \<not> pp_finite_same_component E \<sigma> \<tau>}"

lemma pp_finite_component_precedes_trans:
  "trans (pp_finite_component_precedes E)"
proof (rule transI)
  fix \<sigma> \<tau> \<upsilon>
  let ?R = "pp_finite_PP_dependency E"
  assume st: "(\<sigma>, \<tau>) \<in> pp_finite_component_precedes E"
    and tu: "(\<tau>, \<upsilon>) \<in> pp_finite_component_precedes E"
  have st_path: "(\<sigma>, \<tau>) \<in> ?R\<^sup>+"
    using st
    unfolding pp_finite_component_precedes_def
      pp_finite_same_component_def
    by (auto dest: trancl_into_rtrancl)
  have tu_path: "(\<tau>, \<upsilon>) \<in> ?R\<^sup>+"
    and not_ut: "(\<upsilon>, \<tau>) \<notin> ?R\<^sup>*"
    using tu
    unfolding pp_finite_component_precedes_def
      pp_finite_same_component_def
    by (auto dest: trancl_into_rtrancl)
  have su_path: "(\<sigma>, \<upsilon>) \<in> ?R\<^sup>+"
    using trancl_trans[OF st_path tu_path] .
  have not_us: "(\<upsilon>, \<sigma>) \<notin> ?R\<^sup>*"
  proof
    assume us: "(\<upsilon>, \<sigma>) \<in> ?R\<^sup>*"
    have ut: "(\<upsilon>, \<tau>) \<in> ?R\<^sup>+"
      using rtrancl_trancl_trancl[OF us st_path] .
    show False
      using not_ut trancl_into_rtrancl[OF ut] by blast
  qed
  show "(\<sigma>, \<upsilon>) \<in> pp_finite_component_precedes E"
    using su_path not_us
    unfolding pp_finite_component_precedes_def
      pp_finite_same_component_def
    by (auto dest: trancl_into_rtrancl)
qed

lemma pp_finite_component_precedes_irrefl:
  "(\<sigma>, \<sigma>) \<notin> pp_finite_component_precedes E"
  unfolding pp_finite_component_precedes_def
    pp_finite_same_component_def
  by simp

theorem pp_finite_component_condensation_acyclic:
  "acyclic (pp_finite_component_precedes E)"
proof -
  have trans: "trans (pp_finite_component_precedes E)"
    by (rule pp_finite_component_precedes_trans)
  have closure:
      "(pp_finite_component_precedes E)\<^sup>+ =
        pp_finite_component_precedes E"
    using trancl_id[OF trans] .
  show ?thesis
    unfolding acyclic_def closure
    using pp_finite_component_precedes_irrefl by blast
qed

theorem pp_finite_dependency_edge_decomposition:
  assumes edge: "(\<sigma>, \<tau>) \<in> pp_finite_PP_dependency E"
  shows "pp_finite_same_component E \<sigma> \<tau>
    \<or> (\<sigma>, \<tau>) \<in> pp_finite_component_precedes E"
proof (cases "pp_finite_same_component E \<sigma> \<tau>")
  case True
  then show ?thesis by blast
next
  case False
  have "(\<sigma>, \<tau>)
      \<in> (pp_finite_PP_dependency E)\<^sup>+"
    using edge by (rule r_into_trancl)
  then show ?thesis
    using False
    unfolding pp_finite_component_precedes_def by blast
qed

subsection \<open>The first classifier-bearing cycle\<close>

definition pp_finite_singleton_probe_builder :: oterm where
  "pp_finite_singleton_probe_builder =
    Lam pp_finite_classifier_type
      (Lam Prop
        (App (Var 1)
          (Lam Prop
            (\<box>\<^sub>o ((Var 0) \<longleftrightarrow>\<^sub>o (Var 1))))))"

lemma pp_finite_singleton_probe_builder_typed:
  "[] \<turnstile> pp_finite_singleton_probe_builder :
    pp_finite_classifier_type
      \<rightarrow>\<^sub>o pp_finite_unary_type"
  unfolding pp_finite_singleton_probe_builder_def
  apply (rule has_type.Lam)
  apply (rule has_type.Lam)
  apply (rule has_type.App)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Lam)
  apply (rule typed_ObjBox)
  apply (rule has_type.Conj)
   apply (rule has_type.Imp)
    apply (rule has_type.Var)
    apply simp
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Imp)
   apply (rule has_type.Var)
   apply simp
  apply (rule has_type.Var)
  apply simp
  done

lemma pp_finite_singleton_probe_builder_logical:
  "pp_logical_vocabulary pp_finite_singleton_probe_builder"
  unfolding pp_finite_singleton_probe_builder_def
    pp_logical_vocabulary_def
  by simp

definition pp_finite_first_classifier_cycle ::
    "(otype \<times> otype) set" where
  "pp_finite_first_classifier_cycle =
    {(pp_finite_classifier_type, pp_finite_unary_type)}"

lemma pp_finite_no_application_pairs_acyclic:
  "pp_finite_classifier_acyclic {}"
  unfolding pp_finite_classifier_acyclic_def
    pp_finite_application_dependency_def
  by simp

lemma pp_finite_first_classifier_cycle_not_acyclic:
  "\<not> pp_finite_classifier_acyclic
    pp_finite_first_classifier_cycle"
proof -
  have edge:
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> pp_finite_application_dependency
          pp_finite_first_classifier_cycle"
    unfolding pp_finite_first_classifier_cycle_def
    by (rule pp_finite_application_dependency_argument) simp
  then have
      "(pp_finite_classifier_type, pp_finite_unary_type)
        \<in> (pp_finite_application_dependency
          pp_finite_first_classifier_cycle)\<^sup>*"
    by (rule r_into_rtrancl)
  then show ?thesis
    unfolding pp_finite_classifier_acyclic_def by blast
qed

theorem pp_finite_first_classifier_cycle_minimal:
  "\<not> pp_finite_classifier_acyclic
      pp_finite_first_classifier_cycle
    \<and>
    (\<forall>E. E \<subset> pp_finite_first_classifier_cycle
      \<longrightarrow> pp_finite_classifier_acyclic E)"
proof
  show "\<not> pp_finite_classifier_acyclic
      pp_finite_first_classifier_cycle"
    by (rule pp_finite_first_classifier_cycle_not_acyclic)
  show "\<forall>E. E \<subset> pp_finite_first_classifier_cycle
      \<longrightarrow> pp_finite_classifier_acyclic E"
  proof (intro allI impI)
    fix E
    assume "E \<subset> pp_finite_first_classifier_cycle"
    then have "E = {}"
      unfolding pp_finite_first_classifier_cycle_def by blast
    then show "pp_finite_classifier_acyclic E"
      using pp_finite_no_application_pairs_acyclic by simp
  qed
qed

lemma pp_finite_first_PP_dependency:
  "pp_finite_PP_dependency pp_finite_first_classifier_cycle =
    {
      (pp_finite_unary_type, pp_finite_classifier_type),
      (pp_finite_classifier_type, pp_finite_unary_type),
      (pp_finite_classifier_type \<rightarrow>\<^sub>o
        pp_finite_unary_type, pp_finite_unary_type)
    }"
  unfolding pp_finite_PP_dependency_def
    pp_finite_application_dependency_def
    pp_finite_first_classifier_cycle_def
  by auto

lemma pp_finite_first_reachable_from_unary:
  assumes
    "(pp_finite_unary_type, \<sigma>) \<in>
      (pp_finite_PP_dependency
        pp_finite_first_classifier_cycle)\<^sup>*"
  shows "\<sigma> = pp_finite_unary_type
    \<or> \<sigma> = pp_finite_classifier_type"
  using assms
  unfolding pp_finite_first_PP_dependency
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case by auto
qed

theorem pp_finite_first_classifier_component:
  "pp_finite_component pp_finite_first_classifier_cycle
      pp_finite_unary_type
    = {pp_finite_unary_type, pp_finite_classifier_type}"
proof
  show "pp_finite_component pp_finite_first_classifier_cycle
      pp_finite_unary_type
    \<subseteq> {pp_finite_unary_type, pp_finite_classifier_type}"
  proof
    fix \<sigma>
    assume member:
        "\<sigma> \<in> pp_finite_component
          pp_finite_first_classifier_cycle
          pp_finite_unary_type"
    have path:
        "(pp_finite_unary_type, \<sigma>) \<in>
          (pp_finite_PP_dependency
            pp_finite_first_classifier_cycle)\<^sup>*"
      using member
      unfolding pp_finite_component_def
        pp_finite_same_component_def by blast
    show "\<sigma> \<in>
        {pp_finite_unary_type, pp_finite_classifier_type}"
      using pp_finite_first_reachable_from_unary[OF path]
      by blast
  qed
  show "{pp_finite_unary_type, pp_finite_classifier_type}
      \<subseteq>
      pp_finite_component pp_finite_first_classifier_cycle
        pp_finite_unary_type"
  proof
    fix \<sigma>
    assume "\<sigma> \<in>
        {pp_finite_unary_type, pp_finite_classifier_type}"
    then consider
        (unary) "\<sigma> = pp_finite_unary_type"
      | (classifier) "\<sigma> = pp_finite_classifier_type"
      by blast
    then show "\<sigma> \<in>
        pp_finite_component pp_finite_first_classifier_cycle
          pp_finite_unary_type"
    proof cases
      case unary
      then show ?thesis
        using pp_finite_component_self by simp
    next
      case classifier
      have forward:
          "(pp_finite_unary_type, pp_finite_classifier_type)
            \<in> pp_finite_PP_dependency
              pp_finite_first_classifier_cycle"
        unfolding pp_finite_first_PP_dependency by simp
      have backward:
          "(pp_finite_classifier_type, pp_finite_unary_type)
            \<in> pp_finite_PP_dependency
              pp_finite_first_classifier_cycle"
        unfolding pp_finite_first_PP_dependency by simp
      show ?thesis
        unfolding classifier pp_finite_component_def
          pp_finite_same_component_def
        using forward backward
        by (auto intro: r_into_rtrancl)
    qed
  qed
qed

theorem pp_finite_first_builder_component_precedes:
  "(pp_finite_classifier_type \<rightarrow>\<^sub>o pp_finite_unary_type,
      pp_finite_unary_type)
    \<in> pp_finite_component_precedes
      pp_finite_first_classifier_cycle"
proof -
  let ?F =
    "pp_finite_classifier_type \<rightarrow>\<^sub>o
      pp_finite_unary_type"
  have edge:
      "(?F, pp_finite_unary_type)
        \<in> pp_finite_PP_dependency
          pp_finite_first_classifier_cycle"
    unfolding pp_finite_first_PP_dependency by simp
  have no_return:
      "(pp_finite_unary_type, ?F)
        \<notin> (pp_finite_PP_dependency
          pp_finite_first_classifier_cycle)\<^sup>*"
    using pp_finite_first_reachable_from_unary by auto
  show ?thesis
    using edge no_return
    unfolding pp_finite_component_precedes_def
      pp_finite_same_component_def
    by (auto intro: r_into_trancl r_into_rtrancl)
qed

subsection \<open>The next classifier-bearing component\<close>

abbreviation pp_finite_unary_transformer_type :: otype where
  "pp_finite_unary_transformer_type \<equiv>
    pp_finite_unary_type \<rightarrow>\<^sub>o pp_finite_unary_type"

abbreviation pp_finite_binary_unary_builder_type :: otype where
  "pp_finite_binary_unary_builder_type \<equiv>
    pp_finite_unary_type
      \<rightarrow>\<^sub>o pp_finite_unary_transformer_type"

definition pp_finite_negation_closure_pairs ::
    "(otype \<times> otype) set"
where
  "pp_finite_negation_closure_pairs =
    pp_finite_first_classifier_cycle
    \<union> {(pp_finite_unary_type, pp_finite_unary_type)}"

definition pp_finite_boolean_closure_pairs ::
    "(otype \<times> otype) set"
where
  "pp_finite_boolean_closure_pairs =
    pp_finite_negation_closure_pairs
    \<union> {
      (pp_finite_unary_type,
        pp_finite_unary_transformer_type)}"

lemma pp_finite_negation_PP_dependency:
  "pp_finite_PP_dependency pp_finite_negation_closure_pairs =
    {
      (pp_finite_unary_type, pp_finite_classifier_type),
      (pp_finite_classifier_type, pp_finite_unary_type),
      (pp_finite_classifier_type \<rightarrow>\<^sub>o
        pp_finite_unary_type, pp_finite_unary_type),
      (pp_finite_unary_type, pp_finite_unary_type),
      (pp_finite_unary_transformer_type,
        pp_finite_unary_type)
    }"
  unfolding pp_finite_PP_dependency_def
    pp_finite_application_dependency_def
    pp_finite_negation_closure_pairs_def
    pp_finite_first_classifier_cycle_def
  by auto

lemma pp_finite_negation_reachable_from_unary:
  assumes
    "(pp_finite_unary_type, \<sigma>) \<in>
      (pp_finite_PP_dependency
        pp_finite_negation_closure_pairs)\<^sup>*"
  shows "\<sigma> = pp_finite_unary_type
    \<or> \<sigma> = pp_finite_classifier_type"
  using assms
  unfolding pp_finite_negation_PP_dependency
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case by auto
qed

theorem pp_finite_negation_classifier_component:
  "pp_finite_component pp_finite_negation_closure_pairs
      pp_finite_unary_type
    = {pp_finite_unary_type, pp_finite_classifier_type}"
proof
  show "pp_finite_component pp_finite_negation_closure_pairs
      pp_finite_unary_type
    \<subseteq> {pp_finite_unary_type, pp_finite_classifier_type}"
    using pp_finite_negation_reachable_from_unary
    unfolding pp_finite_component_def
      pp_finite_same_component_def
    by blast
  show "{pp_finite_unary_type, pp_finite_classifier_type}
      \<subseteq>
      pp_finite_component pp_finite_negation_closure_pairs
        pp_finite_unary_type"
  proof
    fix \<sigma>
    assume member:
        "\<sigma> \<in>
          {pp_finite_unary_type, pp_finite_classifier_type}"
    have UC:
        "(pp_finite_unary_type, pp_finite_classifier_type)
          \<in> pp_finite_PP_dependency
            pp_finite_negation_closure_pairs"
      unfolding pp_finite_negation_PP_dependency by simp
    have CU:
        "(pp_finite_classifier_type, pp_finite_unary_type)
          \<in> pp_finite_PP_dependency
            pp_finite_negation_closure_pairs"
      unfolding pp_finite_negation_PP_dependency by simp
    from member consider
        (unary) "\<sigma> = pp_finite_unary_type"
      | (classifier) "\<sigma> = pp_finite_classifier_type"
      by blast
    then show "\<sigma> \<in>
        pp_finite_component pp_finite_negation_closure_pairs
          pp_finite_unary_type"
    proof cases
      case unary
      then show ?thesis
        using pp_finite_component_self by simp
    next
      case classifier
      show ?thesis
        unfolding classifier pp_finite_component_def
          pp_finite_same_component_def
        using UC CU
        by (auto intro: r_into_rtrancl)
    qed
  qed
qed

lemma pp_finite_boolean_PP_dependency:
  "pp_finite_PP_dependency pp_finite_boolean_closure_pairs =
    {
      (pp_finite_unary_type, pp_finite_classifier_type),
      (pp_finite_classifier_type, pp_finite_unary_type),
      (pp_finite_classifier_type \<rightarrow>\<^sub>o
        pp_finite_unary_type, pp_finite_unary_type),
      (pp_finite_unary_type, pp_finite_unary_type),
      (pp_finite_unary_transformer_type,
        pp_finite_unary_type),
      (pp_finite_unary_type,
        pp_finite_unary_transformer_type),
      (pp_finite_binary_unary_builder_type,
        pp_finite_unary_transformer_type)
    }"
  unfolding pp_finite_PP_dependency_def
    pp_finite_application_dependency_def
    pp_finite_boolean_closure_pairs_def
    pp_finite_negation_closure_pairs_def
    pp_finite_first_classifier_cycle_def
  by auto

lemma pp_finite_boolean_reachable_from_unary:
  assumes
    "(pp_finite_unary_type, \<sigma>) \<in>
      (pp_finite_PP_dependency
        pp_finite_boolean_closure_pairs)\<^sup>*"
  shows "\<sigma> = pp_finite_unary_type
    \<or> \<sigma> = pp_finite_classifier_type
    \<or> \<sigma> = pp_finite_unary_transformer_type"
  using assms
  unfolding pp_finite_boolean_PP_dependency
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case by auto
qed

theorem pp_finite_boolean_classifier_component:
  "pp_finite_component pp_finite_boolean_closure_pairs
      pp_finite_unary_type
    =
    {pp_finite_unary_type, pp_finite_classifier_type,
      pp_finite_unary_transformer_type}"
proof
  show "pp_finite_component pp_finite_boolean_closure_pairs
      pp_finite_unary_type
    \<subseteq>
    {pp_finite_unary_type, pp_finite_classifier_type,
      pp_finite_unary_transformer_type}"
    using pp_finite_boolean_reachable_from_unary
    unfolding pp_finite_component_def
      pp_finite_same_component_def
    by blast
  show "{pp_finite_unary_type, pp_finite_classifier_type,
      pp_finite_unary_transformer_type}
    \<subseteq>
    pp_finite_component pp_finite_boolean_closure_pairs
      pp_finite_unary_type"
  proof
    fix \<sigma>
    assume member:
        "\<sigma> \<in>
          {pp_finite_unary_type, pp_finite_classifier_type,
            pp_finite_unary_transformer_type}"
    have UC:
        "(pp_finite_unary_type, pp_finite_classifier_type)
          \<in> pp_finite_PP_dependency
            pp_finite_boolean_closure_pairs"
      unfolding pp_finite_boolean_PP_dependency by simp
    have CU:
        "(pp_finite_classifier_type, pp_finite_unary_type)
          \<in> pp_finite_PP_dependency
            pp_finite_boolean_closure_pairs"
      unfolding pp_finite_boolean_PP_dependency by simp
    have UN:
        "(pp_finite_unary_type,
          pp_finite_unary_transformer_type)
          \<in> pp_finite_PP_dependency
            pp_finite_boolean_closure_pairs"
      unfolding pp_finite_boolean_PP_dependency by simp
    have NU:
        "(pp_finite_unary_transformer_type,
          pp_finite_unary_type)
          \<in> pp_finite_PP_dependency
            pp_finite_boolean_closure_pairs"
      unfolding pp_finite_boolean_PP_dependency by simp
    from member consider
        (unary) "\<sigma> = pp_finite_unary_type"
      | (classifier) "\<sigma> = pp_finite_classifier_type"
      | (transformer)
          "\<sigma> = pp_finite_unary_transformer_type"
      by blast
    then show "\<sigma> \<in>
        pp_finite_component pp_finite_boolean_closure_pairs
          pp_finite_unary_type"
    proof cases
      case unary
      then show ?thesis
        using pp_finite_component_self by simp
    next
      case classifier
      show ?thesis
        unfolding classifier pp_finite_component_def
          pp_finite_same_component_def
        using UC CU
        by (auto intro: r_into_rtrancl)
    next
      case transformer
      show ?thesis
        unfolding transformer pp_finite_component_def
          pp_finite_same_component_def
        using UN NU
        by (auto intro: r_into_rtrancl)
    qed
  qed
qed

text \<open>
  The component calculation shows exactly where the first semantic
  obligation lies.  PP and application closure form the strongly connected
  component consisting of the unary type and its classifier type.  A pure
  builder of type
  \<open>pp_finite_classifier_type \<rightarrow>\<^sub>o pp_finite_unary_type\<close>
  lies in a preceding component and injects a value into this cycle.  The
  singleton-family builder is the first such generator.  Its classifier
  application reduces to the closed logical non-contingency operator.
\<close>

end
