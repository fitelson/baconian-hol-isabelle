theory Bacon_PP_ZF_Tree_Indexed_Family_Probe
  imports Bacon_PP_ZF_Tree_Family_View_Definability
begin

section \<open>Uniform family tests under higher-order quantifiers\<close>

text \<open>
  A quantified one-classifier context requires one definition which is
  uniform in the quantified object.  We therefore let \<open>B\<close> be a closed
  logical family indexed by an arbitrary object-language type \<open>\<alpha>\<close>.
  The indexed probe maps \<open>a\<close> and \<open>p\<close> to
  \<open>Pure (B a p)\<close>.
\<close>

definition pp_t_indexed_family_probe_builder ::
    "otype \<Rightarrow> oterm \<Rightarrow> oterm"
where
  "pp_t_indexed_family_probe_builder \<alpha> B =
    Lam pp_t_one_context_classifier_type
      (Lam \<alpha>
        (Lam Prop
          (App (Var 2)
            (App
              (App (shift (shift (shift B))) (Var 1))
              (Var 0)))))"

lemma pp_t_indexed_family_probe_builder_typed:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  shows "[] \<turnstile> pp_t_indexed_family_probe_builder \<alpha> B :
    pp_t_one_context_classifier_type
      \<rightarrow>\<^sub>o \<alpha>
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
proof -
  have B_shift_1:
      "[pp_t_one_context_classifier_type]
        \<turnstile> shift B :
          \<alpha> \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_typed by (rule weakening_front)
  have B_shift_2:
      "[\<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> shift (shift B) :
          \<alpha> \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_shift_1 by (rule weakening_front)
  have B_shift_3:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> shift (shift (shift B)) :
          \<alpha> \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_shift_2 by (rule weakening_front)
  have classifier_var:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> Var 2 : pp_t_one_context_classifier_type"
    by (rule has_type.Var) (simp add: lookup_def)
  have index_var:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> Var 1 : \<alpha>"
    by (rule has_type.Var) (simp add: lookup_def)
  have prop_var:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> Var 0 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have B_at_index:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile> App (shift (shift (shift B))) (Var 1) :
          Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    using B_shift_3 index_var by (rule has_type.App)
  have B_at_index_prop:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile>
          App
            (App (shift (shift (shift B))) (Var 1))
            (Var 0) :
          pp_t_one_context_unary_type"
    using B_at_index prop_var by (rule has_type.App)
  have test:
      "[Prop, \<alpha>, pp_t_one_context_classifier_type]
        \<turnstile>
          App (Var 2)
            (App
              (App (shift (shift (shift B))) (Var 1))
              (Var 0)) :
          Prop"
    using classifier_var B_at_index_prop by (rule has_type.App)
  show ?thesis
    unfolding pp_t_indexed_family_probe_builder_def
    using test by (intro has_type.Lam)
qed

lemma pp_t_indexed_family_probe_builder_logical:
  assumes B_logical: "pp_logical_vocabulary B"
  shows "pp_logical_vocabulary
    (pp_t_indexed_family_probe_builder \<alpha> B)"
  using B_logical
  by (simp add: pp_t_indexed_family_probe_builder_def
      pp_logical_vocabulary_def shift_def)

definition pp_t_indexed_family_probe ::
    "otype \<Rightarrow> oterm \<Rightarrow> ZF"
where
  "pp_t_indexed_family_probe \<alpha> B =
    pp_t_closed_den (pp_t_indexed_family_probe_builder \<alpha> B)
      \<acute> pp_t_old_unary_stock_classifier"

lemma pp_t_indexed_family_probe_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  shows "Elem (pp_t_indexed_family_probe \<alpha> B)
    (pp_t_domain
      (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_indexed_family_probe_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_indexed_family_probe_builder_typed[OF B_typed]]
      pp_t_old_unary_stock_classifier_in_domain] .

lemma pp_t_indexed_family_value_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "Elem
    ((pp_t_closed_den B \<acute> a) \<acute> p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_app_closed[
      OF pp_t_closed_den_in_domain[OF B_typed] a] p] .

lemma pp_t_indexed_family_probe_apply:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "(pp_t_indexed_family_probe \<alpha> B \<acute> a) \<acute> p =
    pp_t_old_unary_stock_classifier
      \<acute> ((pp_t_closed_den B \<acute> a) \<acute> p)"
  unfolding pp_t_indexed_family_probe_def
    pp_t_indexed_family_probe_builder_def pp_t_closed_den_def
  using a p pp_t_old_unary_stock_classifier_in_domain
    pp_t_closed_den_in_domain[OF B_typed]
  by (simp add: Lambda_app pp_t_eval_shift)

theorem pp_t_indexed_family_probe_apply_holds:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_indexed_family_probe \<alpha> B \<acute> a) \<acute> p) w
    \<longleftrightarrow>
    pp_t_closed_logical_stock pp_t_one_context_unary_type w
      ((pp_t_closed_den B \<acute> a) \<acute> p)"
  unfolding pp_t_indexed_family_probe_apply[OF B_typed a p]
    pp_t_old_unary_stock_classifier_def
  using pp_t_classifier_holds[
    OF pp_t_indexed_family_value_in_domain[
      OF B_typed a p],
    of "pp_t_closed_logical_stock
      pp_t_one_context_unary_type" w]
  by simp

lemma pp_t_indexed_unary_function_ext:
  assumes F:
      "Elem F
        (pp_t_domain
          (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    and G:
      "Elem G
        (pp_t_domain
          (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    and applications:
      "\<And>a. Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        F \<acute> a = G \<acute> a"
  shows "F = G"
proof -
  have F_fun:
      "Elem F
        (Fun (pp_t_domain \<alpha>)
          (pp_t_domain pp_t_one_context_unary_type))"
    using pp_t_arrow_member_function[OF F] .
  have G_fun:
      "Elem G
        (Fun (pp_t_domain \<alpha>)
          (pp_t_domain pp_t_one_context_unary_type))"
    using pp_t_arrow_member_function[OF G] .
  obtain A where F_rep:
      "F = Lambda (pp_t_domain \<alpha>) A"
    using Elem_Fun_Lambda[OF F_fun] by blast
  obtain C where G_rep:
      "G = Lambda (pp_t_domain \<alpha>) C"
    using Elem_Fun_Lambda[OF G_fun] by blast
  have pointwise:
      "\<And>a. Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        A a = C a"
  proof -
    fix a
    assume a: "Elem a (pp_t_domain \<alpha>)"
    have app: "F \<acute> a = G \<acute> a"
      using applications[OF a] .
    show "A a = C a"
      using app
      apply (subst (asm) F_rep)
      apply (subst (asm) G_rep)
      using a by (simp add: Lambda_app)
  qed
  show ?thesis
    apply (subst F_rep)
    apply (subst G_rep)
    using pointwise by (simp add: Lambda_ext)
qed

theorem pp_t_indexed_family_probe_elimination_criterion:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_typed:
      "[] \<turnstile> S :
        \<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and criterion:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            ((pp_t_closed_den B \<acute> a) \<acute> p)
          \<longleftrightarrow>
         pp_t_holds
           ((pp_t_closed_den S \<acute> a) \<acute> p) w)"
  shows "pp_t_indexed_family_probe \<alpha> B =
    pp_t_closed_den S"
proof (rule pp_t_indexed_unary_function_ext)
  show "Elem (pp_t_indexed_family_probe \<alpha> B)
      (pp_t_domain
        (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_indexed_family_probe_in_domain[OF B_typed] .
  show "Elem (pp_t_closed_den S)
      (pp_t_domain
        (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
    using pp_t_closed_den_in_domain[OF S_typed] .
  fix a
  assume a: "Elem a (pp_t_domain \<alpha>)"
  show "pp_t_indexed_family_probe \<alpha> B \<acute> a =
      pp_t_closed_den S \<acute> a"
  proof (rule pp_t_unary_function_ext)
    show "Elem (pp_t_indexed_family_probe \<alpha> B \<acute> a)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_app_closed[
        OF pp_t_indexed_family_probe_in_domain[OF B_typed] a] .
    show "Elem (pp_t_closed_den S \<acute> a)
        (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_app_closed[
        OF pp_t_closed_den_in_domain[OF S_typed] a] .
    fix p
    assume p: "Elem p (pp_t_domain Prop)"
    show "(pp_t_indexed_family_probe \<alpha> B \<acute> a) \<acute> p =
        (pp_t_closed_den S \<acute> a) \<acute> p"
    proof (rule pp_t_prop_ext)
      show "Elem
          ((pp_t_indexed_family_probe \<alpha> B \<acute> a) \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_indexed_family_probe_in_domain[OF B_typed] a] p] .
      show "Elem ((pp_t_closed_den S \<acute> a) \<acute> p)
          (pp_t_domain Prop)"
        using pp_t_app_closed[
          OF pp_t_app_closed[
            OF pp_t_closed_den_in_domain[OF S_typed] a] p] .
      fix w
      show "pp_t_holds
            ((pp_t_indexed_family_probe \<alpha> B \<acute> a) \<acute> p) w
          \<longleftrightarrow>
          pp_t_holds ((pp_t_closed_den S \<acute> a) \<acute> p) w"
        using pp_t_indexed_family_probe_apply_holds[
          OF B_typed a p, of w]
          criterion[OF a p, of w]
        by blast
    qed
  qed
qed

definition pp_t_indexed_condition_uniformly_definable ::
    "otype \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool)
      \<Rightarrow> bool"
where
  "pp_t_indexed_condition_uniformly_definable \<alpha> Q \<longleftrightarrow>
    (\<exists>S.
      [] \<turnstile> S :
        \<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> (\<forall>a p w.
        Elem a (pp_t_domain \<alpha>)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (pp_t_holds
            ((pp_t_closed_den S \<acute> a) \<acute> p) w
          \<longleftrightarrow>
         Q a p w)))"

definition pp_t_indexed_condition_characterizes_stock ::
    "otype \<Rightarrow> oterm
      \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> bool)
      \<Rightarrow> bool"
where
  "pp_t_indexed_condition_characterizes_stock \<alpha> B Q \<longleftrightarrow>
    (\<forall>a p w.
      Elem a (pp_t_domain \<alpha>)
      \<longrightarrow>
      Elem p (pp_t_domain Prop)
      \<longrightarrow>
      (pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          ((pp_t_closed_den B \<acute> a) \<acute> p)
        \<longleftrightarrow>
       Q a p w))"

definition
  pp_t_indexed_family_probe_has_closed_logical_definition ::
    "otype \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_t_indexed_family_probe_has_closed_logical_definition \<alpha> B
    \<longleftrightarrow>
    (\<exists>S.
      [] \<turnstile> S :
        \<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type
      \<and> pp_logical_vocabulary S
      \<and> pp_t_indexed_family_probe \<alpha> B =
        pp_t_closed_den S)"

theorem pp_t_uniform_condition_eliminates_indexed_probe:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and characterizes:
      "pp_t_indexed_condition_characterizes_stock \<alpha> B Q"
    and definable:
      "pp_t_indexed_condition_uniformly_definable \<alpha> Q"
  shows
    "pp_t_indexed_family_probe_has_closed_logical_definition \<alpha> B"
proof -
  obtain S where
      S_typed:
        "[] \<turnstile> S :
          \<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and S_defines:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_holds
            ((pp_t_closed_den S \<acute> a) \<acute> p) w
          \<longleftrightarrow>
         Q a p w)"
    using definable
    unfolding pp_t_indexed_condition_uniformly_definable_def
    by blast
  have criterion:
      "\<And>a p w.
        Elem a (pp_t_domain \<alpha>) \<Longrightarrow>
        Elem p (pp_t_domain Prop) \<Longrightarrow>
        (pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            ((pp_t_closed_den B \<acute> a) \<acute> p)
          \<longleftrightarrow>
         pp_t_holds
           ((pp_t_closed_den S \<acute> a) \<acute> p) w)"
    using characterizes S_defines
    unfolding pp_t_indexed_condition_characterizes_stock_def
    by blast
  have probe_S:
      "pp_t_indexed_family_probe \<alpha> B =
        pp_t_closed_den S"
    using pp_t_indexed_family_probe_elimination_criterion[
      OF B_typed S_typed criterion] .
  show ?thesis
    unfolding
      pp_t_indexed_family_probe_has_closed_logical_definition_def
    using S_typed S_logical probe_S by blast
qed

theorem pp_t_indexed_probe_eliminable_iff_stock_uniformly_definable:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  shows
    "pp_t_indexed_family_probe_has_closed_logical_definition \<alpha> B
      \<longleftrightarrow>
     (\<exists>Q.
       pp_t_indexed_condition_characterizes_stock \<alpha> B Q
       \<and> pp_t_indexed_condition_uniformly_definable \<alpha> Q)"
proof
  assume eliminable:
      "pp_t_indexed_family_probe_has_closed_logical_definition \<alpha> B"
  then obtain S where
      S_typed:
        "[] \<turnstile> S :
          \<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_logical: "pp_logical_vocabulary S"
    and probe_S:
      "pp_t_indexed_family_probe \<alpha> B =
        pp_t_closed_den S"
    unfolding
      pp_t_indexed_family_probe_has_closed_logical_definition_def
    by blast
  let ?Q =
    "\<lambda>a p w.
      pp_t_holds ((pp_t_closed_den S \<acute> a) \<acute> p) w"
  have characterizes:
      "pp_t_indexed_condition_characterizes_stock \<alpha> B ?Q"
    unfolding pp_t_indexed_condition_characterizes_stock_def
  proof (intro allI impI)
    fix a p w
    assume a: "Elem a (pp_t_domain \<alpha>)"
      and p: "Elem p (pp_t_domain Prop)"
    show "pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          ((pp_t_closed_den B \<acute> a) \<acute> p)
        \<longleftrightarrow>
        pp_t_holds ((pp_t_closed_den S \<acute> a) \<acute> p) w"
      using pp_t_indexed_family_probe_apply_holds[
        OF B_typed a p, of w]
      unfolding probe_S by blast
  qed
  have definable:
      "pp_t_indexed_condition_uniformly_definable \<alpha> ?Q"
    unfolding pp_t_indexed_condition_uniformly_definable_def
    using S_typed S_logical by blast
  show "\<exists>Q.
      pp_t_indexed_condition_characterizes_stock \<alpha> B Q
      \<and> pp_t_indexed_condition_uniformly_definable \<alpha> Q"
    using characterizes definable by blast
next
  assume conditions:
      "\<exists>Q.
        pp_t_indexed_condition_characterizes_stock \<alpha> B Q
        \<and> pp_t_indexed_condition_uniformly_definable \<alpha> Q"
  then obtain Q where
      characterizes:
        "pp_t_indexed_condition_characterizes_stock \<alpha> B Q"
    and definable:
        "pp_t_indexed_condition_uniformly_definable \<alpha> Q"
    by blast
  show
      "pp_t_indexed_family_probe_has_closed_logical_definition \<alpha> B"
    using pp_t_uniform_condition_eliminates_indexed_probe[
      OF B_typed characterizes definable] .
qed

text \<open>
  The last biconditional gives the exact uniformity requirement.  It is not
  enough that each fixed value of the quantified variable have some
  definition.  One closed logical term of type
  \<open>\<alpha> \<rightarrow> Prop \<rightarrow> Prop\<close> must define the stock-membership
  condition simultaneously for every value of type \<open>\<alpha>\<close>.  Whenever
  the cone-class condition is sufficient and has such a uniform definition,
  every quantifier over \<open>\<alpha>\<close> can use the resulting classifier-free
  indexed probe.
\<close>

end
