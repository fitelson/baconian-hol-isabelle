theory Bacon_PP_ZF_Tree_Indexed_Family_Stock_Probe
  imports
    Higher_Order_Metaphysics_PP_ZF_Singleton_Symmetrized_Pair.Bacon_PP_ZF_Tree_Singleton_Symmetrized_Pair
    Higher_Order_Metaphysics_PP_ZF_Secondary.Bacon_PP_ZF_Tree_Indexed_Family_Probe
begin

section \<open>Stock-parametric probes for indexed families\<close>

definition pp_t_indexed_family_probe_for_stock ::
    "otype \<Rightarrow> (bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> oterm \<Rightarrow> ZF"
where
  "pp_t_indexed_family_probe_for_stock \<alpha> S B =
    pp_t_closed_den (pp_t_indexed_family_probe_builder \<alpha> B)
      \<acute> pp_t_classifier pp_t_one_context_unary_type S"

lemma pp_t_indexed_family_probe_for_stock_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows "Elem (pp_t_indexed_family_probe_for_stock \<alpha> S B)
    (pp_t_domain
      (\<alpha> \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
  unfolding pp_t_indexed_family_probe_for_stock_def
  using pp_t_app_closed[
    OF pp_t_closed_den_in_domain[
      OF pp_t_indexed_family_probe_builder_typed[OF B_typed]]
      pp_t_classifier_in_domain[OF S_admissible]] .

lemma pp_t_indexed_family_probe_for_stock_apply:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "(pp_t_indexed_family_probe_for_stock \<alpha> S B
      \<acute> a) \<acute> p
    =
    pp_t_classifier pp_t_one_context_unary_type S
      \<acute> ((pp_t_closed_den B \<acute> a) \<acute> p)"
  unfolding pp_t_indexed_family_probe_for_stock_def
    pp_t_indexed_family_probe_builder_def pp_t_closed_den_def
  using a p pp_t_classifier_in_domain[OF S_admissible]
    pp_t_closed_den_in_domain[OF B_typed]
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_indexed_family_value_in_domain_for_stock:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "Elem ((pp_t_closed_den B \<acute> a) \<acute> p)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_app_closed[
      OF pp_t_closed_den_in_domain[OF B_typed] a] p] .

theorem pp_t_indexed_family_probe_for_stock_apply_holds:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and a: "Elem a (pp_t_domain \<alpha>)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_indexed_family_probe_for_stock \<alpha> S B
        \<acute> a) \<acute> p) w
    \<longleftrightarrow>
    S w ((pp_t_closed_den B \<acute> a) \<acute> p)"
  unfolding pp_t_indexed_family_probe_for_stock_apply[
    OF B_typed S_admissible a p]
  using pp_t_classifier_holds[
    OF pp_t_indexed_family_value_in_domain_for_stock[
      OF B_typed a p],
    of S w]
  by simp

definition pp_t_indexed_family_section_stock_enlargement ::
    "otype \<Rightarrow> (bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> oterm \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_indexed_family_section_stock_enlargement \<alpha> S B w X
    \<longleftrightarrow>
    S w X
    \<or> (\<exists>a.
      Elem a (pp_t_domain \<alpha>)
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X)"

lemma pp_t_indexed_family_probe_section_in_domain:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and a: "Elem a (pp_t_domain \<alpha>)"
  shows "Elem
    (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_app_closed[
    OF pp_t_indexed_family_probe_for_stock_in_domain[
      OF B_typed S_admissible] a] .

lemma pp_t_indexed_family_section_stock_enlargement_admissible:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows "pp_t_predicate_admissible
    pp_t_one_context_unary_type
    (pp_t_indexed_family_section_stock_enlargement \<alpha> S B)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X
      (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y
      (pp_t_domain pp_t_one_context_unary_type)"
    and XY:
      "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have XY_v:
      "pp_t_eqv pp_t_one_context_unary_type v X Y"
    using pp_t_eqv_persistent[OF XY wv] .
  have YX_v:
      "pp_t_eqv pp_t_one_context_unary_type v Y X"
    using pp_t_eqv_symmetric[OF X Y XY_v] .
  have S_equiv: "S v X \<longleftrightarrow> S v Y"
    using S_admissible X Y XY wv
    unfolding pp_t_predicate_admissible_def
    by blast
  have added_equiv:
      "(\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            X)
      \<longleftrightarrow>
       (\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            Y)"
  proof
    assume left:
        "\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            X"
    then obtain a where a: "Elem a (pp_t_domain \<alpha>)"
      and probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_indexed_family_probe_section_in_domain[
        OF B_typed S_admissible a] .
    have probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) Y"
      using pp_t_eqv_transitive[
        OF probe X Y probe_X XY_v] .
    show "\<exists>a.
        Elem a (pp_t_domain \<alpha>)
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) Y"
      using a probe_Y by blast
  next
    assume right:
        "\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            Y"
    then obtain a where a: "Elem a (pp_t_domain \<alpha>)"
      and probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) Y"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_indexed_family_probe_section_in_domain[
        OF B_typed S_admissible a] .
    have probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X"
      using pp_t_eqv_transitive[
        OF probe Y X probe_Y YX_v] .
    show "\<exists>a.
        Elem a (pp_t_domain \<alpha>)
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X"
      using a probe_X by blast
  qed
  show "pp_t_indexed_family_section_stock_enlargement \<alpha> S B v X
      \<longleftrightarrow>
    pp_t_indexed_family_section_stock_enlargement \<alpha> S B v Y"
    unfolding pp_t_indexed_family_section_stock_enlargement_def
    using S_equiv added_equiv by blast
qed

end
