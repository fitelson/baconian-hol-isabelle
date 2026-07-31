theory Bacon_PP_ZF_Tree_Guarded_Indexed_Family
  imports
    Higher_Order_Metaphysics_PP_ZF_Iterated_Stabilization.Bacon_PP_ZF_Tree_Iterated_Stabilization
begin

section \<open>Purity-guarded indexed probe sections\<close>

text \<open>
  Application closure does not license application of a pure operator to every
  semantic argument.  The argument must itself be pure.  Accordingly, the
  construction below adjoins only those indexed probe sections whose indices
  satisfy a designated guard.
\<close>

definition pp_t_guarded_indexed_family_section_stock_enlargement ::
    "otype \<Rightarrow> (bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> (bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> oterm \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_guarded_indexed_family_section_stock_enlargement
      \<alpha> Guard S B w X
    \<longleftrightarrow>
    S w X
    \<or> (\<exists>a.
      Elem a (pp_t_domain \<alpha>)
      \<and> Guard w a
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
        X)"

lemma pp_t_guarded_indexed_family_enlargement_subset_unrestricted:
  "pp_t_guarded_indexed_family_section_stock_enlargement
      \<alpha> Guard S B w X
    \<Longrightarrow>
   pp_t_indexed_family_section_stock_enlargement \<alpha> S B w X"
  unfolding
    pp_t_guarded_indexed_family_section_stock_enlargement_def
    pp_t_indexed_family_section_stock_enlargement_def
  by blast

lemma pp_t_guarded_indexed_family_section_stock_enlargement_admissible:
  assumes B_typed:
      "[] \<turnstile> B :
        \<alpha> \<rightarrow>\<^sub>o Prop
          \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type S"
  shows "pp_t_predicate_admissible pp_t_one_context_unary_type
    (pp_t_guarded_indexed_family_section_stock_enlargement
      \<alpha> Guard S B)"
  unfolding pp_t_predicate_admissible_def
proof (intro allI impI)
  fix w X Y v
  assume X: "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_one_context_unary_type)"
    and XY: "pp_t_eqv pp_t_one_context_unary_type w X Y"
    and wv: "prefix w v"
  have XY_v: "pp_t_eqv pp_t_one_context_unary_type v X Y"
    by (rule pp_t_eqv_persistent[OF XY wv])
  have YX_v: "pp_t_eqv pp_t_one_context_unary_type v Y X"
    by (rule pp_t_eqv_symmetric[OF X Y XY_v])
  have S_equiv: "S v X \<longleftrightarrow> S v Y"
    using S_admissible X Y XY wv
    unfolding pp_t_predicate_admissible_def
    by blast
  have added_equiv:
      "(\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> Guard v a
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            X)
      \<longleftrightarrow>
       (\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> Guard v a
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            Y)"
  proof
    assume left:
        "\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> Guard v a
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            X"
    then obtain a where a: "Elem a (pp_t_domain \<alpha>)"
      and guarded: "Guard v a"
      and probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_indexed_family_probe_section_in_domain[
        OF B_typed S_admissible a])
    have probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) Y"
      by (rule pp_t_eqv_transitive[
        OF probe X Y probe_X XY_v])
    show "\<exists>a.
        Elem a (pp_t_domain \<alpha>)
        \<and> Guard v a
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          Y"
      using a guarded probe_Y by blast
  next
    assume right:
        "\<exists>a.
          Elem a (pp_t_domain \<alpha>)
          \<and> Guard v a
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
            Y"
    then obtain a where a: "Elem a (pp_t_domain \<alpha>)"
      and guarded: "Guard v a"
      and probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) Y"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_indexed_family_probe_section_in_domain[
        OF B_typed S_admissible a])
    have probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a) X"
      by (rule pp_t_eqv_transitive[
        OF probe Y X probe_Y YX_v])
    show "\<exists>a.
        Elem a (pp_t_domain \<alpha>)
        \<and> Guard v a
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
          X"
      using a guarded probe_X by blast
  qed
  show "pp_t_guarded_indexed_family_section_stock_enlargement
          \<alpha> Guard S B v X
      \<longleftrightarrow>
      pp_t_guarded_indexed_family_section_stock_enlargement
          \<alpha> Guard S B v Y"
    unfolding
      pp_t_guarded_indexed_family_section_stock_enlargement_def
    using S_equiv added_equiv by blast
qed

lemma pp_t_guarded_indexed_family_new_member_iff_guarded_collision:
  assumes not_old: "\<not> S w X"
  shows
    "pp_t_guarded_indexed_family_section_stock_enlargement
        \<alpha> Guard S B w X
      \<longleftrightarrow>
    (\<exists>a.
      Elem a (pp_t_domain \<alpha>)
      \<and> Guard w a
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock \<alpha> S B \<acute> a)
        X)"
  unfolding pp_t_guarded_indexed_family_section_stock_enlargement_def
  using not_old by blast

section \<open>The exact guarded frontier for the parity singleton\<close>

theorem
  pp_t_guarded_operator_indexed_parity_singleton_enters_iff_pure_collision:
  "pp_t_guarded_indexed_family_section_stock_enlargement
      pp_t_one_context_unary_type Pure
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder
      w
      (pp_t_singleton_family_at pp_t_even_false_parity)
    \<longleftrightarrow>
    (\<exists>F.
      Elem F (pp_t_domain pp_t_one_context_unary_type)
      \<and> Pure w F
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> F)
        (pp_t_singleton_family_at pp_t_even_false_parity))"
  by (rule
    pp_t_guarded_indexed_family_new_member_iff_guarded_collision[
      where \<alpha>=pp_t_one_context_unary_type
        and Guard=Pure
        and S="pp_t_closed_logical_stock
          pp_t_one_context_unary_type"
        and B=pp_t_operator_indexed_singleton_family_builder
        and w=w
        and X="pp_t_singleton_family_at pp_t_even_false_parity",
      OF pp_t_parity_singleton_not_in_closed_stock])

corollary
  pp_t_recombination_rules_out_canonical_parity_collision_index:
  assumes recombines:
    "pp_t_unary_recombines_at Pure pp_t_even_false_parity w"
  shows
    "\<not> Pure w
      (pp_t_singleton_settledness_realizer
        pp_t_even_false_parity)"
  by (rule pp_t_recombination_excludes_singleton_settledness_realizer[
    OF pp_t_even_false_parity_in_domain recombines])

end
