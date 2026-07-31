theory Bacon_PP_ZF_Tree_Multi_Indexed_Family_Stock
  imports
    Higher_Order_Metaphysics_PP_ZF_Indexed_Equivalence_Singleton.Bacon_PP_ZF_Tree_Indexed_Equivalence_Singleton
begin

section \<open>Simultaneous enlargement by heterogeneous indexed families\<close>

text \<open>
  A finite application component may contain several uniformly indexed family
  builders, and their quantified index types need not coincide.  A meta-level
  tag \<open>i\<close> selects both the object-language type \<open>alpha i\<close> and the closed
  builder \<open>B i\<close>.  The following stock adjoins every semantic section of
  every selected indexed probe.
\<close>

definition pp_t_multi_indexed_family_section_stock_enlargement ::
    "(bool list \<Rightarrow> ZF \<Rightarrow> bool)
      \<Rightarrow> ('i \<Rightarrow> otype) \<Rightarrow> ('i \<Rightarrow> oterm)
      \<Rightarrow> 'i set \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_multi_indexed_family_section_stock_enlargement
      S \<alpha> B I w X
    \<longleftrightarrow>
    S w X
    \<or> (\<exists>i \<in> I. \<exists>a.
      Elem a (pp_t_domain (\<alpha> i))
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
          \<acute> a)
        X)"

lemma pp_t_multi_indexed_family_probe_section_in_domain:
  assumes i: "i \<in> I"
    and B_typed:
      "\<And>j. j \<in> I \<Longrightarrow>
        [] \<turnstile> B j :
          \<alpha> j \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and a: "Elem a (pp_t_domain (\<alpha> i))"
  shows "Elem
    (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
      \<acute> a)
    (pp_t_domain pp_t_one_context_unary_type)"
  using pp_t_indexed_family_probe_section_in_domain[
    OF B_typed[OF i] S_admissible a] .

lemma pp_t_multi_indexed_family_section_stock_enlargement_admissible:
  assumes B_typed:
      "\<And>i. i \<in> I \<Longrightarrow>
        [] \<turnstile> B i :
          \<alpha> i \<rightarrow>\<^sub>o Prop
            \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
  shows "pp_t_predicate_admissible
    pp_t_one_context_unary_type
    (pp_t_multi_indexed_family_section_stock_enlargement S \<alpha> B I)"
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
      "(\<exists>i \<in> I. \<exists>a.
          Elem a (pp_t_domain (\<alpha> i))
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
              \<acute> a)
            X)
      \<longleftrightarrow>
       (\<exists>i \<in> I. \<exists>a.
          Elem a (pp_t_domain (\<alpha> i))
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
              \<acute> a)
            Y)"
  proof
    assume left:
        "\<exists>i \<in> I. \<exists>a.
          Elem a (pp_t_domain (\<alpha> i))
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
              \<acute> a)
            X"
    then obtain i a where i: "i \<in> I"
      and a: "Elem a (pp_t_domain (\<alpha> i))"
      and probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          X"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_multi_indexed_family_probe_section_in_domain[
        where i=i and I=I and \<alpha>=\<alpha> and B=B and S=S,
        OF i B_typed S_admissible a] .
    have probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          Y"
      using pp_t_eqv_transitive[
        OF probe X Y probe_X XY_v] .
    show "\<exists>i \<in> I. \<exists>a.
        Elem a (pp_t_domain (\<alpha> i))
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          Y"
      using i a probe_Y by blast
  next
    assume right:
        "\<exists>i \<in> I. \<exists>a.
          Elem a (pp_t_domain (\<alpha> i))
          \<and> pp_t_eqv pp_t_one_context_unary_type v
            (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
              \<acute> a)
            Y"
    then obtain i a where i: "i \<in> I"
      and a: "Elem a (pp_t_domain (\<alpha> i))"
      and probe_Y:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          Y"
      by blast
    have probe:
        "Elem
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          (pp_t_domain pp_t_one_context_unary_type)"
      using pp_t_multi_indexed_family_probe_section_in_domain[
        where i=i and I=I and \<alpha>=\<alpha> and B=B and S=S,
        OF i B_typed S_admissible a] .
    have probe_X:
        "pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          X"
      using pp_t_eqv_transitive[
        OF probe Y X probe_Y YX_v] .
    show "\<exists>i \<in> I. \<exists>a.
        Elem a (pp_t_domain (\<alpha> i))
        \<and> pp_t_eqv pp_t_one_context_unary_type v
          (pp_t_indexed_family_probe_for_stock (\<alpha> i) S (B i)
            \<acute> a)
          X"
      using i a probe_X by blast
  qed
  show "pp_t_multi_indexed_family_section_stock_enlargement
        S \<alpha> B I v X
      \<longleftrightarrow>
      pp_t_multi_indexed_family_section_stock_enlargement
        S \<alpha> B I v Y"
    unfolding
      pp_t_multi_indexed_family_section_stock_enlargement_def
    using S_equiv added_equiv by blast
qed

lemma pp_t_multi_indexed_family_generated_value_membership_iff:
  "pp_t_multi_indexed_family_section_stock_enlargement
      S \<alpha> B I w
      ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
    \<longleftrightarrow>
    S w ((pp_t_closed_den (B i) \<acute> a) \<acute> p)
    \<or> (\<exists>j \<in> I. \<exists>b.
      Elem b (pp_t_domain (\<alpha> j))
      \<and> pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock (\<alpha> j) S (B j)
          \<acute> b)
        ((pp_t_closed_den (B i) \<acute> a) \<acute> p))"
  unfolding
    pp_t_multi_indexed_family_section_stock_enlargement_def
  by simp

end
