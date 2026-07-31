theory Bacon_PP_ZF_Tree_Indexed_Equivalence_Singleton
  imports
    Higher_Order_Metaphysics_PP_ZF_Indexed_Conjunctive_Singleton.Bacon_PP_ZF_Tree_Indexed_Conjunctive_Singleton
begin

section \<open>An indexed family stabilized by complement symmetry\<close>

definition pp_t_indexed_equivalence_singleton_family_builder :: oterm where
  "pp_t_indexed_equivalence_singleton_family_builder =
    Lam Prop
      (Lam Prop
        (App
          (shift (shift pp_t_singleton_family_builder))
          (Conj
            (Imp (Var 1) (Var 0))
            (Imp (Var 0) (Var 1)))))"

lemma pp_t_indexed_equivalence_singleton_family_builder_typed:
  "[] \<turnstile> pp_t_indexed_equivalence_singleton_family_builder :
    Prop \<rightarrow>\<^sub>o Prop
      \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
  by (rule infer_type_sound)
    (simp add:
      pp_t_indexed_equivalence_singleton_family_builder_def
      pp_t_singleton_family_builder_def
      ObjBox_def ObjTrue_def lookup_def shift_def)

lemma pp_t_indexed_equivalence_singleton_family_builder_logical:
  "pp_logical_vocabulary
    pp_t_indexed_equivalence_singleton_family_builder"
  by (simp add:
      pp_t_indexed_equivalence_singleton_family_builder_def
      pp_t_singleton_family_builder_def
      pp_logical_vocabulary_def ObjBox_def ObjTrue_def shift_def)

definition pp_t_indexed_equivalence_parameter ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_indexed_equivalence_parameter a p =
    pp_t_prop
      (\<lambda>w.
        (pp_t_holds a w \<longrightarrow> pp_t_holds p w)
        \<and> (pp_t_holds p w \<longrightarrow> pp_t_holds a w))"

lemma pp_t_indexed_equivalence_parameter_in_domain:
  "Elem (pp_t_indexed_equivalence_parameter a p)
    (pp_t_domain Prop)"
  unfolding pp_t_indexed_equivalence_parameter_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_indexed_equivalence_singleton_family_value:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "(pp_t_closed_den
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a) \<acute> p
      =
    pp_t_singleton_family_at
      (pp_t_indexed_equivalence_parameter a p)"
  unfolding
    pp_t_indexed_equivalence_singleton_family_builder_def
    pp_t_indexed_equivalence_parameter_def
    pp_t_closed_den_def
  using a p
  by (simp add: Lambda_app pp_t_eval_shift)

lemma pp_t_indexed_equivalence_parameter_true_iff:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_eqv Prop w
        (pp_t_indexed_equivalence_parameter a p)
        (pp_zf_truth True)
      \<longleftrightarrow>
    pp_t_eqv Prop w p a"
  unfolding pp_t_indexed_equivalence_parameter_def
  by auto

lemma pp_t_indexed_equivalence_parameter_false_iff:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_eqv Prop w
        (pp_t_indexed_equivalence_parameter a p)
        (pp_zf_truth False)
      \<longleftrightarrow>
    pp_t_eqv Prop w p (pp_t_complement a)"
  unfolding pp_t_indexed_equivalence_parameter_def
    pp_t_complement_def
  by auto

lemma pp_t_indexed_equivalence_probe_section_eq_symmetrized_singleton:
  assumes a: "Elem a (pp_t_domain Prop)"
  shows
    "pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a
      =
    pp_t_symmetrized_singleton_family_at a"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_indexed_family_probe_for_stock Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
      (pp_t_domain pp_t_one_context_unary_type)"
    using pp_t_indexed_family_probe_section_in_domain[
      OF pp_t_indexed_equivalence_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible a] .
  show "Elem (pp_t_symmetrized_singleton_family_at a)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF a])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "(pp_t_indexed_family_probe_for_stock Prop
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
          \<acute> p
      =
      pp_t_symmetrized_singleton_family_at a \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        ((pp_t_indexed_family_probe_for_stock Prop
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
          \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_indexed_family_probe_section_in_domain[
          OF pp_t_indexed_equivalence_singleton_family_builder_typed
            pp_t_closed_logical_stock_admissible a]
        p] .
    show "Elem (pp_t_symmetrized_singleton_family_at a \<acute> p)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_symmetrized_singleton_family_at_in_domain[OF a] p] .
    fix w
    let ?r = "pp_t_indexed_equivalence_parameter a p"
    have r: "Elem ?r (pp_t_domain Prop)"
      by (rule pp_t_indexed_equivalence_parameter_in_domain)
    have probe:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          ((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p)"
      using pp_t_indexed_family_probe_for_stock_apply_holds[
        OF pp_t_indexed_equivalence_singleton_family_builder_typed
          pp_t_closed_logical_stock_admissible a p,
        of w] .
    have stock:
        "pp_t_closed_logical_stock
            pp_t_one_context_unary_type w
            ((pp_t_closed_den
                pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
              \<acute> p)
        \<longleftrightarrow>
        (pp_t_eqv Prop w ?r (pp_zf_truth True)
          \<or> pp_t_eqv Prop w ?r (pp_zf_truth False))"
      unfolding
        pp_t_indexed_equivalence_singleton_family_value[OF a p]
      using pp_t_singleton_family_in_closed_stock_iff_settled[
        OF r, of w] .
    have parameter:
        "(pp_t_eqv Prop w ?r (pp_zf_truth True)
          \<or> pp_t_eqv Prop w ?r (pp_zf_truth False))
        \<longleftrightarrow>
        (pp_t_eqv Prop w p a
          \<or> pp_t_eqv Prop w p (pp_t_complement a))"
      using pp_t_indexed_equivalence_parameter_true_iff[
        OF a p, of w]
        pp_t_indexed_equivalence_parameter_false_iff[
          OF a p, of w]
      by blast
    have symmetrized:
        "pp_t_holds
          (pp_t_symmetrized_singleton_family_at a \<acute> p) w
        \<longleftrightarrow>
        (pp_t_eqv Prop w p a
          \<or> pp_t_eqv Prop w p (pp_t_complement a))"
      using pp_t_symmetrized_singleton_family_at_apply_holds[
        OF a p, of w] .
    show "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p) w
        \<longleftrightarrow>
        pp_t_holds
          (pp_t_symmetrized_singleton_family_at a \<acute> p) w"
      using probe stock parameter symmetrized by blast
  qed
qed

lemma pp_t_complement_left_eqv_iff:
  "pp_t_eqv Prop w (pp_t_complement p) a
    \<longleftrightarrow>
   pp_t_eqv Prop w p (pp_t_complement a)"
proof
  assume left:
      "pp_t_eqv Prop w (pp_t_complement p) a"
  show "pp_t_eqv Prop w p (pp_t_complement a)"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have "(\<not> pp_t_holds p v) = pp_t_holds a v"
      using left future by simp
    then show "pp_t_holds p v =
        pp_t_holds (pp_t_complement a) v"
      by (simp only: pp_t_complement_holds; blast)
  qed
next
  assume right:
      "pp_t_eqv Prop w p (pp_t_complement a)"
  show "pp_t_eqv Prop w (pp_t_complement p) a"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have "pp_t_holds p v = (\<not> pp_t_holds a v)"
      using right future by simp
    then show "pp_t_holds (pp_t_complement p) v =
        pp_t_holds a v"
      by (simp only: pp_t_complement_holds; blast)
  qed
qed

lemma pp_t_complement_both_eqv_iff:
  "pp_t_eqv Prop w (pp_t_complement p) (pp_t_complement a)
    \<longleftrightarrow>
   pp_t_eqv Prop w p a"
proof
  assume left:
      "pp_t_eqv Prop w
        (pp_t_complement p) (pp_t_complement a)"
  show "pp_t_eqv Prop w p a"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have "(\<not> pp_t_holds p v) =
        (\<not> pp_t_holds a v)"
      using left future by simp
    then show "pp_t_holds p v = pp_t_holds a v"
      by blast
  qed
next
  assume right: "pp_t_eqv Prop w p a"
  show "pp_t_eqv Prop w
      (pp_t_complement p) (pp_t_complement a)"
    unfolding pp_t_eqv.simps
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have "pp_t_holds p v = pp_t_holds a v"
      using right future by simp
    then show "pp_t_holds (pp_t_complement p) v =
        pp_t_holds (pp_t_complement a) v"
      by (simp only: pp_t_complement_holds; blast)
  qed
qed

lemma pp_t_symmetrized_singleton_value_apply_complement:
  assumes a: "Elem a (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_symmetrized_singleton_family_at a
        \<acute> pp_t_complement p
      =
    pp_t_symmetrized_singleton_family_at a \<acute> p"
proof (rule pp_t_prop_ext)
  show "Elem
      (pp_t_symmetrized_singleton_family_at a
        \<acute> pp_t_complement p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_symmetrized_singleton_family_at_in_domain[OF a]
        pp_t_complement_in_domain] .
  show "Elem (pp_t_symmetrized_singleton_family_at a \<acute> p)
      (pp_t_domain Prop)"
    using pp_t_app_closed[
      OF pp_t_symmetrized_singleton_family_at_in_domain[OF a] p] .
  fix w
  show "pp_t_holds
        (pp_t_symmetrized_singleton_family_at a
          \<acute> pp_t_complement p) w
      \<longleftrightarrow>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at a \<acute> p) w"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
        where p=a and q="pp_t_complement p" and w=w,
        OF a pp_t_complement_in_domain]
      pp_t_symmetrized_singleton_family_at_apply_holds[
        where p=a and q=p and w=w, OF a p]
      pp_t_complement_left_eqv_iff[
        of w p a]
      pp_t_complement_both_eqv_iff[
        of w p a]
    by blast
qed

theorem
  pp_t_symmetrized_singleton_value_has_no_singleton_family_collision:
  assumes a: "Elem a (pp_t_domain Prop)"
    and r: "Elem r (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_symmetrized_singleton_family_at a)
    (pp_t_singleton_family_at r)"
proof
  assume collision:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_symmetrized_singleton_family_at a)
        (pp_t_singleton_family_at r)"
  have rr: "pp_t_eqv Prop w r r"
    by (rule pp_t_eqv_reflexive[OF r])
  have at_r:
      "pp_t_eqv Prop w
        (pp_t_symmetrized_singleton_family_at a \<acute> r)
        (pp_t_singleton_family_at r \<acute> r)"
    using pp_t_app_respects[OF collision r r rr] .
  have singleton_r:
      "pp_t_holds (pp_t_singleton_family_at r \<acute> r) w"
    using pp_t_singleton_family_at_apply_holds[OF r r, of w]
      rr by blast
  have symmetrized_r:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at a \<acute> r) w"
    using pp_t_prop_eqv_at[OF at_r, of w]
      singleton_r by simp
  have complement_r:
      "Elem (pp_t_complement r) (pp_t_domain Prop)"
    by (rule pp_t_complement_in_domain)
  have cc:
      "pp_t_eqv Prop w (pp_t_complement r) (pp_t_complement r)"
    by (rule pp_t_eqv_reflexive[OF complement_r])
  have at_complement:
      "pp_t_eqv Prop w
        (pp_t_symmetrized_singleton_family_at a
          \<acute> pp_t_complement r)
        (pp_t_singleton_family_at r \<acute> pp_t_complement r)"
    using pp_t_app_respects[
      OF collision complement_r complement_r cc] .
  have symmetrized_complement:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at a
          \<acute> pp_t_complement r) w"
    unfolding
      pp_t_symmetrized_singleton_value_apply_complement[OF a r]
    using symmetrized_r .
  have singleton_complement:
      "pp_t_holds
        (pp_t_singleton_family_at r \<acute> pp_t_complement r) w"
    using pp_t_prop_eqv_at[OF at_complement, of w]
      symmetrized_complement by simp
  have complement_equivalent:
      "pp_t_eqv Prop w (pp_t_complement r) r"
    using pp_t_singleton_family_at_apply_holds[
      OF r complement_r, of w]
      singleton_complement by blast
  show False
    using pp_t_proposition_not_equivalent_to_its_complement[
      OF r, of w]
      complement_equivalent by blast
qed

lemma pp_t_indexed_equivalence_singleton_has_no_collisions:
  assumes a: "Elem a (pp_t_domain Prop)"
    and b: "Elem b (pp_t_domain Prop)"
    and p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv pp_t_one_context_unary_type w
    (pp_t_indexed_family_probe_for_stock Prop
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_indexed_equivalence_singleton_family_builder \<acute> b)
    ((pp_t_closed_den
        pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
      \<acute> p)"
  unfolding
    pp_t_indexed_equivalence_probe_section_eq_symmetrized_singleton[
      OF b]
    pp_t_indexed_equivalence_singleton_family_value[OF a p]
  using pp_t_symmetrized_singleton_value_has_no_singleton_family_collision[
    OF b pp_t_indexed_equivalence_parameter_in_domain, of w] .

theorem
  pp_t_indexed_equivalence_singleton_probe_stabilizes_after_all_sections_adjoined:
  "pp_t_indexed_family_probe_for_stock Prop
      (pp_t_indexed_family_section_stock_enlargement Prop
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_indexed_equivalence_singleton_family_builder)
      pp_t_indexed_equivalence_singleton_family_builder
    =
    pp_t_indexed_family_probe_for_stock Prop
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_indexed_equivalence_singleton_family_builder"
proof -
  have all_collisions:
      "\<forall>a p w.
        Elem a (pp_t_domain Prop)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>b.
          Elem b (pp_t_domain Prop)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock Prop
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_indexed_equivalence_singleton_family_builder \<acute> b)
            ((pp_t_closed_den
                pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
              \<acute> p))
        \<longrightarrow>
        pp_t_closed_logical_stock
          pp_t_one_context_unary_type w
          ((pp_t_closed_den
              pp_t_indexed_equivalence_singleton_family_builder \<acute> a)
            \<acute> p)"
    using pp_t_indexed_equivalence_singleton_has_no_collisions
    by blast
  show ?thesis
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF pp_t_indexed_equivalence_singleton_family_builder_typed
        pp_t_closed_logical_stock_admissible]
      all_collisions by (rule iffD2)
qed

end
