theory Bacon_PP_ZF_Tree_Boolean_Probe_Classification
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Core.Bacon_PP_ZF_Tree_Boolean_Probe_Closure
begin

section \<open>Classification of the symmetrized family’s stable parameters\<close>

fun pp_t_word_character ::
    "bool \<Rightarrow> bool \<Rightarrow> bool list \<Rightarrow> bool"
where
  "pp_t_word_character on_true on_false [] = False"
| "pp_t_word_character on_true on_false (b # w) =
    ((if b then on_true else on_false)
      \<noteq> pp_t_word_character on_true on_false w)"

lemma pp_t_word_character_append:
  "pp_t_word_character on_true on_false (s @ u) =
    (pp_t_word_character on_true on_false s
      \<noteq> pp_t_word_character on_true on_false u)"
  by (induction s) (auto split: if_splits)

theorem pp_t_two_state_left_quotient_classification:
  fixes f :: "bool list \<Rightarrow> bool"
  assumes quotient:
      "\<And>s.
        (\<forall>u. f (s @ u) = f u)
        \<or> (\<forall>u. f (s @ u) = (\<not> f u))"
  shows "f w =
    (f [] \<noteq>
      pp_t_word_character
        (f [True] \<noteq> f [])
        (f [False] \<noteq> f []) w)"
proof -
  have append:
      "\<And>s u. f (s @ u) =
        ((f s \<noteq> f []) \<noteq> f u)"
  proof -
    fix s u
    from quotient[of s] show
        "f (s @ u) = ((f s \<noteq> f []) \<noteq> f u)"
    proof
      assume same: "\<forall>u. f (s @ u) = f u"
      have fs: "f s = f []"
        using same[rule_format, of "[]"] by simp
      show ?thesis
        using same[rule_format, of u] fs by simp
    next
      assume opposite:
          "\<forall>u. f (s @ u) = (\<not> f u)"
      have fs: "f s = (\<not> f [])"
        using opposite[rule_format, of "[]"] by simp
      show ?thesis
        using opposite[rule_format, of u] fs by simp
    qed
  qed
  show ?thesis
  proof (induction w)
    case Nil
    then show ?case by simp
  next
    case (Cons b w)
    have step:
        "f (b # w) =
          ((f [b] \<noteq> f []) \<noteq> f w)"
      using append[of "[b]" w] by simp
    show ?case
      using step Cons.IH
      by (cases b) auto
  qed
qed

definition pp_t_word_character_prop ::
    "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ZF"
where
  "pp_t_word_character_prop initial on_true on_false =
    pp_t_prop
      (\<lambda>w. initial \<noteq>
        pp_t_word_character on_true on_false w)"

lemma pp_t_word_character_prop_in_domain:
  "Elem (pp_t_word_character_prop initial on_true on_false)
    (pp_t_domain Prop)"
  unfolding pp_t_word_character_prop_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_word_character_prop_holds[simp]:
  "pp_t_holds
      (pp_t_word_character_prop initial on_true on_false) w
    \<longleftrightarrow>
    (initial \<noteq>
      pp_t_word_character on_true on_false w)"
  by (simp add: pp_t_word_character_prop_def)

lemma pp_t_symmetrized_family_values_equal_imp_parameter_pair:
  assumes p: "Elem p (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
    and value_eq:
      "pp_t_symmetrized_singleton_family_at q =
        pp_t_symmetrized_singleton_family_at p"
  shows "q = p \<or> q = pp_t_complement p"
proof -
  have at_q:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at q \<acute> q) []"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
      OF q q, of "[]"]
      pp_t_eqv_reflexive[OF q]
    by blast
  have p_at_q:
      "pp_t_holds
        (pp_t_symmetrized_singleton_family_at p \<acute> q) []"
    using at_q value_eq by simp
  have pair:
      "pp_t_eqv Prop [] q p
        \<or> pp_t_eqv Prop [] q (pp_t_complement p)"
    using pp_t_symmetrized_singleton_family_at_apply_holds[
      OF p q, of "[]"]
      p_at_q by blast
  show ?thesis
    using pair
      pp_t_root_eqv_iff_eq[OF q p]
      pp_t_root_eqv_iff_eq[
        OF q pp_t_complement_in_domain]
    by blast
qed

theorem
  pp_t_symmetrized_family_stable_parameter_is_word_character:
  assumes p: "Elem p (pp_t_domain Prop)"
    and stable:
      "pp_t_family_same_value_on_relative_views
        pp_t_symmetrized_singleton_family_builder [] p"
  shows "p =
    pp_t_word_character_prop
      (pp_t_holds p [])
      (pp_t_holds p [True] \<noteq> pp_t_holds p [])
      (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
proof -
  have view_pair:
      "\<And>s. pp_t_cone_view s p = p
        \<or> pp_t_cone_view s p = pp_t_complement p"
  proof -
    fix s
    have family_eq:
        "pp_t_symmetrized_singleton_family_at
            (pp_t_cone_view s p)
          =
          pp_t_symmetrized_singleton_family_at p"
      using stable
      unfolding pp_t_family_same_value_on_relative_views_def
      using pp_t_cone_view_empty[OF p]
      by simp
    show "pp_t_cone_view s p = p
        \<or> pp_t_cone_view s p = pp_t_complement p"
      by (rule
        pp_t_symmetrized_family_values_equal_imp_parameter_pair[
          OF p pp_t_cone_view_in_domain[of s p] family_eq])
  qed
  let ?f = "\<lambda>w. pp_t_holds p w"
  have quotient:
      "\<And>s.
        (\<forall>u. ?f (s @ u) = ?f u)
        \<or> (\<forall>u. ?f (s @ u) = (\<not> ?f u))"
  proof -
    fix s
    from view_pair[of s] show
        "(\<forall>u. ?f (s @ u) = ?f u)
        \<or> (\<forall>u. ?f (s @ u) = (\<not> ?f u))"
    proof
      assume same: "pp_t_cone_view s p = p"
      have "\<forall>u. ?f (s @ u) = ?f u"
      proof
        fix u
        have at_u:
            "pp_t_holds (pp_t_cone_view s p) u =
              pp_t_holds p u"
          by (rule arg_cong[OF same])
        show "?f (s @ u) = ?f u"
          using at_u by simp
      qed
      then show ?thesis by blast
    next
      assume opposite:
          "pp_t_cone_view s p = pp_t_complement p"
      have "\<forall>u. ?f (s @ u) = (\<not> ?f u)"
      proof
        fix u
        have at_u:
            "pp_t_holds (pp_t_cone_view s p) u =
              pp_t_holds (pp_t_complement p) u"
          by (rule arg_cong[OF opposite])
        show "?f (s @ u) = (\<not> ?f u)"
          using at_u by simp
      qed
      then show ?thesis by blast
    qed
  qed
  have classification:
      "\<And>w. ?f w =
        (?f [] \<noteq>
          pp_t_word_character
            (?f [True] \<noteq> ?f [])
            (?f [False] \<noteq> ?f []) w)"
    by (rule
      pp_t_two_state_left_quotient_classification[
        OF quotient])
  show ?thesis
  proof (rule pp_t_prop_ext)
    show "Elem p (pp_t_domain Prop)"
      by (rule p)
    show "Elem
        (pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p []))
        (pp_t_domain Prop)"
      by (rule pp_t_word_character_prop_in_domain)
    fix w
    show "pp_t_holds p w =
      pp_t_holds
        (pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p [])) w"
      using classification[of w] by simp
  qed
qed


end
