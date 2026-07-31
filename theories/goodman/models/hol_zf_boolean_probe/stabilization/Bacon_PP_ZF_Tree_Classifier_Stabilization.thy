theory Bacon_PP_ZF_Tree_Classifier_Stabilization
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Finite_Model.Bacon_PP_ZF_Tree_Boolean_Probe_Finite_Model
begin

section \<open>A reusable classifier-cycle absorption criterion\<close>

lemma pp_t_negation_closed_stock_complement_iff:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and complement_closed:
      "\<And>w Y.
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow> S w Y
        \<Longrightarrow> S w (pp_t_unary_complement Y)"
  shows "S w (pp_t_unary_complement X) \<longleftrightarrow> S w X"
proof
  assume complemented: "S w (pp_t_unary_complement X)"
  have twice:
      "S w
        (pp_t_unary_complement (pp_t_unary_complement X))"
    by (rule complement_closed[
      OF pp_t_unary_complement_in_domain[OF X] complemented])
  show "S w X"
    using twice pp_t_unary_complement_involution[OF X]
    by simp
next
  assume stock: "S w X"
  show "S w (pp_t_unary_complement X)"
    by (rule complement_closed[OF X stock])
qed

theorem pp_t_negation_closed_stock_complemented_probe_eq:
  assumes S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and complement_closed:
      "\<And>w X.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow> S w X
        \<Longrightarrow> S w (pp_t_unary_complement X)"
  shows "pp_t_family_probe_for_stock S
      pp_t_complemented_symmetrized_singleton_family_builder
    =
    pp_t_family_probe_for_stock S
      pp_t_symmetrized_singleton_family_builder"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock S
        pp_t_complemented_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_family_probe_for_stock_in_domain[
      OF
        pp_t_complemented_symmetrized_singleton_family_builder_typed
        S_admissible])
  show "Elem
      (pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_family_probe_for_stock_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  let ?Bp = "pp_t_symmetrized_singleton_family_at p"
  show "pp_t_family_probe_for_stock S
          pp_t_complemented_symmetrized_singleton_family_builder
          \<acute> p
      =
      pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder
          \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock S
          pp_t_complemented_symmetrized_singleton_family_builder
          \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            S_admissible]
          p])
    show "Elem
        (pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder
          \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed
            S_admissible]
          p])
    fix w
    have Bp:
        "Elem ?Bp (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
    have stock_iff:
        "S w (pp_t_complemented_symmetrized_singleton_family_at p)
        \<longleftrightarrow> S w ?Bp"
      unfolding
        pp_t_complemented_symmetrized_singleton_family_at_eq[OF p]
      by (rule pp_t_negation_closed_stock_complement_iff[
        where S=S and w=w, OF Bp complement_closed])
    show "pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_complemented_symmetrized_singleton_family_builder
            \<acute> p) w
        =
        pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_symmetrized_singleton_family_builder
            \<acute> p) w"
      using pp_t_family_probe_for_stock_apply_holds[
          OF
            pp_t_complemented_symmetrized_singleton_family_builder_typed
            S_admissible p,
          of w]
        pp_t_family_probe_for_stock_apply_holds[
          OF pp_t_symmetrized_singleton_family_builder_typed
            S_admissible p,
          of w]
        stock_iff
      by blast
  qed
qed

lemma
  pp_t_symmetrized_singleton_cone_natural_parameter_classification:
  assumes p: "Elem p (pp_t_domain Prop)"
    and family_cone:
      "\<And>s.
        pp_t_cone_rel pp_t_boolean_probe_unary_type s
          (pp_t_symmetrized_singleton_family_at p)
          (pp_t_symmetrized_singleton_family_at p)"
  shows "p =
    pp_t_word_character_prop
      (pp_t_holds p [])
      (pp_t_holds p [True] \<noteq> pp_t_holds p [])
      (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
proof -
  have stable:
      "pp_t_family_same_value_on_relative_views
        pp_t_symmetrized_singleton_family_builder [] p"
    unfolding pp_t_family_same_value_on_relative_views_def
      pp_t_cone_view_empty[OF p]
  proof
    fix s
    show "pp_t_symmetrized_singleton_family_at
          (pp_t_cone_view s p)
        =
        pp_t_symmetrized_singleton_family_at p"
      by (rule
        pp_t_logical_family_cone_natural_forces_same_value[
          OF pp_t_symmetrized_singleton_family_builder_typed
            pp_t_symmetrized_singleton_family_builder_logical
            p family_cone])
  qed
  show ?thesis
    by (rule
      pp_t_symmetrized_family_stable_parameter_is_word_character[
        OF p stable])
qed

theorem
  pp_t_fixed_cone_natural_symmetrized_singleton_family_reduction:
  assumes p: "Elem p (pp_t_domain Prop)"
    and family_cone:
      "\<And>s.
        pp_t_cone_rel pp_t_boolean_probe_unary_type s
          (pp_t_symmetrized_singleton_family_at p)
          (pp_t_symmetrized_singleton_family_at p)"
    and family_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type
          (pp_t_symmetrized_singleton_family_at p)
        =
        pp_t_symmetrized_singleton_family_at p"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    pp_t_symmetrized_singleton_family_at p
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
proof -
  have parameter:
      "p =
        pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p [])"
    by (rule
      pp_t_symmetrized_singleton_cone_natural_parameter_classification[
        OF p family_cone])
  have reduced:
      "pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p [])))
      \<or>
      pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p []))
        =
        pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity"
  proof (rule pp_t_fixed_canonical_character_family_reduction)
    show "pp_t_aut pp_t_boolean_probe_unary_type
        (pp_t_symmetrized_singleton_family_at
          (pp_t_word_character_prop
            (pp_t_holds p [])
            (pp_t_holds p [True] \<noteq> pp_t_holds p [])
            (pp_t_holds p [False] \<noteq> pp_t_holds p [])))
      =
      pp_t_symmetrized_singleton_family_at
        (pp_t_word_character_prop
          (pp_t_holds p [])
          (pp_t_holds p [True] \<noteq> pp_t_holds p [])
          (pp_t_holds p [False] \<noteq> pp_t_holds p []))"
      using family_fixed parameter by simp
  qed
  show ?thesis
    using reduced parameter by simp
qed

lemma pp_t_invariant_stock_family_member_reduction:
  assumes p: "Elem p (pp_t_domain Prop)"
    and member:
      "S [] (pp_t_symmetrized_singleton_family_at p)"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
  shows "pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    pp_t_symmetrized_singleton_family_at p
      =
      pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity"
  by (rule
    pp_t_fixed_cone_natural_symmetrized_singleton_family_reduction[
      OF p members_cone_natural[OF member] members_fixed[OF member]])

theorem pp_t_invariant_stock_family_membership_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
  shows "S [] (pp_t_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_probe_boolean_stock []
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    (S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) [])"
proof
  let ?Fp = "pp_t_symmetrized_singleton_family_at p"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  assume member: "S [] ?Fp"
  have family_cone:
      "\<And>s. pp_t_cone_rel pp_t_boolean_probe_unary_type s
        ?Fp ?Fp"
    by (rule members_cone_natural[OF member])
  have family_fixed:
      "pp_t_aut pp_t_boolean_probe_unary_type ?Fp = ?Fp"
    by (rule members_fixed[OF member])
  have reduced:
      "pp_t_probe_boolean_stock [] ?Fp \<or> ?Fp = ?L"
    by (rule
      pp_t_fixed_cone_natural_symmetrized_singleton_family_reduction[
        OF p family_cone family_fixed])
  from reduced show
      "pp_t_probe_boolean_stock [] ?Fp
      \<or> S [] ?L \<and> pp_t_holds (?L \<acute> p) []"
  proof
    assume old: "pp_t_probe_boolean_stock [] ?Fp"
    then show ?thesis by blast
  next
    assume equality: "?Fp = ?L"
    have holds: "pp_t_holds (?L \<acute> p) []"
      using pp_t_even_length_family_holds_iff_view_family[
        OF p, of "[]"] equality
        pp_t_cone_view_empty[OF p]
      by simp
    have length_member: "S [] ?L"
      using member equality by simp
    show ?thesis using length_member holds by blast
  qed
next
  let ?Fp = "pp_t_symmetrized_singleton_family_at p"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  assume right:
      "pp_t_probe_boolean_stock [] ?Fp
      \<or> S [] ?L \<and> pp_t_holds (?L \<acute> p) []"
  from right show "S [] ?Fp"
  proof
    assume old: "pp_t_probe_boolean_stock [] ?Fp"
    show ?thesis by (rule old_subset[OF old])
  next
    assume length: "S [] ?L \<and> pp_t_holds (?L \<acute> p) []"
    have equality: "?Fp = ?L"
      using pp_t_even_length_family_holds_iff_view_family[
        OF p, of "[]"] length
        pp_t_cone_view_empty[OF p]
      by simp
    show ?thesis using length equality by simp
  qed
qed

lemma pp_t_invariant_stock_family_probe_holds_iff:
  assumes p: "Elem p (pp_t_domain Prop)"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
  shows "pp_t_holds
      (pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder \<acute> p) []
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_probe_boolean_family_probe \<acute> p) []
    \<or>
    (S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) [])"
proof -
  have new_probe:
      "pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_symmetrized_singleton_family_builder \<acute> p) []
      \<longleftrightarrow>
      S [] (pp_t_symmetrized_singleton_family_at p)"
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible p])
  have prior_probe:
      "pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> p) []
      \<longleftrightarrow>
      pp_t_probe_boolean_stock []
        (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_probe_boolean_family_probe_def
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_boolean_stock_admissible p])
  show ?thesis
    using new_probe prior_probe
      pp_t_invariant_stock_family_membership_iff[
        where S=S, OF p old_subset members_cone_natural members_fixed]
    by blast
qed

theorem pp_t_invariant_stock_family_membership_iff_at:
  assumes p: "Elem p (pp_t_domain Prop)"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
  shows "S w (pp_t_symmetrized_singleton_family_at p)
    \<longleftrightarrow>
    pp_t_probe_boolean_stock w
      (pp_t_symmetrized_singleton_family_at p)
    \<or>
    (S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) w)"
proof -
  let ?q = "pp_t_cone_view w p"
  let ?Fp = "pp_t_symmetrized_singleton_family_at p"
  let ?Fq = "pp_t_symmetrized_singleton_family_at ?q"
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_cone_view_in_domain)
  have Fp:
      "Elem ?Fp (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF p])
  have Fq:
      "Elem ?Fq (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_symmetrized_singleton_family_at_in_domain[OF q])
  have family_cone:
      "pp_t_cone_rel pp_t_boolean_probe_unary_type w ?Fp ?Fq"
    by (rule pp_t_logical_family_at_cone_related[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_symmetrized_singleton_family_builder_logical p])
  have S_transport: "S w ?Fp \<longleftrightarrow> S [] ?Fq"
    by (rule stock_cone_iff[OF Fp Fq family_cone])
  have old_transport:
      "pp_t_probe_boolean_stock w ?Fp
      \<longleftrightarrow>
      pp_t_probe_boolean_stock [] ?Fq"
    using pp_t_probe_boolean_stock_cone_iff[
      OF Fp Fq family_cone, of "[]"]
    by simp
  have root:
      "S [] ?Fq
      \<longleftrightarrow>
      pp_t_probe_boolean_stock [] ?Fq
      \<or> S [] ?L \<and> pp_t_holds (?L \<acute> ?q) []"
    by (rule pp_t_invariant_stock_family_membership_iff[
      where S=S,
      OF q old_subset members_cone_natural members_fixed])
  have length_transport:
      "pp_t_holds (?L \<acute> p) w
      \<longleftrightarrow>
      pp_t_holds (?L \<acute> ?q) []"
  proof -
    have left:
        "pp_t_holds (?L \<acute> p) w
        \<longleftrightarrow> ?Fq = ?L"
      by (rule pp_t_even_length_family_holds_iff_view_family[
        OF p, of w])
    have right:
        "pp_t_holds (?L \<acute> ?q) []
        \<longleftrightarrow> ?Fq = ?L"
      using pp_t_even_length_family_holds_iff_view_family[
          OF q, of "[]"]
        pp_t_cone_view_empty[OF q]
      by simp
    show ?thesis using left right by blast
  qed
  show ?thesis
    using S_transport old_transport root length_transport
    by blast
qed

lemma pp_t_invariant_stock_family_probe_holds_iff_at:
  assumes p: "Elem p (pp_t_domain Prop)"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
  shows "pp_t_holds
      (pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder \<acute> p) w
    \<longleftrightarrow>
    pp_t_holds
      (pp_t_probe_boolean_family_probe \<acute> p) w
    \<or>
    (S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)
      \<and>
      pp_t_holds
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity \<acute> p) w)"
proof -
  have new_probe:
      "pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_symmetrized_singleton_family_builder \<acute> p) w
      \<longleftrightarrow>
      S w (pp_t_symmetrized_singleton_family_at p)"
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible p])
  have prior_probe:
      "pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> p) w
      \<longleftrightarrow>
      pp_t_probe_boolean_stock w
        (pp_t_symmetrized_singleton_family_at p)"
    unfolding pp_t_probe_boolean_family_probe_def
    by (rule pp_t_family_probe_for_stock_apply_holds[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_boolean_stock_admissible p])
  show ?thesis
    using new_probe prior_probe
      pp_t_invariant_stock_family_membership_iff_at[
        where S=S,
        OF p old_subset members_cone_natural members_fixed
          stock_cone_iff]
    by blast
qed

lemma pp_t_invariant_stock_family_probe_eq_prior_if_no_length:
  assumes S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
    and no_length:
      "\<not> S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
  shows "pp_t_family_probe_for_stock S
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_probe_boolean_family_probe"
proof (rule pp_t_unary_function_ext)
  show "Elem
      (pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_family_probe_for_stock_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible])
  show "Elem pp_t_probe_boolean_family_probe
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_probe_boolean_family_probe_in_domain)
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder \<acute> p
      =
      pp_t_probe_boolean_family_probe \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed
            S_admissible] p])
    show "Elem (pp_t_probe_boolean_family_probe \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_probe_boolean_family_probe_in_domain p])
    fix w
    show "pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_symmetrized_singleton_family_builder \<acute> p) w
        =
        pp_t_holds
          (pp_t_probe_boolean_family_probe \<acute> p) w"
      using pp_t_invariant_stock_family_probe_holds_iff_at[
        where S=S,
        OF p S_admissible old_subset members_cone_natural
          members_fixed stock_cone_iff]
        no_length
      by blast
  qed
qed

lemma pp_t_invariant_stock_family_probe_eq_disjunction_if_length:
  assumes S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
    and length:
      "S []
        (pp_t_symmetrized_singleton_family_at
          pp_t_even_length_parity)"
  shows "pp_t_family_probe_for_stock S
      pp_t_symmetrized_singleton_family_builder
    =
    pp_t_unary_output_disjunction
      pp_t_probe_boolean_family_probe
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)"
proof (rule pp_t_unary_function_ext)
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  show "Elem
      (pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_family_probe_for_stock_in_domain[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible])
  show "Elem
      (pp_t_unary_output_disjunction
        pp_t_probe_boolean_family_probe ?L)
      (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_unary_output_disjunction_in_domain[
      OF pp_t_probe_boolean_family_probe_in_domain
        pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_even_length_parity_in_domain]])
  fix p
  assume p: "Elem p (pp_t_domain Prop)"
  show "pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder \<acute> p
      =
      pp_t_unary_output_disjunction
        pp_t_probe_boolean_family_probe ?L \<acute> p"
  proof (rule pp_t_prop_ext)
    show "Elem
        (pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_family_probe_for_stock_in_domain[
          OF pp_t_symmetrized_singleton_family_builder_typed
            S_admissible] p])
    show "Elem
        (pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L \<acute> p)
        (pp_t_domain Prop)"
      by (rule pp_t_app_closed[
        OF pp_t_unary_output_disjunction_in_domain[
          OF pp_t_probe_boolean_family_probe_in_domain
            pp_t_symmetrized_singleton_family_at_in_domain[
              OF pp_t_even_length_parity_in_domain]]
          p])
    fix w
    show "pp_t_holds
          (pp_t_family_probe_for_stock S
            pp_t_symmetrized_singleton_family_builder \<acute> p) w
        =
        pp_t_holds
          (pp_t_unary_output_disjunction
            pp_t_probe_boolean_family_probe ?L \<acute> p) w"
      using pp_t_invariant_stock_family_probe_holds_iff_at[
          where S=S,
          OF p S_admissible old_subset members_cone_natural
            members_fixed stock_cone_iff]
        pp_t_unary_output_disjunction_apply_holds[
          OF pp_t_probe_boolean_family_probe_in_domain
            pp_t_symmetrized_singleton_family_at_in_domain[
              OF pp_t_even_length_parity_in_domain]
            p,
          of w]
        length
      by blast
  qed
qed

theorem pp_t_invariant_boolean_stock_absorbs_family_probe_at_root:
  assumes S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
    and prior_probe:
      "S [] pp_t_probe_boolean_family_probe"
    and disjunction_closed:
      "\<And>X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        S [] X
        \<Longrightarrow>
        S [] Y
        \<Longrightarrow>
        S [] (pp_t_unary_output_disjunction X Y)"
  shows "S []
    (pp_t_family_probe_for_stock S
      pp_t_symmetrized_singleton_family_builder)"
proof (cases
    "S []
      (pp_t_symmetrized_singleton_family_at
        pp_t_even_length_parity)")
  case False
  have equality:
      "pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder
        =
        pp_t_probe_boolean_family_probe"
    by (rule
      pp_t_invariant_stock_family_probe_eq_prior_if_no_length[
        where S=S,
        OF S_admissible old_subset members_cone_natural
          members_fixed stock_cone_iff False])
  show ?thesis using prior_probe equality by simp
next
  case True
  let ?L =
    "pp_t_symmetrized_singleton_family_at
      pp_t_even_length_parity"
  have disjunction:
      "S []
        (pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L)"
    by (rule disjunction_closed[
      OF pp_t_probe_boolean_family_probe_in_domain
        pp_t_symmetrized_singleton_family_at_in_domain[
          OF pp_t_even_length_parity_in_domain]
        prior_probe True])
  have equality:
      "pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder
        =
        pp_t_unary_output_disjunction
          pp_t_probe_boolean_family_probe ?L"
    by (rule
      pp_t_invariant_stock_family_probe_eq_disjunction_if_length[
        where S=S,
        OF S_admissible old_subset members_cone_natural
          members_fixed stock_cone_iff True])
  show ?thesis using disjunction equality by simp
qed

theorem pp_t_family_probe_in_stock_implies_fixed_point:
  assumes B_typed:
      "[] \<turnstile> B :
        Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type"
    and S_admissible:
      "pp_t_predicate_admissible
        pp_t_one_context_unary_type S"
    and probe_in_stock:
      "\<And>w. S w (pp_t_family_probe_for_stock S B)"
  shows
    "(\<forall>w X.
      Elem X (pp_t_domain pp_t_one_context_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement S B w X
        \<longleftrightarrow> S w X))
    \<and>
    pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B
      =
      pp_t_family_probe_for_stock S B"
proof
  show "\<forall>w X.
      Elem X (pp_t_domain pp_t_one_context_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement S B w X
        \<longleftrightarrow> S w X)"
  proof (intro allI impI)
    fix w X
    assume X:
        "Elem X (pp_t_domain pp_t_one_context_unary_type)"
    show "pp_t_family_probe_stock_enlargement S B w X
        \<longleftrightarrow> S w X"
    proof
      assume enlarged:
          "pp_t_family_probe_stock_enlargement S B w X"
      from enlarged consider
          (old) "S w X"
        | (new)
            "pp_t_eqv pp_t_one_context_unary_type w
              (pp_t_family_probe_for_stock S B) X"
        unfolding pp_t_family_probe_stock_enlargement_def
        by blast
      then show "S w X"
      proof cases
        case old
        then show ?thesis .
      next
        case new
        have probe_domain:
            "Elem (pp_t_family_probe_for_stock S B)
              (pp_t_domain pp_t_one_context_unary_type)"
          by (rule pp_t_family_probe_for_stock_in_domain[
            OF B_typed S_admissible])
        have same:
            "S w (pp_t_family_probe_for_stock S B) = S w X"
          using S_admissible probe_domain X new
          unfolding pp_t_predicate_admissible_def
          by (metis prefix_order.refl)
        show ?thesis
          using same probe_in_stock[of w] by blast
      qed
    next
      assume stock: "S w X"
      show "pp_t_family_probe_stock_enlargement S B w X"
        unfolding pp_t_family_probe_stock_enlargement_def
        using stock by blast
    qed
  qed
  have collisions:
      "\<forall>p w.
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S B)
          (pp_t_closed_den B \<acute> p)
        \<longrightarrow>
        S w (pp_t_closed_den B \<acute> p)"
  proof (intro allI impI)
    fix p w
    assume p: "Elem p (pp_t_domain Prop)"
      and collision:
        "pp_t_eqv pp_t_one_context_unary_type w
          (pp_t_family_probe_for_stock S B)
          (pp_t_closed_den B \<acute> p)"
    have probe_domain:
        "Elem (pp_t_family_probe_for_stock S B)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_family_probe_for_stock_in_domain[
        OF B_typed S_admissible])
    have B_den:
        "Elem (pp_t_closed_den B)
          (pp_t_domain
            (Prop \<rightarrow>\<^sub>o pp_t_one_context_unary_type))"
      by (rule pp_t_closed_den_in_domain[OF B_typed])
    have Bp_domain:
        "Elem (pp_t_closed_den B \<acute> p)
          (pp_t_domain pp_t_one_context_unary_type)"
      by (rule pp_t_app_closed[OF B_den p])
    have same:
        "S w (pp_t_family_probe_for_stock S B)
          =
          S w (pp_t_closed_den B \<acute> p)"
      using S_admissible probe_domain Bp_domain collision
      unfolding pp_t_predicate_admissible_def
      by (metis prefix_order.refl)
    show "S w (pp_t_closed_den B \<acute> p)"
      using same probe_in_stock[of w] by blast
  qed
  show "pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement S B) B
      =
      pp_t_family_probe_for_stock S B"
    using collisions
      pp_t_family_probe_stabilizes_iff_collisions_absorbed[
        OF B_typed S_admissible]
    by blast
qed

theorem pp_t_invariant_boolean_stock_classifier_fixed_point:
  assumes S_admissible:
      "pp_t_predicate_admissible
        pp_t_boolean_probe_unary_type S"
    and old_subset:
      "\<And>X. pp_t_probe_boolean_stock [] X \<Longrightarrow> S [] X"
    and members_cone_natural:
      "\<And>X s. S [] X \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type s X X"
    and members_fixed:
      "\<And>X. S [] X \<Longrightarrow>
        pp_t_aut pp_t_boolean_probe_unary_type X = X"
    and stock_cone_iff:
      "\<And>w X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        pp_t_cone_rel pp_t_boolean_probe_unary_type w X Y
        \<Longrightarrow>
        (S w X \<longleftrightarrow> S [] Y)"
    and prior_probe:
      "S [] pp_t_probe_boolean_family_probe"
    and disjunction_closed:
      "\<And>X Y.
        Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)
        \<Longrightarrow>
        S [] X
        \<Longrightarrow>
        S [] Y
        \<Longrightarrow>
        S [] (pp_t_unary_output_disjunction X Y)"
    and root_persistent:
      "\<And>w X. S [] X \<Longrightarrow> S w X"
  shows
    "(\<forall>w X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement
          S pp_t_symmetrized_singleton_family_builder w X
        \<longleftrightarrow> S w X))
    \<and>
    pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement
          S pp_t_symmetrized_singleton_family_builder)
        pp_t_symmetrized_singleton_family_builder
      =
      pp_t_family_probe_for_stock S
        pp_t_symmetrized_singleton_family_builder"
proof -
  have probe_root:
      "S []
        (pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder)"
    by (rule
      pp_t_invariant_boolean_stock_absorbs_family_probe_at_root[
        where S=S,
        OF S_admissible old_subset members_cone_natural
          members_fixed stock_cone_iff prior_probe
          disjunction_closed])
  have probe_all:
      "\<And>w. S w
        (pp_t_family_probe_for_stock S
          pp_t_symmetrized_singleton_family_builder)"
    by (rule root_persistent[OF probe_root])
  show ?thesis
    by (rule pp_t_family_probe_in_stock_implies_fixed_point[
      OF pp_t_symmetrized_singleton_family_builder_typed
        S_admissible probe_all])
qed

corollary pp_t_probe_successor_stock_is_classifier_fixed_point:
  "(\<forall>w X.
      Elem X (pp_t_domain pp_t_boolean_probe_unary_type)
      \<longrightarrow>
      (pp_t_family_probe_stock_enlargement
          pp_t_probe_successor_stock
          pp_t_symmetrized_singleton_family_builder w X
        \<longleftrightarrow>
        pp_t_probe_successor_stock w X))
    \<and>
    pp_t_family_probe_for_stock
        (pp_t_family_probe_stock_enlargement
          pp_t_probe_successor_stock
          pp_t_symmetrized_singleton_family_builder)
        pp_t_symmetrized_singleton_family_builder
      =
      pp_t_probe_successor_family_probe"
proof -
  have probe_in:
      "\<And>w. pp_t_probe_successor_stock w
        (pp_t_family_probe_for_stock
          pp_t_probe_successor_stock
          pp_t_symmetrized_singleton_family_builder)"
    unfolding pp_t_probe_successor_family_probe_def[symmetric]
    by (rule pp_t_probe_successor_family_probe_in_stock)
  show ?thesis
    using pp_t_family_probe_in_stock_implies_fixed_point[
      OF pp_t_symmetrized_singleton_family_builder_typed
        pp_t_probe_successor_stock_admissible probe_in]
    unfolding pp_t_probe_successor_family_probe_def .
qed

end
