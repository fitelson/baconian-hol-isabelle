theory Bacon_PP_ZF_Tree_Operator_Indexed_Collision
  imports
    Higher_Order_Metaphysics_PP_ZF_Operator_Indexed_Singleton.Bacon_PP_ZF_Tree_Operator_Indexed_Singleton
begin

section \<open>Realizing persistent predicates as settledness profiles\<close>

definition pp_t_persistent_settledness_lift ::
    "(bool list \<Rightarrow> bool) \<Rightarrow> ZF"
where
  "pp_t_persistent_settledness_lift A =
    pp_t_prop
      (\<lambda>w.
        A w
        \<or> (\<not> (\<exists>v. prefix w v \<and> A v)
          \<and> pp_t_holds pp_t_even_false_parity w))"

lemma pp_t_persistent_settledness_lift_in_domain:
  "Elem (pp_t_persistent_settledness_lift A)
    (pp_t_domain Prop)"
  unfolding pp_t_persistent_settledness_lift_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_persistent_settledness_lift_holds[simp]:
  "pp_t_holds (pp_t_persistent_settledness_lift A) w
    \<longleftrightarrow>
    (A w
      \<or> (\<not> (\<exists>v. prefix w v \<and> A v)
        \<and> pp_t_holds pp_t_even_false_parity w))"
  by (simp add: pp_t_persistent_settledness_lift_def)

lemma pp_t_even_false_parity_toggles:
  "pp_t_holds pp_t_even_false_parity (w @ [False])
    \<longleftrightarrow>
    \<not> pp_t_holds pp_t_even_false_parity w"
  by simp

lemma pp_t_persistent_settledness_lift_eqv_truth:
  assumes persistent:
    "\<And>w v. prefix w v \<Longrightarrow> A w \<Longrightarrow> A v"
  shows
    "pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth True)
      \<longleftrightarrow>
    A w"
proof
  assume lift_true:
      "pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth True)"
  show "A w"
  proof (rule ccontr)
    assume not_A: "\<not> A w"
    have all_true:
        "\<And>v. prefix w v \<Longrightarrow>
          pp_t_holds (pp_t_persistent_settledness_lift A) v"
      using lift_true pp_t_prop_eqv_truth_iff by blast
    show False
    proof (cases "\<exists>v. prefix w v \<and> A v")
      case True
      then show False
        using all_true[of w] not_A by simp
    next
      case False
      show False
      proof (cases "pp_t_holds pp_t_even_false_parity w")
        case True
        have no_A_future:
            "\<not> (\<exists>v.
              prefix (w @ [False]) v \<and> A v)"
        proof
          assume "\<exists>v. prefix (w @ [False]) v \<and> A v"
          then obtain v where wF_v: "prefix (w @ [False]) v"
            and Av: "A v"
            by blast
          have w_v: "prefix w v"
            using wF_v prefix_order.trans[of w "w @ [False]" v]
            by simp
          show False
            using False w_v Av by blast
        qed
        have not_parity:
            "\<not> pp_t_holds
              pp_t_even_false_parity (w @ [False])"
          using True pp_t_even_false_parity_toggles by blast
        have not_lift:
            "\<not> pp_t_holds
              (pp_t_persistent_settledness_lift A)
              (w @ [False])"
          using False no_A_future not_parity by simp
        show False
          using all_true[of "w @ [False]"] not_lift by simp
      next
        case False
        then show False
          using all_true[of w] \<open>\<not> A w\<close> by simp
      qed
    qed
  qed
next
  assume A: "A w"
  show "pp_t_eqv Prop w
      (pp_t_persistent_settledness_lift A)
      (pp_zf_truth True)"
    unfolding pp_t_prop_eqv_truth_iff
    using persistent A by simp
qed

lemma pp_t_persistent_settledness_lift_not_eqv_false:
  assumes persistent:
    "\<And>w v. prefix w v \<Longrightarrow> A w \<Longrightarrow> A v"
    and not_A: "\<not> A w"
  shows "\<not> pp_t_eqv Prop w
    (pp_t_persistent_settledness_lift A)
    (pp_zf_truth False)"
proof
  assume lift_false:
      "pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth False)"
  have all_false:
      "\<And>v. prefix w v \<Longrightarrow>
        \<not> pp_t_holds (pp_t_persistent_settledness_lift A) v"
  proof -
    fix v
    assume wv: "prefix w v"
    have at_v:
        "pp_t_holds (pp_t_persistent_settledness_lift A) v
          \<longleftrightarrow>
        pp_t_holds (pp_zf_truth False) v"
      using pp_t_prop_eqv_at[OF lift_false wv] .
    show "\<not> pp_t_holds
        (pp_t_persistent_settledness_lift A) v"
      using at_v by simp
  qed
  show False
  proof (cases "\<exists>v. prefix w v \<and> A v")
    case True
    then obtain v where wv: "prefix w v" and Av: "A v"
      by blast
    have "pp_t_holds (pp_t_persistent_settledness_lift A) v"
      using Av by simp
    then show False
      using all_false[OF wv] by blast
  next
    case False
    show False
    proof (cases "pp_t_holds pp_t_even_false_parity w")
      case True
      have "pp_t_holds
          (pp_t_persistent_settledness_lift A) w"
        using False True by simp
      then show False
        using all_false[of w] by simp
    next
      case False_parity: False
      have no_A_future:
          "\<not> (\<exists>v.
            prefix (w @ [False]) v \<and> A v)"
      proof
        assume "\<exists>v. prefix (w @ [False]) v \<and> A v"
        then obtain v where wF_v: "prefix (w @ [False]) v"
          and Av: "A v"
          by blast
        have w_v: "prefix w v"
          using wF_v prefix_order.trans[of w "w @ [False]" v]
          by simp
        show False
          using False w_v Av by blast
      qed
      have parity:
          "pp_t_holds pp_t_even_false_parity (w @ [False])"
        using False_parity pp_t_even_false_parity_toggles by blast
      have lift:
          "pp_t_holds
            (pp_t_persistent_settledness_lift A)
            (w @ [False])"
        using no_A_future parity by simp
      have future: "prefix w (w @ [False])"
        by simp
      have not_lift:
          "\<not> pp_t_holds
            (pp_t_persistent_settledness_lift A)
            (w @ [False])"
        by (rule all_false[OF future])
      show False
        using not_lift lift by blast
    qed
  qed
qed

theorem pp_t_persistent_settledness_lift_exact:
  assumes persistent:
    "\<And>w v. prefix w v \<Longrightarrow> A w \<Longrightarrow> A v"
  shows
    "(pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth True)
      \<or>
      pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth False))
      \<longleftrightarrow>
    A w"
proof -
  have truth_iff:
      "pp_t_eqv Prop w
          (pp_t_persistent_settledness_lift A)
          (pp_zf_truth True)
        \<longleftrightarrow>
      A w"
  proof (rule pp_t_persistent_settledness_lift_eqv_truth)
    fix u v
    assume uv: "prefix u v" and Au: "A u"
    show "A v"
      by (rule persistent[OF uv Au])
  qed
  show ?thesis
  proof (cases "A w")
  case True
  have true_eqv:
      "pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth True)"
    using truth_iff True by blast
  then show ?thesis
    using True by blast
next
  case False
  have not_true:
      "\<not> pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth True)"
    using truth_iff False by blast
  have not_false:
      "\<not> pp_t_eqv Prop w
        (pp_t_persistent_settledness_lift A)
        (pp_zf_truth False)"
  proof (rule pp_t_persistent_settledness_lift_not_eqv_false)
    fix u v
    assume uv: "prefix u v" and Au: "A u"
    show "A v"
      by (rule persistent[OF uv Au])
  next
    show "\<not> A w"
      by (rule False)
  qed
  show ?thesis
    using False not_true not_false by blast
qed
qed

section \<open>A settledness realizer for each singleton family\<close>

definition pp_t_singleton_settledness_realizer :: "ZF \<Rightarrow> ZF"
where
  "pp_t_singleton_settledness_realizer r =
    Lambda (pp_t_domain Prop)
      (\<lambda>q.
        pp_t_persistent_settledness_lift
          (\<lambda>w. pp_t_eqv Prop w q r))"

lemma pp_t_singleton_settledness_realizer_in_domain:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "Elem (pp_t_singleton_settledness_realizer r)
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_singleton_settledness_realizer_def
proof (rule pp_t_lambda_closed)
  fix q
  assume "Elem q (pp_t_domain Prop)"
  show "Elem
      (pp_t_persistent_settledness_lift
        (\<lambda>w. pp_t_eqv Prop w q r))
      (pp_t_domain Prop)"
    by (rule pp_t_persistent_settledness_lift_in_domain)
next
  fix w q q'
  assume q: "Elem q (pp_t_domain Prop)"
    and q': "Elem q' (pp_t_domain Prop)"
    and qq': "pp_t_eqv Prop w q q'"
  show "pp_t_eqv Prop w
      (pp_t_persistent_settledness_lift
        (\<lambda>v. pp_t_eqv Prop v q r))
      (pp_t_persistent_settledness_lift
        (\<lambda>v. pp_t_eqv Prop v q' r))"
    unfolding pp_t_persistent_settledness_lift_def
      pp_t_prop_eqv_pp_t_prop_iff
  proof (intro allI impI)
    fix v
    assume wv: "prefix w v"
    have qq'_v: "pp_t_eqv Prop v q q'"
      by (rule pp_t_eqv_persistent[OF qq' wv])
    have at_v:
        "pp_t_eqv Prop v q r =
          pp_t_eqv Prop v q' r"
      using pp_t_eqv_congruence[
        OF q q' r r qq'_v pp_t_eqv_reflexive[OF r]] .
    have at_future:
        "\<And>u. prefix v u \<Longrightarrow>
          pp_t_eqv Prop u q r =
            pp_t_eqv Prop u q' r"
    proof -
      fix u
      assume vu: "prefix v u"
      have qq'_u: "pp_t_eqv Prop u q q'"
        by (rule pp_t_eqv_persistent[OF qq'_v vu])
      show "pp_t_eqv Prop u q r =
          pp_t_eqv Prop u q' r"
        using pp_t_eqv_congruence[
          OF q q' r r qq'_u pp_t_eqv_reflexive[OF r]] .
    qed
    show "(pp_t_eqv Prop v q r
          \<or> (\<not> (\<exists>u.
              prefix v u \<and> pp_t_eqv Prop u q r)
            \<and> pp_t_holds pp_t_even_false_parity v))
        =
        (pp_t_eqv Prop v q' r
          \<or> (\<not> (\<exists>u.
              prefix v u \<and> pp_t_eqv Prop u q' r)
            \<and> pp_t_holds pp_t_even_false_parity v))"
      using at_v at_future by metis
  qed
qed

lemma pp_t_singleton_settledness_realizer_apply:
  assumes q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_singleton_settledness_realizer r \<acute> q =
    pp_t_persistent_settledness_lift
      (\<lambda>w. pp_t_eqv Prop w q r)"
  using q
  by (simp add:
    pp_t_singleton_settledness_realizer_def Lambda_app)

theorem pp_t_singleton_settledness_realizer_exact:
  assumes r: "Elem r (pp_t_domain Prop)"
    and q: "Elem q (pp_t_domain Prop)"
  shows
    "(pp_t_eqv Prop w
        (pp_t_singleton_settledness_realizer r \<acute> q)
        (pp_zf_truth True)
      \<or>
      pp_t_eqv Prop w
        (pp_t_singleton_settledness_realizer r \<acute> q)
        (pp_zf_truth False))
      \<longleftrightarrow>
    pp_t_eqv Prop w q r"
  unfolding pp_t_singleton_settledness_realizer_apply[OF q]
proof (rule pp_t_persistent_settledness_lift_exact)
  fix u v
  assume uv: "prefix u v"
    and qr: "pp_t_eqv Prop u q r"
  show "pp_t_eqv Prop v q r"
    by (rule pp_t_eqv_persistent[OF qr uv])
qed

theorem pp_t_operator_indexed_probe_realizes_singleton:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows
    "pp_t_indexed_family_probe_for_stock
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder
        \<acute> pp_t_singleton_settledness_realizer r
      =
    pp_t_singleton_family_at r"
proof (rule pp_t_unary_function_ext)
  let ?G = "pp_t_singleton_settledness_realizer r"
  have G: "Elem ?G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_settledness_realizer_in_domain[OF r])
  show "Elem
      (pp_t_indexed_family_probe_for_stock
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder \<acute> ?G)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_indexed_family_probe_section_in_domain[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible G])
  show "Elem (pp_t_singleton_family_at r)
      (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_family_at_in_domain[OF r])
  fix q
  assume q: "Elem q (pp_t_domain Prop)"
  show "(pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder \<acute> ?G)
          \<acute> q
      =
      pp_t_singleton_family_at r \<acute> q"
  proof (rule pp_t_prop_ext)
    show "Elem
        ((pp_t_indexed_family_probe_for_stock
            pp_t_one_context_unary_type
            (pp_t_closed_logical_stock pp_t_one_context_unary_type)
            pp_t_operator_indexed_singleton_family_builder \<acute> ?G)
          \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_indexed_family_probe_section_in_domain[
          OF pp_t_operator_indexed_singleton_terms_typed(1)
            pp_t_closed_logical_stock_admissible G]
        q] .
    show "Elem (pp_t_singleton_family_at r \<acute> q)
        (pp_t_domain Prop)"
      using pp_t_app_closed[
        OF pp_t_singleton_family_at_in_domain[OF r] q] .
    fix w
    have probe:
        "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock
              pp_t_one_context_unary_type
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_operator_indexed_singleton_family_builder \<acute> ?G)
            \<acute> q) w
        \<longleftrightarrow>
        (pp_t_eqv Prop w (?G \<acute> q) (pp_zf_truth True)
          \<or> pp_t_eqv Prop w (?G \<acute> q) (pp_zf_truth False))"
      by (rule
        pp_t_operator_indexed_singleton_probe_apply_holds[OF G q])
    have realized:
        "(pp_t_eqv Prop w (?G \<acute> q) (pp_zf_truth True)
          \<or> pp_t_eqv Prop w (?G \<acute> q) (pp_zf_truth False))
        \<longleftrightarrow>
        pp_t_eqv Prop w q r"
      by (rule pp_t_singleton_settledness_realizer_exact[OF r q])
    have singleton:
        "pp_t_holds (pp_t_singleton_family_at r \<acute> q) w
          \<longleftrightarrow>
        pp_t_eqv Prop w q r"
      by (rule pp_t_singleton_family_at_apply_holds[OF r q])
    show "pp_t_holds
          ((pp_t_indexed_family_probe_for_stock
              pp_t_one_context_unary_type
              (pp_t_closed_logical_stock pp_t_one_context_unary_type)
              pp_t_operator_indexed_singleton_family_builder \<acute> ?G)
            \<acute> q) w
        \<longleftrightarrow>
        pp_t_holds (pp_t_singleton_family_at r \<acute> q) w"
      using probe realized singleton by blast
  qed
qed

section \<open>Recombination excludes the canonical realizer from purity\<close>

definition pp_t_flip_at_world :: "ZF \<Rightarrow> bool list \<Rightarrow> ZF"
where
  "pp_t_flip_at_world r w =
    pp_t_prop
      (\<lambda>v. if v = w then \<not> pp_t_holds r v else pp_t_holds r v)"

lemma pp_t_flip_at_world_in_domain:
  "Elem (pp_t_flip_at_world r w) (pp_t_domain Prop)"
  unfolding pp_t_flip_at_world_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_flip_at_world_differs:
  "pp_t_holds (pp_t_flip_at_world r w) w
    \<longleftrightarrow>
    \<not> pp_t_holds r w"
  by (simp add: pp_t_flip_at_world_def)

lemma pp_t_flip_at_world_recovers_on_child:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "pp_t_eqv Prop (w @ [True])
    (pp_t_flip_at_world r w) r"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume child_v: "prefix (w @ [True]) v"
  have "v \<noteq> w"
    using child_v
    by (auto simp: prefix_def)
  then show "pp_t_holds (pp_t_flip_at_world r w) v =
      pp_t_holds r v"
    by (simp add: pp_t_flip_at_world_def)
qed

lemma pp_t_flip_at_world_not_equivalent_at_world:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "\<not> pp_t_eqv Prop w
    (pp_t_flip_at_world r w) r"
proof
  assume equivalent:
      "pp_t_eqv Prop w (pp_t_flip_at_world r w) r"
  have at_w:
      "pp_t_holds (pp_t_flip_at_world r w) w
        \<longleftrightarrow>
      pp_t_holds r w"
    by (rule pp_t_prop_eqv_at[OF equivalent], simp)
  show False
    using at_w pp_t_flip_at_world_differs[of r w] by blast
qed

lemma pp_t_singleton_settledness_realizer_necessary_at_parameter:
  assumes r: "Elem r (pp_t_domain Prop)"
    and future: "prefix w v"
  shows "pp_t_holds
    (pp_t_singleton_settledness_realizer r \<acute> r) v"
  unfolding pp_t_singleton_settledness_realizer_apply[OF r]
  using pp_t_eqv_reflexive[OF r, of v]
  by simp

lemma pp_t_singleton_settledness_realizer_fails_on_world_flip:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "\<not> pp_t_holds
    (pp_t_singleton_settledness_realizer r
      \<acute> pp_t_flip_at_world r w) w"
proof -
  let ?q = "pp_t_flip_at_world r w"
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have not_equivalent: "\<not> pp_t_eqv Prop w ?q r"
    by (rule pp_t_flip_at_world_not_equivalent_at_world[OF r])
  have possible:
      "\<exists>v. prefix w v \<and> pp_t_eqv Prop v ?q r"
    using pp_t_flip_at_world_recovers_on_child[OF r, of w]
    by (intro exI[of _ "w @ [True]"]) simp
  show ?thesis
    unfolding pp_t_singleton_settledness_realizer_apply[OF q]
    using not_equivalent possible by simp
qed

theorem pp_t_recombination_excludes_singleton_settledness_realizer:
  assumes r: "Elem r (pp_t_domain Prop)"
    and recombines: "pp_t_unary_recombines_at Pure r w"
  shows "\<not> Pure w (pp_t_singleton_settledness_realizer r)"
proof
  let ?G = "pp_t_singleton_settledness_realizer r"
  let ?q = "pp_t_flip_at_world r w"
  assume G_pure: "Pure w ?G"
  have G: "Elem ?G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_settledness_realizer_in_domain[OF r])
  have necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_t_holds (?G \<acute> r) v"
    using
      pp_t_singleton_settledness_realizer_necessary_at_parameter[OF r]
    by blast
  have all:
      "\<forall>q. Elem q (pp_t_domain Prop)
        \<longrightarrow> pp_t_holds (?G \<acute> q) w"
    using recombines G G_pure necessary
    unfolding pp_t_unary_recombines_at_def
    by blast
  have q: "Elem ?q (pp_t_domain Prop)"
    by (rule pp_t_flip_at_world_in_domain)
  have Gq: "pp_t_holds (?G \<acute> ?q) w"
    using all q by blast
  show False
    using Gq
      pp_t_singleton_settledness_realizer_fails_on_world_flip[OF r]
    by blast
qed

section \<open>The first operator-indexed stabilization failure\<close>

lemma pp_t_even_false_parity_is_unsettled:
  "\<not> (pp_t_eqv Prop w
      pp_t_even_false_parity (pp_zf_truth True)
    \<or>
    pp_t_eqv Prop w
      pp_t_even_false_parity (pp_zf_truth False))"
proof
  assume settled:
      "pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth True)
        \<or>
       pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth False)"
  have ww: "prefix w w"
    by simp
  have wF: "prefix w (w @ [False])"
    by simp
  show False
  proof (cases "pp_t_holds pp_t_even_false_parity w")
    case True
    have not_future:
        "\<not> pp_t_holds pp_t_even_false_parity (w @ [False])"
      using True pp_t_even_false_parity_toggles by blast
    have not_true_eqv:
        "\<not> pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth True)"
    proof
      assume eqv:
          "pp_t_eqv Prop w
            pp_t_even_false_parity (pp_zf_truth True)"
      have at_future:
          "pp_t_holds pp_t_even_false_parity (w @ [False])
            \<longleftrightarrow>
          pp_t_holds (pp_zf_truth True) (w @ [False])"
        by (rule pp_t_prop_eqv_at[OF eqv wF])
      show False
        using at_future not_future by simp
    qed
    have not_false_eqv:
        "\<not> pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth False)"
    proof
      assume eqv:
          "pp_t_eqv Prop w
            pp_t_even_false_parity (pp_zf_truth False)"
      have at_w:
          "pp_t_holds pp_t_even_false_parity w
            \<longleftrightarrow>
          pp_t_holds (pp_zf_truth False) w"
        by (rule pp_t_prop_eqv_at[OF eqv ww])
      show False
        using at_w True by simp
    qed
    show False
      using settled not_true_eqv not_false_eqv by blast
  next
    case False
    have future:
        "pp_t_holds pp_t_even_false_parity (w @ [False])"
      using False pp_t_even_false_parity_toggles by blast
    have not_true_eqv:
        "\<not> pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth True)"
    proof
      assume eqv:
          "pp_t_eqv Prop w
            pp_t_even_false_parity (pp_zf_truth True)"
      have at_w:
          "pp_t_holds pp_t_even_false_parity w
            \<longleftrightarrow>
          pp_t_holds (pp_zf_truth True) w"
        by (rule pp_t_prop_eqv_at[OF eqv ww])
      show False
        using at_w False by simp
    qed
    have not_false_eqv:
        "\<not> pp_t_eqv Prop w
          pp_t_even_false_parity (pp_zf_truth False)"
    proof
      assume eqv:
          "pp_t_eqv Prop w
            pp_t_even_false_parity (pp_zf_truth False)"
      have at_future:
          "pp_t_holds pp_t_even_false_parity (w @ [False])
            \<longleftrightarrow>
          pp_t_holds (pp_zf_truth False) (w @ [False])"
        by (rule pp_t_prop_eqv_at[OF eqv wF])
      show False
        using at_future future by simp
    qed
    show False
      using settled not_true_eqv not_false_eqv by blast
  qed
qed

lemma pp_t_parity_singleton_not_in_closed_stock:
  "\<not> pp_t_closed_logical_stock
    pp_t_one_context_unary_type w
    (pp_t_singleton_family_at pp_t_even_false_parity)"
  using pp_t_singleton_family_in_closed_stock_iff_settled[
      OF pp_t_even_false_parity_in_domain, of w]
    pp_t_even_false_parity_is_unsettled[of w]
  by blast

definition pp_t_operator_collision_identity :: ZF where
  "pp_t_operator_collision_identity =
    Lambda (pp_t_domain Prop) (\<lambda>p. p)"

lemma pp_t_operator_collision_identity_in_domain:
  "Elem pp_t_operator_collision_identity
    (pp_t_domain pp_t_one_context_unary_type)"
  unfolding pp_t_operator_collision_identity_def
  by (rule pp_t_lambda_closed) simp_all

lemma pp_t_operator_collision_identity_apply:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_operator_collision_identity \<acute> p = p"
  using p
  by (simp add: pp_t_operator_collision_identity_def Lambda_app)

theorem
  pp_t_operator_indexed_singleton_probe_does_not_stabilize_after_all_sections_adjoined:
  "pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_indexed_family_section_stock_enlargement
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder)
      pp_t_operator_indexed_singleton_family_builder
    \<noteq>
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder"
proof
  let ?B = "pp_t_operator_indexed_singleton_family_builder"
  let ?S = "pp_t_closed_logical_stock pp_t_one_context_unary_type"
  let ?r = "pp_t_even_false_parity"
  let ?a = "pp_t_operator_collision_identity"
  let ?b = "pp_t_singleton_settledness_realizer ?r"
  assume stable:
      "pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type
          (pp_t_indexed_family_section_stock_enlargement
            pp_t_one_context_unary_type ?S ?B) ?B
        =
       pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type ?S ?B"
  have criterion:
      "\<forall>a p w.
        Elem a (pp_t_domain pp_t_one_context_unary_type)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>b.
          Elem b (pp_t_domain pp_t_one_context_unary_type)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock
              pp_t_one_context_unary_type ?S ?B \<acute> b)
            ((pp_t_closed_den ?B \<acute> a) \<acute> p))
        \<longrightarrow>
        ?S w ((pp_t_closed_den ?B \<acute> a) \<acute> p)"
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        pp_t_closed_logical_stock_admissible]
      stable
    by (rule iffD1)
  have a: "Elem ?a (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_operator_collision_identity_in_domain)
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_even_false_parity_in_domain)
  have b: "Elem ?b (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_settledness_realizer_in_domain[OF r])
  have target:
      "(pp_t_closed_den ?B \<acute> ?a) \<acute> ?r
        = pp_t_singleton_family_at ?r"
    unfolding pp_t_operator_indexed_singleton_family_value[OF a r]
    by (simp add: pp_t_operator_collision_identity_apply[OF r])
  have probe:
      "pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type ?S ?B \<acute> ?b
        = pp_t_singleton_family_at ?r"
    by (rule pp_t_operator_indexed_probe_realizes_singleton[OF r])
  have collision:
      "pp_t_eqv pp_t_one_context_unary_type []
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type ?S ?B \<acute> ?b)
        ((pp_t_closed_den ?B \<acute> ?a) \<acute> ?r)"
    unfolding probe target
    by (rule pp_t_eqv_reflexive[
      OF pp_t_singleton_family_at_in_domain[OF r]])
  have target_in_stock:
      "?S [] ((pp_t_closed_den ?B \<acute> ?a) \<acute> ?r)"
    using criterion a r b collision by blast
  show False
    using target_in_stock pp_t_parity_singleton_not_in_closed_stock[of "[]"]
    unfolding target by blast
qed

section \<open>Two-stage stabilization of the operator-indexed component\<close>

lemma
  pp_t_operator_indexed_family_value_in_first_probe_section_enlargement:
  assumes F: "Elem F (pp_t_domain pp_t_one_context_unary_type)"
    and p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_indexed_family_section_stock_enlargement
      pp_t_one_context_unary_type
      (pp_t_closed_logical_stock pp_t_one_context_unary_type)
      pp_t_operator_indexed_singleton_family_builder
      w
      ((pp_t_closed_den
          pp_t_operator_indexed_singleton_family_builder \<acute> F) \<acute> p)"
proof -
  let ?S = "pp_t_closed_logical_stock pp_t_one_context_unary_type"
  let ?B = "pp_t_operator_indexed_singleton_family_builder"
  let ?r = "F \<acute> p"
  let ?G = "pp_t_singleton_settledness_realizer ?r"
  have r: "Elem ?r (pp_t_domain Prop)"
    by (rule pp_t_app_closed[OF F p])
  have G: "Elem ?G (pp_t_domain pp_t_one_context_unary_type)"
    by (rule pp_t_singleton_settledness_realizer_in_domain[OF r])
  have probe:
      "pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type ?S ?B \<acute> ?G
        = pp_t_singleton_family_at ?r"
    by (rule pp_t_operator_indexed_probe_realizes_singleton[OF r])
  have target:
      "(pp_t_closed_den ?B \<acute> F) \<acute> p
        = pp_t_singleton_family_at ?r"
    by (rule pp_t_operator_indexed_singleton_family_value[OF F p])
  have related:
      "pp_t_eqv pp_t_one_context_unary_type w
        (pp_t_indexed_family_probe_for_stock
          pp_t_one_context_unary_type ?S ?B \<acute> ?G)
        ((pp_t_closed_den ?B \<acute> F) \<acute> p)"
    unfolding probe target
    by (rule pp_t_eqv_reflexive[
      OF pp_t_singleton_family_at_in_domain[OF r]])
  show ?thesis
    unfolding pp_t_indexed_family_section_stock_enlargement_def
    using G related by blast
qed

theorem
  pp_t_operator_indexed_singleton_probe_stabilizes_at_second_stage:
  "pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_indexed_family_section_stock_enlargement
        pp_t_one_context_unary_type
        (pp_t_indexed_family_section_stock_enlargement
          pp_t_one_context_unary_type
          (pp_t_closed_logical_stock pp_t_one_context_unary_type)
          pp_t_operator_indexed_singleton_family_builder)
        pp_t_operator_indexed_singleton_family_builder)
      pp_t_operator_indexed_singleton_family_builder
    =
    pp_t_indexed_family_probe_for_stock
      pp_t_one_context_unary_type
      (pp_t_indexed_family_section_stock_enlargement
        pp_t_one_context_unary_type
        (pp_t_closed_logical_stock pp_t_one_context_unary_type)
        pp_t_operator_indexed_singleton_family_builder)
      pp_t_operator_indexed_singleton_family_builder"
proof -
  let ?B = "pp_t_operator_indexed_singleton_family_builder"
  let ?S0 = "pp_t_closed_logical_stock pp_t_one_context_unary_type"
  let ?S1 =
    "pp_t_indexed_family_section_stock_enlargement
      pp_t_one_context_unary_type ?S0 ?B"
  have S1_admissible:
      "pp_t_predicate_admissible pp_t_one_context_unary_type ?S1"
    by (rule
      pp_t_indexed_family_section_stock_enlargement_admissible[
        OF pp_t_operator_indexed_singleton_terms_typed(1)
          pp_t_closed_logical_stock_admissible])
  have all_collisions:
      "\<forall>F p w.
        Elem F (pp_t_domain pp_t_one_context_unary_type)
        \<longrightarrow>
        Elem p (pp_t_domain Prop)
        \<longrightarrow>
        (\<exists>G.
          Elem G (pp_t_domain pp_t_one_context_unary_type)
          \<and> pp_t_eqv pp_t_one_context_unary_type w
            (pp_t_indexed_family_probe_for_stock
              pp_t_one_context_unary_type ?S1 ?B \<acute> G)
            ((pp_t_closed_den ?B \<acute> F) \<acute> p))
        \<longrightarrow>
        ?S1 w ((pp_t_closed_den ?B \<acute> F) \<acute> p)"
    using
      pp_t_operator_indexed_family_value_in_first_probe_section_enlargement
    by blast
  show ?thesis
    using pp_t_indexed_family_probe_stabilizes_iff_collisions_absorbed[
      OF pp_t_operator_indexed_singleton_terms_typed(1)
        S1_admissible]
      all_collisions
    by (rule iffD2)
qed

end
