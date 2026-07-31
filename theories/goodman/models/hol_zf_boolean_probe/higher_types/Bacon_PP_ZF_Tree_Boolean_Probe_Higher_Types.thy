theory Bacon_PP_ZF_Tree_Boolean_Probe_Higher_Types
  imports
    Higher_Order_Metaphysics_PP_ZF_Boolean_Probe_Successor.Bacon_PP_ZF_Tree_Boolean_Probe_Successor
begin

section \<open>Higher-type stocks forced by the Boolean cycle\<close>

abbreviation pp_t_boolean_probe_classifier_type :: otype where
  "pp_t_boolean_probe_classifier_type \<equiv>
    pp_t_boolean_probe_unary_type \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_boolean_probe_family_builder_type :: otype where
  "pp_t_boolean_probe_family_builder_type \<equiv>
    pp_t_boolean_probe_classifier_type
      \<rightarrow>\<^sub>o pp_t_boolean_probe_unary_type"

abbreviation pp_t_boolean_probe_negator_den :: ZF where
  "pp_t_boolean_probe_negator_den \<equiv>
    pp_t_closed_den pp_t_unary_output_negator"

definition pp_t_probe_successor_transformer_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_transformer_stock w f \<longleftrightarrow>
    Elem f (pp_t_domain pp_t_boolean_probe_transformer_type)
    \<and>
    (pp_t_eqv pp_t_boolean_probe_transformer_type w
        pp_t_boolean_probe_negator_den f
      \<or>
      (\<exists>X.
        pp_t_probe_successor_stock w X
        \<and>
        pp_t_eqv pp_t_boolean_probe_transformer_type w
          (pp_t_unary_output_conjunction_den \<acute> X) f))"

lemma pp_t_boolean_probe_negator_den_in_domain:
  "Elem pp_t_boolean_probe_negator_den
    (pp_t_domain pp_t_boolean_probe_transformer_type)"
  by (rule pp_t_closed_den_in_domain)
    (rule pp_t_unary_output_negator_typed)

lemma pp_t_probe_successor_conjunction_section_in_domain:
  assumes X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
  shows "Elem (pp_t_unary_output_conjunction_den \<acute> X)
    (pp_t_domain pp_t_boolean_probe_transformer_type)"
  by (rule pp_t_app_closed[
    OF pp_t_unary_output_conjunction_den_in_domain X])

lemma pp_t_probe_successor_transformer_stock_admissible:
  "pp_t_predicate_admissible
    pp_t_boolean_probe_transformer_type
    pp_t_probe_successor_transformer_stock"
proof (unfold pp_t_predicate_admissible_def, intro allI impI)
  fix w f g v
  assume f:
      "Elem f (pp_t_domain pp_t_boolean_probe_transformer_type)"
    and g:
      "Elem g (pp_t_domain pp_t_boolean_probe_transformer_type)"
    and fg:
      "pp_t_eqv pp_t_boolean_probe_transformer_type w f g"
    and wv: "prefix w v"
  have fgv:
      "pp_t_eqv pp_t_boolean_probe_transformer_type v f g"
    by (rule pp_t_eqv_persistent[OF fg wv])
  have gfv:
      "pp_t_eqv pp_t_boolean_probe_transformer_type v g f"
    by (rule pp_t_eqv_symmetric[OF f g fgv])
  show "pp_t_probe_successor_transformer_stock v f =
      pp_t_probe_successor_transformer_stock v g"
  proof
    assume stock_f:
        "pp_t_probe_successor_transformer_stock v f"
    then consider
        (negator)
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            pp_t_boolean_probe_negator_den f"
      | (conjunction) X where
          "pp_t_probe_successor_stock v X"
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            (pp_t_unary_output_conjunction_den \<acute> X) f"
      unfolding pp_t_probe_successor_transformer_stock_def
      by blast
    then show "pp_t_probe_successor_transformer_stock v g"
    proof cases
      case negator
      have related:
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            pp_t_boolean_probe_negator_den g"
        by (rule pp_t_eqv_transitive[
          OF pp_t_boolean_probe_negator_den_in_domain f g
            negator fgv])
      show ?thesis
        unfolding pp_t_probe_successor_transformer_stock_def
        using g related by blast
    next
      case (conjunction X)
      have X_domain:
          "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
        using conjunction(1)
        unfolding pp_t_probe_successor_stock_def by blast
      have section_domain:
          "Elem (pp_t_unary_output_conjunction_den \<acute> X)
            (pp_t_domain pp_t_boolean_probe_transformer_type)"
        by (rule
          pp_t_probe_successor_conjunction_section_in_domain[OF X_domain])
      have related:
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            (pp_t_unary_output_conjunction_den \<acute> X) g"
        by (rule pp_t_eqv_transitive[
          OF section_domain f g conjunction(2) fgv])
      show ?thesis
        unfolding pp_t_probe_successor_transformer_stock_def
        using g conjunction(1) related by blast
    qed
  next
    assume stock_g:
        "pp_t_probe_successor_transformer_stock v g"
    then consider
        (negator)
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            pp_t_boolean_probe_negator_den g"
      | (conjunction) X where
          "pp_t_probe_successor_stock v X"
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            (pp_t_unary_output_conjunction_den \<acute> X) g"
      unfolding pp_t_probe_successor_transformer_stock_def
      by blast
    then show "pp_t_probe_successor_transformer_stock v f"
    proof cases
      case negator
      have related:
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            pp_t_boolean_probe_negator_den f"
        by (rule pp_t_eqv_transitive[
          OF pp_t_boolean_probe_negator_den_in_domain g f
            negator gfv])
      show ?thesis
        unfolding pp_t_probe_successor_transformer_stock_def
        using f related by blast
    next
      case (conjunction X)
      have X_domain:
          "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
        using conjunction(1)
        unfolding pp_t_probe_successor_stock_def by blast
      have section_domain:
          "Elem (pp_t_unary_output_conjunction_den \<acute> X)
            (pp_t_domain pp_t_boolean_probe_transformer_type)"
        by (rule
          pp_t_probe_successor_conjunction_section_in_domain[OF X_domain])
      have related:
          "pp_t_eqv pp_t_boolean_probe_transformer_type v
            (pp_t_unary_output_conjunction_den \<acute> X) f"
        by (rule pp_t_eqv_transitive[
          OF section_domain g f conjunction(2) gfv])
      show ?thesis
        unfolding pp_t_probe_successor_transformer_stock_def
        using f conjunction(1) related by blast
    qed
  qed
qed

lemma pp_t_probe_successor_transformer_stock_negator:
  "pp_t_probe_successor_transformer_stock w
    pp_t_boolean_probe_negator_den"
  unfolding pp_t_probe_successor_transformer_stock_def
  using pp_t_boolean_probe_negator_den_in_domain
    pp_t_eqv_reflexive[
      OF pp_t_boolean_probe_negator_den_in_domain]
  by blast

lemma pp_t_probe_successor_transformer_stock_conjunction_section:
  assumes stock: "pp_t_probe_successor_stock w X"
  shows "pp_t_probe_successor_transformer_stock w
    (pp_t_unary_output_conjunction_den \<acute> X)"
proof -
  have X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    using stock
    unfolding pp_t_probe_successor_stock_def by blast
  have conjunction_section:
      "Elem (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule
      pp_t_probe_successor_conjunction_section_in_domain[OF X])
  show ?thesis
    unfolding pp_t_probe_successor_transformer_stock_def
    using stock conjunction_section
      pp_t_eqv_reflexive[OF conjunction_section]
    by blast
qed

theorem pp_t_probe_successor_transformer_application_absorbed:
  assumes f:
      "Elem f (pp_t_domain pp_t_boolean_probe_transformer_type)"
    and Y:
      "Elem Y (pp_t_domain pp_t_boolean_probe_unary_type)"
    and f_stock:
      "pp_t_probe_successor_transformer_stock w f"
    and Y_stock: "pp_t_probe_successor_stock w Y"
  shows "pp_t_probe_successor_stock w (f \<acute> Y)"
proof -
  from f_stock consider
      (negator)
        "pp_t_eqv pp_t_boolean_probe_transformer_type w
          pp_t_boolean_probe_negator_den f"
    | (conjunction) X where
        "pp_t_probe_successor_stock w X"
        "pp_t_eqv pp_t_boolean_probe_transformer_type w
          (pp_t_unary_output_conjunction_den \<acute> X) f"
    unfolding pp_t_probe_successor_transformer_stock_def
    by blast
  then show ?thesis
  proof cases
    case negator
    have base_stock:
        "pp_t_probe_successor_stock w
          (pp_t_boolean_probe_negator_den \<acute> Y)"
      by (rule
        pp_t_probe_successor_stock_output_negation_closed[OF Y_stock])
    have base_domain:
        "Elem (pp_t_boolean_probe_negator_den \<acute> Y)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_app_closed[
        OF pp_t_boolean_probe_negator_den_in_domain Y])
    have result_domain:
        "Elem (f \<acute> Y)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_app_closed[OF f Y])
    have related:
        "pp_t_eqv pp_t_boolean_probe_unary_type w
          (pp_t_boolean_probe_negator_den \<acute> Y)
          (f \<acute> Y)"
      by (rule pp_t_app_respects[
        OF negator Y Y pp_t_eqv_reflexive[OF Y]])
    show ?thesis
      using pp_t_probe_successor_stock_admissible
        base_domain result_domain related base_stock
      unfolding pp_t_predicate_admissible_def
      by (metis prefix_order.refl)
  next
    case (conjunction X)
    have X_domain:
        "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
      using conjunction(1)
      unfolding pp_t_probe_successor_stock_def by blast
    have conjunction_section_domain:
        "Elem (pp_t_unary_output_conjunction_den \<acute> X)
          (pp_t_domain pp_t_boolean_probe_transformer_type)"
      by (rule
        pp_t_probe_successor_conjunction_section_in_domain[OF X_domain])
    have base_stock:
        "pp_t_probe_successor_stock w
          ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)"
      by (rule
        pp_t_probe_successor_stock_output_conjunction_closed[
          OF conjunction(1) Y_stock])
    have base_domain:
        "Elem
          ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_app_closed[
        OF conjunction_section_domain Y])
    have result_domain:
        "Elem (f \<acute> Y)
          (pp_t_domain pp_t_boolean_probe_unary_type)"
      by (rule pp_t_app_closed[OF f Y])
    have related:
        "pp_t_eqv pp_t_boolean_probe_unary_type w
          ((pp_t_unary_output_conjunction_den \<acute> X) \<acute> Y)
          (f \<acute> Y)"
      by (rule pp_t_app_respects[
        OF conjunction(2) Y Y pp_t_eqv_reflexive[OF Y]])
    show ?thesis
      using pp_t_probe_successor_stock_admissible
        base_domain result_domain related base_stock
      unfolding pp_t_predicate_admissible_def
      by (metis prefix_order.refl)
  qed
qed

definition pp_t_probe_successor_classifier :: ZF where
  "pp_t_probe_successor_classifier =
    pp_t_classifier pp_t_boolean_probe_unary_type
      pp_t_probe_successor_stock"

lemma pp_t_probe_successor_classifier_in_domain:
  "Elem pp_t_probe_successor_classifier
    (pp_t_domain pp_t_boolean_probe_classifier_type)"
  unfolding pp_t_probe_successor_classifier_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_probe_successor_stock_admissible)

definition pp_t_probe_successor_classifier_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_classifier_stock w c \<longleftrightarrow>
    pp_t_eqv pp_t_boolean_probe_classifier_type w
      pp_t_probe_successor_classifier c"

lemma pp_t_probe_successor_classifier_stock_admissible:
  "pp_t_predicate_admissible
    pp_t_boolean_probe_classifier_type
    pp_t_probe_successor_classifier_stock"
  unfolding pp_t_probe_successor_classifier_stock_def
  by (rule pp_t_eqv_class_predicate_admissible[
    OF pp_t_probe_successor_classifier_in_domain])

lemma pp_t_probe_successor_classifier_in_stock:
  "pp_t_probe_successor_classifier_stock w
    pp_t_probe_successor_classifier"
  unfolding pp_t_probe_successor_classifier_stock_def
  by (rule pp_t_eqv_reflexive[
    OF pp_t_probe_successor_classifier_in_domain])

definition pp_t_probe_successor_family_builder_den :: ZF where
  "pp_t_probe_successor_family_builder_den =
    pp_t_closed_den
      (pp_t_family_probe_builder
        pp_t_symmetrized_singleton_family_builder)"

lemma pp_t_probe_successor_family_builder_den_in_domain:
  "Elem pp_t_probe_successor_family_builder_den
    (pp_t_domain pp_t_boolean_probe_family_builder_type)"
  unfolding pp_t_probe_successor_family_builder_den_def
  by (rule pp_t_closed_den_in_domain)
    (rule pp_t_family_probe_builder_typed[
      OF pp_t_symmetrized_singleton_family_builder_typed])

definition pp_t_probe_successor_family_builder_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_family_builder_stock w b \<longleftrightarrow>
    pp_t_eqv pp_t_boolean_probe_family_builder_type w
      pp_t_probe_successor_family_builder_den b"

lemma pp_t_probe_successor_family_builder_stock_admissible:
  "pp_t_predicate_admissible
    pp_t_boolean_probe_family_builder_type
    pp_t_probe_successor_family_builder_stock"
  unfolding pp_t_probe_successor_family_builder_stock_def
  by (rule pp_t_eqv_class_predicate_admissible[
    OF pp_t_probe_successor_family_builder_den_in_domain])

lemma pp_t_probe_successor_family_builder_in_stock:
  "pp_t_probe_successor_family_builder_stock w
    pp_t_probe_successor_family_builder_den"
  unfolding pp_t_probe_successor_family_builder_stock_def
  by (rule pp_t_eqv_reflexive[
    OF pp_t_probe_successor_family_builder_den_in_domain])

lemma pp_t_probe_successor_family_builder_at_classifier:
  "pp_t_probe_successor_family_builder_den
      \<acute> pp_t_probe_successor_classifier
    =
    pp_t_probe_successor_family_probe"
  unfolding pp_t_probe_successor_family_builder_den_def
    pp_t_probe_successor_classifier_def
    pp_t_probe_successor_family_probe_def
    pp_t_family_probe_for_stock_def
  by simp

theorem pp_t_probe_successor_family_builder_application_absorbed:
  assumes b:
      "Elem b (pp_t_domain pp_t_boolean_probe_family_builder_type)"
    and c:
      "Elem c (pp_t_domain pp_t_boolean_probe_classifier_type)"
    and b_stock:
      "pp_t_probe_successor_family_builder_stock w b"
    and c_stock:
      "pp_t_probe_successor_classifier_stock w c"
  shows "pp_t_probe_successor_stock w (b \<acute> c)"
proof -
  have b_eqv:
      "pp_t_eqv pp_t_boolean_probe_family_builder_type w
        pp_t_probe_successor_family_builder_den b"
    using b_stock
    unfolding pp_t_probe_successor_family_builder_stock_def .
  have c_eqv:
      "pp_t_eqv pp_t_boolean_probe_classifier_type w
        pp_t_probe_successor_classifier c"
    using c_stock
    unfolding pp_t_probe_successor_classifier_stock_def .
  have related:
      "pp_t_eqv pp_t_boolean_probe_unary_type w
        (pp_t_probe_successor_family_builder_den
          \<acute> pp_t_probe_successor_classifier)
        (b \<acute> c)"
    by (rule pp_t_app_respects[
      OF b_eqv pp_t_probe_successor_classifier_in_domain c c_eqv])
  have base_stock:
      "pp_t_probe_successor_stock w
        (pp_t_probe_successor_family_builder_den
          \<acute> pp_t_probe_successor_classifier)"
    unfolding pp_t_probe_successor_family_builder_at_classifier
    by (rule pp_t_probe_successor_family_probe_in_stock)
  have base_domain:
      "Elem
        (pp_t_probe_successor_family_builder_den
          \<acute> pp_t_probe_successor_classifier)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[
      OF pp_t_probe_successor_family_builder_den_in_domain
        pp_t_probe_successor_classifier_in_domain])
  have result_domain:
      "Elem (b \<acute> c)
        (pp_t_domain pp_t_boolean_probe_unary_type)"
    by (rule pp_t_app_closed[OF b c])
  show ?thesis
    using pp_t_probe_successor_stock_admissible
      base_domain result_domain related base_stock
    unfolding pp_t_predicate_admissible_def
    by (metis prefix_order.refl)
qed

definition pp_t_probe_successor_conjunction_builder_stock ::
    "bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_conjunction_builder_stock w k \<longleftrightarrow>
    pp_t_eqv pp_t_boolean_probe_builder_type w
      pp_t_unary_output_conjunction_den k"

lemma pp_t_probe_successor_conjunction_builder_stock_admissible:
  "pp_t_predicate_admissible
    pp_t_boolean_probe_builder_type
    pp_t_probe_successor_conjunction_builder_stock"
  unfolding pp_t_probe_successor_conjunction_builder_stock_def
  by (rule pp_t_eqv_class_predicate_admissible[
    OF pp_t_unary_output_conjunction_den_in_domain])

lemma pp_t_probe_successor_conjunction_builder_in_stock:
  "pp_t_probe_successor_conjunction_builder_stock w
    pp_t_unary_output_conjunction_den"
  unfolding pp_t_probe_successor_conjunction_builder_stock_def
  by (rule pp_t_eqv_reflexive[
    OF pp_t_unary_output_conjunction_den_in_domain])

theorem
    pp_t_probe_successor_conjunction_builder_application_absorbed:
  assumes k:
      "Elem k (pp_t_domain pp_t_boolean_probe_builder_type)"
    and X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and k_stock:
      "pp_t_probe_successor_conjunction_builder_stock w k"
    and X_stock: "pp_t_probe_successor_stock w X"
  shows "pp_t_probe_successor_transformer_stock w (k \<acute> X)"
proof -
  have k_eqv:
      "pp_t_eqv pp_t_boolean_probe_builder_type w
        pp_t_unary_output_conjunction_den k"
    using k_stock
    unfolding pp_t_probe_successor_conjunction_builder_stock_def .
  have related:
      "pp_t_eqv pp_t_boolean_probe_transformer_type w
        (pp_t_unary_output_conjunction_den \<acute> X)
        (k \<acute> X)"
    by (rule pp_t_app_respects[
      OF k_eqv X X pp_t_eqv_reflexive[OF X]])
  have base_stock:
      "pp_t_probe_successor_transformer_stock w
        (pp_t_unary_output_conjunction_den \<acute> X)"
    by (rule
      pp_t_probe_successor_transformer_stock_conjunction_section[
        OF X_stock])
  have base_domain:
      "Elem (pp_t_unary_output_conjunction_den \<acute> X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule
      pp_t_probe_successor_conjunction_section_in_domain[OF X])
  have result_domain:
      "Elem (k \<acute> X)
        (pp_t_domain pp_t_boolean_probe_transformer_type)"
    by (rule pp_t_app_closed[OF k X])
  show ?thesis
    using pp_t_probe_successor_transformer_stock_admissible
      base_domain result_domain related base_stock
    unfolding pp_t_predicate_admissible_def
    by (metis prefix_order.refl)
qed

section \<open>The type-indexed pure interpretation\<close>

definition pp_t_probe_successor_model_pure ::
    "otype \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_probe_successor_model_pure \<sigma> w x \<longleftrightarrow>
    (if \<sigma> = pp_t_boolean_probe_unary_type
     then pp_t_probe_successor_stock w x
     else if \<sigma> = pp_t_boolean_probe_transformer_type
     then pp_t_probe_successor_transformer_stock w x
     else if \<sigma> = pp_t_boolean_probe_builder_type
     then pp_t_probe_successor_conjunction_builder_stock w x
     else if \<sigma> = pp_t_boolean_probe_classifier_type
     then pp_t_probe_successor_classifier_stock w x
     else if \<sigma> = pp_t_boolean_probe_family_builder_type
     then pp_t_probe_successor_family_builder_stock w x
     else False)"

lemma pp_t_probe_successor_model_pure_unary_function[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_unary_type
    =
    pp_t_probe_successor_stock"
  by (rule ext)+
    (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_transformer_function[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_transformer_type
    =
    pp_t_probe_successor_transformer_stock"
  by (rule ext)+
    (simp add: pp_t_probe_successor_model_pure_def)

lemma
    pp_t_probe_successor_model_pure_conjunction_builder_function[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_builder_type
    =
    pp_t_probe_successor_conjunction_builder_stock"
  by (rule ext)+
    (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_classifier_function[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_classifier_type
    =
    pp_t_probe_successor_classifier_stock"
  by (rule ext)+
    (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_family_builder_function[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_family_builder_type
    =
    pp_t_probe_successor_family_builder_stock"
  by (rule ext)+
    (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_admissible:
  "pp_t_predicate_admissible \<sigma>
    (pp_t_probe_successor_model_pure \<sigma>)"
proof (cases "\<sigma> = pp_t_boolean_probe_unary_type")
  case True
  then show ?thesis
    using pp_t_probe_successor_stock_admissible
    by simp
next
  case not_unary: False
  show ?thesis
  proof (cases "\<sigma> = pp_t_boolean_probe_transformer_type")
    case True
    then show ?thesis
      using pp_t_probe_successor_transformer_stock_admissible
        not_unary
      by simp
  next
    case not_transformer: False
    show ?thesis
    proof (cases "\<sigma> = pp_t_boolean_probe_builder_type")
      case True
      then show ?thesis
        using
          pp_t_probe_successor_conjunction_builder_stock_admissible
          not_unary not_transformer
        by simp
    next
      case not_builder: False
      show ?thesis
      proof (cases "\<sigma> = pp_t_boolean_probe_classifier_type")
        case True
        then show ?thesis
          using pp_t_probe_successor_classifier_stock_admissible
            not_unary not_transformer not_builder
          by simp
      next
        case not_classifier: False
        show ?thesis
        proof (cases
            "\<sigma> = pp_t_boolean_probe_family_builder_type")
          case True
          then show ?thesis
            using
              pp_t_probe_successor_family_builder_stock_admissible
              not_unary not_transformer not_builder not_classifier
            by simp
        next
          case False
          then show ?thesis
            using not_unary not_transformer not_builder
              not_classifier
            by (simp add: pp_t_probe_successor_model_pure_def
                pp_t_predicate_admissible_def)
        qed
      qed
    qed
  qed
qed

lemma pp_t_probe_successor_model_pure_unary[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_unary_type w x
    \<longleftrightarrow>
    pp_t_probe_successor_stock w x"
  by (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_transformer[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_transformer_type w x
    \<longleftrightarrow>
    pp_t_probe_successor_transformer_stock w x"
  by (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_conjunction_builder[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_builder_type w x
    \<longleftrightarrow>
    pp_t_probe_successor_conjunction_builder_stock w x"
  by (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_classifier[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_classifier_type w x
    \<longleftrightarrow>
    pp_t_probe_successor_classifier_stock w x"
  by (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_pure_family_builder[simp]:
  "pp_t_probe_successor_model_pure
      pp_t_boolean_probe_family_builder_type w x
    \<longleftrightarrow>
    pp_t_probe_successor_family_builder_stock w x"
  by (simp add: pp_t_probe_successor_model_pure_def)

lemma pp_t_probe_successor_model_unary_classifier:
  "pp_t_classifier pp_t_boolean_probe_unary_type
      (pp_t_probe_successor_model_pure
        pp_t_boolean_probe_unary_type)
    =
    pp_t_probe_successor_classifier"
  unfolding pp_t_probe_successor_classifier_def
    pp_t_probe_successor_model_pure_def
  by simp

lemma pp_t_probe_successor_model_classifier_is_pure:
  "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_classifier_type w
    pp_t_probe_successor_classifier"
  by (simp add: pp_t_probe_successor_classifier_in_stock)

theorem pp_t_probe_successor_model_family_application:
  assumes b:
      "Elem b (pp_t_domain pp_t_boolean_probe_family_builder_type)"
    and c:
      "Elem c (pp_t_domain pp_t_boolean_probe_classifier_type)"
    and pure_b:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_family_builder_type w b"
    and pure_c:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_classifier_type w c"
  shows "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_unary_type w (b \<acute> c)"
  using pp_t_probe_successor_family_builder_application_absorbed[
    OF b c] pure_b pure_c
  by simp

theorem pp_t_probe_successor_model_transformer_application:
  assumes f:
      "Elem f (pp_t_domain pp_t_boolean_probe_transformer_type)"
    and X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and pure_f:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_transformer_type w f"
    and pure_X:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_unary_type w X"
  shows "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_unary_type w (f \<acute> X)"
  using pp_t_probe_successor_transformer_application_absorbed[
    OF f X] pure_f pure_X
  by simp

theorem pp_t_probe_successor_model_builder_application:
  assumes k:
      "Elem k (pp_t_domain pp_t_boolean_probe_builder_type)"
    and X:
      "Elem X (pp_t_domain pp_t_boolean_probe_unary_type)"
    and pure_k:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_builder_type w k"
    and pure_X:
      "pp_t_probe_successor_model_pure
        pp_t_boolean_probe_unary_type w X"
  shows "pp_t_probe_successor_model_pure
    pp_t_boolean_probe_transformer_type w (k \<acute> X)"
  using
    pp_t_probe_successor_conjunction_builder_application_absorbed[
      OF k X] pure_k pure_X
  by simp

end
