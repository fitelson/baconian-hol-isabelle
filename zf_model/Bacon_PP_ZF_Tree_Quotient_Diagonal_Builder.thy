theory Bacon_PP_ZF_Tree_Quotient_Diagonal_Builder
  imports
    Bacon_PP_ZF_Tree_Quotient_Diagonal
    Bacon_PP_ZF_Tree_Range_Term_Basis
begin

section \<open>A closed object-language quotient diagonal\<close>

abbreviation pp_t_qd_enum_type :: otype where
  "pp_t_qd_enum_type \<equiv> Ind \<rightarrow>\<^sub>o pp_t_unary_type"

abbreviation pp_t_qd_tag_type :: otype where
  "pp_t_qd_tag_type \<equiv> Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_qd_relation_type :: otype where
  "pp_t_qd_relation_type \<equiv>
    Prop \<rightarrow>\<^sub>o pp_t_unary_type
      \<rightarrow>\<^sub>o pp_t_unary_type \<rightarrow>\<^sub>o Prop"

abbreviation pp_t_qd_builder_type :: otype where
  "pp_t_qd_builder_type \<equiv>
    pp_t_qd_enum_type
      \<rightarrow>\<^sub>o pp_t_qd_tag_type
      \<rightarrow>\<^sub>o pp_t_qd_relation_type
      \<rightarrow>\<^sub>o pp_t_unary_type"

text \<open>
  The four outer abstractions bind, in order, the enumerator \<open>E\<close>, tag
  constructor \<open>H\<close>, relation \<open>R\<close>, and argument proposition \<open>q\<close>.
  The body says that every separated representation of \<open>q\<close> to whose
  representing operator all other representatives are related is false at
  \<open>q\<close>.
\<close>

definition pp_qd_builder :: oterm where
  "pp_qd_builder =
    Lam pp_t_qd_enum_type
      (Lam pp_t_qd_tag_type
        (Lam pp_t_qd_relation_type
          (Lam Prop
            (Forall Prop
              (Forall Ind
                (Imp
                  (Conj
                    (Conj
                      (Forall Ind
                        (Forall Ind
                          (Imp
                            (Neg
                              (Eq pp_t_unary_type
                                (App (Var 7) (Var 1))
                                (App (Var 7) (Var 0))))
                            (Neg
                              (Eq Prop
                                (App
                                  (App (Var 7) (Var 1))
                                  (Var 3))
                                (App
                                  (App (Var 7) (Var 0))
                                  (Var 3)))))))
                      (Eq Prop
                        (Var 2)
                        (App
                          (App (Var 4) (Var 1))
                          (App
                            (App (Var 5) (Var 0))
                            (Var 1)))))
                    (Forall Prop
                      (Forall Ind
                        (Imp
                          (Conj
                            (Forall Ind
                              (Forall Ind
                                (Imp
                                  (Neg
                                    (Eq pp_t_unary_type
                                      (App (Var 9) (Var 1))
                                      (App (Var 9) (Var 0))))
                                  (Neg
                                    (Eq Prop
                                      (App
                                        (App (Var 9) (Var 1))
                                        (Var 3))
                                      (App
                                        (App (Var 9) (Var 0))
                                        (Var 3)))))))
                            (Eq Prop
                              (Var 4)
                              (App
                                (App (Var 6) (Var 1))
                                (App
                                  (App (Var 7) (Var 0))
                                  (Var 1)))))
                          (App
                            (App
                              (App (Var 5) (Var 4))
                              (App (Var 7) (Var 0)))
                            (App (Var 7) (Var 2)))))))
                  (Neg
                    (App
                      (App (Var 5) (Var 0))
                      (Var 2)))))))))"

lemma pp_qd_builder_typed:
  "[] \<turnstile> pp_qd_builder : pp_t_qd_builder_type"
  unfolding pp_qd_builder_def
  by (intro has_type.Lam has_type.Forall has_type.Imp
      has_type.Conj has_type.Neg has_type.Eq
      has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma pp_qd_builder_logical:
  "pp_logical_vocabulary pp_qd_builder"
  unfolding pp_qd_builder_def pp_logical_vocabulary_def by simp

abbreviation pp_t_qd_den :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pp_t_qd_den E H R \<equiv>
    (((pp_t_closed_den pp_qd_builder) \<acute> E) \<acute> H) \<acute> R"

definition pp_t_qd_separator ::
    "ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_separator E w p \<longleftrightarrow>
    (\<forall>x y.
      Elem x (pp_t_domain Ind) \<longrightarrow>
      Elem y (pp_t_domain Ind) \<longrightarrow>
      (\<not> pp_t_eqv pp_t_unary_type w (E \<acute> x) (E \<acute> y)
        \<longrightarrow>
        \<not> pp_t_eqv Prop w
          ((E \<acute> x) \<acute> p) ((E \<acute> y) \<acute> p)))"

definition pp_t_qd_representation ::
    "ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow>
      ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_representation E H w q p x \<longleftrightarrow>
    pp_t_qd_separator E w p \<and>
    pp_t_eqv Prop w q ((H \<acute> p) \<acute> ((E \<acute> x) \<acute> p))"

definition pp_t_qd_related ::
    "ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_related R w q F G \<longleftrightarrow>
    pp_t_holds (((R \<acute> q) \<acute> F) \<acute> G) w"

definition pp_t_qd_schema ::
    "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_qd_schema E H R w q \<longleftrightarrow>
    (\<forall>p x.
      Elem p (pp_t_domain Prop) \<longrightarrow>
      Elem x (pp_t_domain Ind) \<longrightarrow>
      (pp_t_qd_representation E H w q p x \<and>
        (\<forall>r y.
          Elem r (pp_t_domain Prop) \<longrightarrow>
          Elem y (pp_t_domain Ind) \<longrightarrow>
          (pp_t_qd_representation E H w q r y
            \<longrightarrow>
            pp_t_qd_related R w q (E \<acute> y) (E \<acute> x))))
      \<longrightarrow> \<not> pp_t_holds ((E \<acute> x) \<acute> q) w)"

lemma pp_t_qd_den_in_domain:
  assumes E: "Elem E (pp_t_domain pp_t_qd_enum_type)"
    and H: "Elem H (pp_t_domain pp_t_qd_tag_type)"
    and R: "Elem R (pp_t_domain pp_t_qd_relation_type)"
  shows "Elem (pp_t_qd_den E H R) (pp_t_domain pp_t_unary_type)"
proof -
  have builder:
      "Elem (pp_t_closed_den pp_qd_builder)
        (pp_t_domain pp_t_qd_builder_type)"
    using pp_t_closed_den_in_domain[OF pp_qd_builder_typed] .
  have first:
      "Elem (pp_t_closed_den pp_qd_builder \<acute> E)
        (pp_t_domain
          (pp_t_qd_tag_type \<rightarrow>\<^sub>o
            pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_app_closed[OF builder E] .
  have second:
      "Elem ((pp_t_closed_den pp_qd_builder \<acute> E) \<acute> H)
        (pp_t_domain
          (pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type))"
    using pp_t_app_closed[OF first H] .
  show ?thesis
    using pp_t_app_closed[OF second R] .
qed

theorem pp_t_qd_builder_apply_holds:
  assumes E: "Elem E (pp_t_domain pp_t_qd_enum_type)"
    and H: "Elem H (pp_t_domain pp_t_qd_tag_type)"
    and R: "Elem R (pp_t_domain pp_t_qd_relation_type)"
    and q: "Elem q (pp_t_domain Prop)"
  shows "pp_t_holds ((pp_t_qd_den E H R) \<acute> q) w
    \<longleftrightarrow> pp_t_qd_schema E H R w q"
  unfolding pp_t_closed_den_def pp_qd_builder_def
    pp_t_qd_schema_def pp_t_qd_representation_def
    pp_t_qd_separator_def pp_t_qd_related_def
  using E H R q
  by (simp add: Lambda_app pp_t_default_constants_def
      pp_t_closed_env_def extend_env.simps pp_t_app_closed
      numeral_eq_Suc)

section \<open>Generated-stock membership\<close>

theorem pp_t_qd_den_in_enumerator_basis:
  assumes H:
      "H \<in> pp_t_enumerator_basis E pp_t_qd_tag_type"
    and R:
      "R \<in> pp_t_enumerator_basis E pp_t_qd_relation_type"
  shows "pp_t_qd_den E H R
    \<in> pp_t_enumerator_basis E pp_t_unary_type"
proof -
  have builder:
      "pp_t_closed_den pp_qd_builder
        \<in> pp_t_enumerator_basis E pp_t_qd_builder_type"
    using pp_t_enumerator_basis_contains_logical[
      OF pp_qd_builder_typed pp_qd_builder_logical] .
  have E_stock:
      "E \<in> pp_t_enumerator_basis E pp_t_qd_enum_type"
    by (rule pp_t_enumerator_basis_contains_enumerator)
  have first:
      "pp_t_closed_den pp_qd_builder \<acute> E
        \<in> pp_t_enumerator_basis E
          (pp_t_qd_tag_type \<rightarrow>\<^sub>o
            pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type)"
    using pp_t_enumerator_basis_application[OF builder E_stock] .
  have second:
      "(pp_t_closed_den pp_qd_builder \<acute> E) \<acute> H
        \<in> pp_t_enumerator_basis E
          (pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type)"
    using pp_t_enumerator_basis_application[OF first H] .
  show ?thesis
    using pp_t_enumerator_basis_application[OF second R] .
qed

context pp_t_cone_natural_enumerator
begin

theorem pp_t_qd_den_in_generated_stock:
  assumes H:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        pp_t_qd_tag_type [] H"
    and R:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        pp_t_qd_relation_type [] R"
  shows "pp_t_basis_stock (pp_t_enumerator_basis E)
    pp_t_unary_type [] (pp_t_qd_den E H R)"
proof -
  have builder:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        pp_t_qd_builder_type []
        (pp_t_closed_den pp_qd_builder)"
    using TermBasis.pp_t_basis_stock_contains_logical_den[
      OF pp_qd_builder_typed pp_qd_builder_logical] .
  have first:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        (pp_t_qd_tag_type \<rightarrow>\<^sub>o
          pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type) []
        (pp_t_closed_den pp_qd_builder \<acute> E)"
    using TermBasis.pp_t_basis_stock_application_closed[
      OF builder pp_t_enumerator_in_term_basis_stock] .
  have second:
      "pp_t_basis_stock (pp_t_enumerator_basis E)
        (pp_t_qd_relation_type \<rightarrow>\<^sub>o pp_t_unary_type) []
        ((pp_t_closed_den pp_qd_builder \<acute> E) \<acute> H)"
    using TermBasis.pp_t_basis_stock_application_closed[OF first H] .
  show ?thesis
    using TermBasis.pp_t_basis_stock_application_closed[OF second R] .
qed

end

end
