theory Bacon_PP_Goodman_M1_Fn60
  imports Bacon_PP_Goodman_M1_Complete
begin

section \<open>Goodman M1: the exact failure of the footnote-60 argument\<close>

text \<open>
  At the unary-operator type, the infinitary disjunction of the identity
  properties of the members of \<open>Stock\<close> is a property of unary operators.
  The following definition gives that join directly.  It has, at every
  world, exactly \<open>Stock\<close> as its extension.
\<close>

definition pp_M1_fn60_identity_property ::
    "('p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop"
where
  "pp_M1_fn60_identity_property Y X =
    (if X = Y then UNIV else {})"

definition pp_M1_fn60_identity_join ::
    "('p \<Rightarrow> 'p) set \<Rightarrow>
      ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop"
where
  "pp_M1_fn60_identity_join Stock X =
    (\<Union>Y \<in> Stock. pp_M1_fn60_identity_property Y X)"

lemma pp_M1_fn60_identity_join_at_world:
  "w \<in> pp_M1_fn60_identity_join Stock X
    \<longleftrightarrow> X \<in> Stock"
  by (auto simp: pp_M1_fn60_identity_join_def
      pp_M1_fn60_identity_property_def)

theorem pp_M1_fn60_identity_join_exact_extension:
  "{X. w \<in> pp_M1_fn60_identity_join Stock X} = Stock"
  by (auto simp: pp_M1_fn60_identity_join_at_world)

theorem pp_M1_fn60_identity_join_exists:
  "\<exists>C :: ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop.
    \<forall>w X. w \<in> C X \<longleftrightarrow> X \<in> Stock"
  using pp_M1_fn60_identity_join_at_world by blast

text \<open>
  Existence of this higher-type classifier is therefore harmless.  The
  footnote-60 inference needs the further claim that the classifier is itself
  pure.  The premise \<open>diagonal_from_PP\<close> records exactly what PP, Purity of
  Fun, the purity schema, and application closure then supply: a certified
  instance of the footnote-59 diagonal.  QSS excludes that certification.
\<close>

theorem pp_M1_fn60_identity_join_not_certified:
  fixes Stock :: "('p \<Rightarrow> 'p) set"
    and truth :: "'p \<Rightarrow> bool"
    and r :: 'p
  assumes qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and diagonal_from_PP:
      "(\<exists>C :: ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop.
          (\<forall>w X. w \<in> C X \<longleftrightarrow> X \<in> Stock)
          \<and> certified C)
        \<Longrightarrow>
        \<exists>D. D \<in> Stock
          \<and> (\<forall>p. truth (D p) =
            (\<forall>X \<in> Stock.
              p = X r \<longrightarrow> \<not> truth (X p)))"
  shows "\<not> certified (pp_M1_fn60_identity_join Stock)"
proof
  assume certified:
      "certified (pp_M1_fn60_identity_join Stock)"
  have classifier:
      "\<exists>C :: ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop.
        (\<forall>w X. w \<in> C X \<longleftrightarrow> X \<in> Stock)
        \<and> certified C"
    using certified pp_M1_fn60_identity_join_at_world by blast
  obtain D where D_stock: "D \<in> Stock"
    and diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. p = X r \<longrightarrow> \<not> truth (X p))"
    using diagonal_from_PP[OF classifier] by blast
  show False
    using D_stock qss diagonal
    by (rule pp_M1_fn59_diagonal_contradiction)
qed

corollary pp_M1_fn60_exact_diagnosis:
  fixes Stock :: "('p \<Rightarrow> 'p) set"
    and truth :: "'p \<Rightarrow> bool"
    and r :: 'p
  assumes qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and diagonal_from_PP:
      "(\<exists>C :: ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop.
          (\<forall>w X. w \<in> C X \<longleftrightarrow> X \<in> Stock)
          \<and> certified C)
        \<Longrightarrow>
        \<exists>D. D \<in> Stock
          \<and> (\<forall>p. truth (D p) =
            (\<forall>X \<in> Stock.
              p = X r \<longrightarrow> \<not> truth (X p)))"
  shows
    "(\<exists>C :: ('p \<Rightarrow> 'p) \<Rightarrow> pp_sem_prop.
        \<forall>w X. w \<in> C X \<longleftrightarrow> X \<in> Stock)
      \<and> \<not> certified (pp_M1_fn60_identity_join Stock)"
  using pp_M1_fn60_identity_join_exists
    pp_M1_fn60_identity_join_not_certified[
      OF qss diagonal_from_PP]
  by blast

end
