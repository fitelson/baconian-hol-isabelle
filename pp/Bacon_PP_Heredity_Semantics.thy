theory Bacon_PP_Heredity_Semantics
  imports Bacon_PP_MSet
begin

section \<open>Semantic heredity of genericity in Bacon's substitution action\<close>

text \<open>
  Goodman's T3 says that a proposition which can play the fundamental role is
  \<open>fun\<acute>\<close>.  The object-language derivation from necessitated QSS and
  Persistence reaches only possible identity of the relevant pure operators.
  Bacon's substitution semantics nevertheless validates the heredity claim
  for a separate reason: denotations of closed pure operators are invariant
  elements of the function-space action.

  We isolate that reason without assuming that every invariant operator is
  pure.  A stock is an arbitrary collection of certified pure operators.
\<close>

definition pp_stock_fun_prime ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow> pp_sem_prop \<Rightarrow> bool"
  where
  "pp_stock_fun_prime Stock p \<longleftrightarrow>
    (\<forall>F \<in> Stock. \<forall>G \<in> Stock. F p = G p \<longrightarrow> F = G)"

definition pp_stock_necessitated_QSS ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set \<Rightarrow> pp_sem_prop \<Rightarrow> bool"
  where
  "pp_stock_necessitated_QSS Stock r \<longleftrightarrow>
    (\<forall>i. pp_stock_fun_prime Stock (pp_view i r))"

definition pp_possibly_plays_role ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool"
  where
  "pp_possibly_plays_role r p \<longleftrightarrow>
    (\<exists>i. pp_view i p = pp_view i r)"

lemma pp_stock_fun_primeI:
  assumes "\<And>F G.
      F \<in> Stock \<Longrightarrow>
      G \<in> Stock \<Longrightarrow>
      F p = G p \<Longrightarrow>
      F = G"
  shows "pp_stock_fun_prime Stock p"
  using assms unfolding pp_stock_fun_prime_def by blast

lemma pp_stock_fun_primeD:
  assumes "pp_stock_fun_prime Stock p"
    and "F \<in> Stock"
    and "G \<in> Stock"
    and "F p = G p"
  shows "F = G"
  using assms unfolding pp_stock_fun_prime_def by blast

theorem pp_stock_fun_prime_hereditary:
  assumes qss: "pp_stock_necessitated_QSS Stock r"
    and pure_member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and pure_invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
    and possible: "pp_possibly_plays_role r p"
  shows "pp_stock_fun_prime Stock p"
proof (rule pp_stock_fun_primeI)
  fix F G
  assume F_stock: "F \<in> Stock"
    and G_stock: "G \<in> Stock"
    and agree_p: "F p = G p"
  obtain i where role:
      "pp_view i p = pp_view i r"
    using possible unfolding pp_possibly_plays_role_def by blast
  have F_member: "pp_function_space_member F"
    using F_stock by (rule pure_member)
  have G_member: "pp_function_space_member G"
    using G_stock by (rule pure_member)
  have F_action:
      "pp_view i (F p) = F (pp_view i p)"
  proof -
    have viewed:
        "pp_fun_view i F (pp_view i p) = pp_view i (F p)"
      using F_member by (rule pp_fun_view_preimage_independent) simp
    have fixed: "pp_fun_view i F = F"
      using pure_invariant[OF F_stock]
      unfolding pp_fun_invariant_def by blast
    show ?thesis
      using viewed fixed by simp
  qed
  have G_action:
      "pp_view i (G p) = G (pp_view i p)"
  proof -
    have viewed:
        "pp_fun_view i G (pp_view i p) = pp_view i (G p)"
      using G_member by (rule pp_fun_view_preimage_independent) simp
    have fixed: "pp_fun_view i G = G"
      using pure_invariant[OF G_stock]
      unfolding pp_fun_invariant_def by blast
    show ?thesis
      using viewed fixed by simp
  qed
  have agree_view:
      "F (pp_view i r) = G (pp_view i r)"
  proof -
    have "F (pp_view i p) = pp_view i (F p)"
      using F_action by simp
    also have "... = pp_view i (G p)"
      using agree_p by simp
    also have "... = G (pp_view i p)"
      using G_action .
    finally show ?thesis
      using role by simp
  qed
  have qss_i:
      "pp_stock_fun_prime Stock (pp_view i r)"
    using qss unfolding pp_stock_necessitated_QSS_def by blast
  show "F = G"
    using qss_i F_stock G_stock agree_view
    by (rule pp_stock_fun_primeD)
qed

corollary pp_stock_fun_prime_hereditary_equivariant:
  assumes qss: "pp_stock_necessitated_QSS Stock r"
    and pure_equivariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_equivariant_operator F"
    and possible: "pp_possibly_plays_role r p"
  shows "pp_stock_fun_prime Stock p"
proof (rule pp_stock_fun_prime_hereditary[OF qss _ _ possible])
  fix F
  assume "F \<in> Stock"
  then show "pp_function_space_member F"
    using pure_equivariant pp_equivariant_operator_member by blast
next
  fix F
  assume "F \<in> Stock"
  then show "pp_fun_invariant F"
    using pure_equivariant pp_equivariant_operator_invariant by blast
qed

text \<open>
  The theorem identifies the semantic premise absent from the advertised
  object-language proof.  Persistence says that the predicate \<open>Pure\<close>
  continues to apply to a pure operator.  The argument above uses the stronger
  fact that the operator itself is fixed by every substitution.  That fact is
  true of closed logical denotations in Bacon's intended action semantics, but
  it is not the object-language Persistence axiom.
\<close>

end
