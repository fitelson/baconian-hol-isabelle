theory Bacon_PP_ZF_Goodman_M7
  imports Bacon_PP_ZF_Goodman_M5_Rebuild
begin

section \<open>Goodman M7: failure of Fundamental Completeness\<close>

text \<open>
  Given a countable sequence of proposition denotations, we put above the
  nth reserved cone the complement of the nth denotation's own view there.
  The resulting proposition differs from the nth denotation at the root of
  that cone.  This is the direct Tarski diagonal described in M7.
\<close>

definition pp_t_M7_local_complement ::
    "bool list \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_t_M7_local_complement s P =
    pp_t_prop (\<lambda>u. \<not> pp_t_holds P (s @ u))"

lemma pp_t_M7_local_complement_typed:
  "Elem (pp_t_M7_local_complement s P) (pp_t_domain Prop)"
  unfolding pp_t_M7_local_complement_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_M7_local_complement_holds[simp]:
  "pp_t_holds (pp_t_M7_local_complement s P) u
    \<longleftrightarrow> \<not> pp_t_holds P (s @ u)"
  by (simp add: pp_t_M7_local_complement_def)

definition pp_t_M7_diagonal :: "(nat \<Rightarrow> ZF) \<Rightarrow> ZF"
where
  "pp_t_M7_diagonal a =
    pp_t_branch_glue Prop
      (\<lambda>n. pp_t_M7_local_complement (pp_b_code n) (a n))"

lemma pp_t_M7_diagonal_typed:
  "Elem (pp_t_M7_diagonal a) (pp_t_domain Prop)"
proof -
  have sequence:
      "pp_t_typed_sequence Prop
        (\<lambda>n. pp_t_M7_local_complement (pp_b_code n) (a n))"
    unfolding pp_t_typed_sequence_def
    using pp_t_M7_local_complement_typed by blast
  show ?thesis
    unfolding pp_t_M7_diagonal_def
    by (rule pp_t_branch_glue_in_domain[OF _ sequence])
      simp
qed

lemma pp_t_M7_diagonal_cone:
  "pp_t_cone_rel Prop (pp_b_code n)
    (pp_t_M7_diagonal a)
    (pp_t_M7_local_complement (pp_b_code n) (a n))"
proof -
  have sequence:
      "pp_t_typed_sequence Prop
        (\<lambda>m. pp_t_M7_local_complement (pp_b_code m) (a m))"
    unfolding pp_t_typed_sequence_def
    using pp_t_M7_local_complement_typed by blast
  show ?thesis
    unfolding pp_t_M7_diagonal_def
    by (rule pp_t_branch_glue_cone[OF _ sequence])
      simp
qed

theorem pp_t_M7_diagonal_truth:
  "pp_t_holds (pp_t_M7_diagonal a) (pp_b_code n @ u)
    \<longleftrightarrow>
    \<not> pp_t_holds (a n) (pp_b_code n @ u)"
proof -
  have cone:
      "pp_t_cone_rel Prop (pp_b_code n)
        (pp_t_M7_diagonal a)
        (pp_t_M7_local_complement (pp_b_code n) (a n))"
    by (rule pp_t_M7_diagonal_cone)
  show ?thesis
    using cone by simp
qed

theorem pp_t_M7_diagonal_differs:
  "pp_t_M7_diagonal a \<noteq> a n"
proof
  assume equality: "pp_t_M7_diagonal a = a n"
  have opposite:
      "pp_t_holds (pp_t_M7_diagonal a) (pp_b_code n)
        \<longleftrightarrow>
       \<not> pp_t_holds (a n) (pp_b_code n)"
    using pp_t_M7_diagonal_truth[of a n "[]"] by simp
  show False
    using equality opposite by simp
qed

corollary pp_t_M7_diagonal_outside_range:
  "pp_t_M7_diagonal a \<notin> range a"
  using pp_t_M7_diagonal_differs by blast

theorem pp_t_M7_typed_countable_set_has_diagonal:
  assumes countable: "countable S"
    and typed: "\<And>q. q \<in> S \<Longrightarrow>
      Elem q (pp_t_domain Prop)"
  shows "\<exists>q. Elem q (pp_t_domain Prop) \<and> q \<notin> S"
proof (cases "S = {}")
  case True
  show ?thesis
    using pp_t_default_in_domain[of Prop] True by blast
next
  case False
  let ?a = "from_nat_into S"
  have range: "range ?a = S"
    using False countable by (rule range_from_nat_into)
  have diagonal_typed:
      "Elem (pp_t_M7_diagonal ?a) (pp_t_domain Prop)"
    by (rule pp_t_M7_diagonal_typed)
  have outside: "pp_t_M7_diagonal ?a \<notin> S"
    using pp_t_M7_diagonal_outside_range[of ?a] range by simp
  show ?thesis
    using diagonal_typed outside by blast
qed

definition pp_t_M7_reachable_from ::
    "ZF \<Rightarrow> ZF set"
where
  "pp_t_M7_reachable_from r =
    (\<lambda>X. X \<acute> r) ` pp_t_exact_closed_logical_operators"

lemma pp_t_M7_reachable_countable:
  "countable (pp_t_M7_reachable_from r)"
  unfolding pp_t_M7_reachable_from_def
  using pp_t_exact_closed_logical_operators_countable
  by (rule countable_image)

lemma pp_t_M7_reachable_typed:
  assumes r: "Elem r (pp_t_domain Prop)"
    and q: "q \<in> pp_t_M7_reachable_from r"
  shows "Elem q (pp_t_domain Prop)"
proof -
  obtain X where
      X: "X \<in> pp_t_exact_closed_logical_operators"
    and q_def: "q = X \<acute> r"
    using q unfolding pp_t_M7_reachable_from_def by blast
  have X_typed:
      "Elem X (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    using pp_t_exact_closed_logical_operator_in_domain[OF X] .
  show ?thesis
    unfolding q_def
    using pp_t_app_closed[OF X_typed r] .
qed

theorem pp_t_M7_fundamental_completeness_fails:
  assumes r: "Elem r (pp_t_domain Prop)"
  shows "\<exists>q.
    Elem q (pp_t_domain Prop)
    \<and>
    (\<forall>X \<in> pp_t_exact_closed_logical_operators.
      q \<noteq> X \<acute> r)"
proof -
  have countable:
      "countable (pp_t_M7_reachable_from r)"
    by (rule pp_t_M7_reachable_countable)
  have typed:
      "\<And>q. q \<in> pp_t_M7_reachable_from r \<Longrightarrow>
        Elem q (pp_t_domain Prop)"
    by (rule pp_t_M7_reachable_typed[OF r])
  obtain q where q_typed: "Elem q (pp_t_domain Prop)"
    and outside: "q \<notin> pp_t_M7_reachable_from r"
    using pp_t_M7_typed_countable_set_has_diagonal[
      OF countable typed] by blast
  have unreachable:
      "\<forall>X \<in> pp_t_exact_closed_logical_operators.
        q \<noteq> X \<acute> r"
    using outside
    unfolding pp_t_M7_reachable_from_def by blast
  show ?thesis
    using q_typed unreachable by blast
qed

text \<open>
  Thus Fundamental Completeness already fails at proposition type: for every
  proposed fundamental proposition \<open>r\<close>, some proposition is not the value
  at \<open>r\<close> of any closed constant-free logical unary operator.  The witness
  is the explicit branch diagonal above, rather than a bare cardinality
  argument.
\<close>

end
