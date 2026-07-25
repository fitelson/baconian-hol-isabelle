theory Bacon_PP_Domain_Persistence
  imports Bacon_PP_Seed_Aware_Requirements
begin

section \<open>Persistence of quantified denotations along a chain of domains\<close>

text \<open>
  The stage-wise construction that the previous theories point to would build the
  Henkin domains as an increasing chain \<open>D\<^sub>0 \<subseteq> D\<^sub>1 \<subseteq> \<dots>\<close> with limit \<open>D\<^sub>\<omega>\<close>, and
  would need to know that a term's denotation settles down: that for each term there
  is a stage beyond which its value over \<open>D\<^sub>n\<close> already equals its value over
  \<open>D\<^sub>\<omega>\<close>.  That is the persistence theorem.

  This theory settles its status.  Persistence is \emph{false} as a general fact about
  increasing chains: the denotation of the single term \<open>\<forall>X : Prop. X\<close> can differ from
  its limit value at every finite stage.  So a stage-wise construction cannot simply
  assume it.

  Two things survive, and they are the right things to carry forward.  First, the
  limit value is always determined by the stage values, as their intersection for a
  universal quantifier and their union for an existential one; no hypothesis at all is
  needed for this.  Second, persistence does hold under a checkable hypothesis: if the
  quantified body takes only finitely many values over the limit domain, the
  denotation stabilizes.

  The variance lemmas below also make precise why the standard fixed-point theorems
  are unavailable here.  Universal quantification is antitone in the domain and
  existential quantification is monotone, so a term with alternating quantifiers has
  no uniform variance in the domain, and Knaster--Tarski has nothing to work with.
\<close>

subsection \<open>Quantification over a domain\<close>

definition pp_forall_over ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop"
  where
  "pp_forall_over D f = {i. \<forall>X \<in> D. i \<in> f X}"

definition pp_exists_over ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop"
  where
  "pp_exists_over D f = {i. \<exists>X \<in> D. i \<in> f X}"

lemma pp_forall_over_iff:
  "i \<in> pp_forall_over D f \<longleftrightarrow> (\<forall>X \<in> D. i \<in> f X)"
  by (simp add: pp_forall_over_def)

lemma pp_exists_over_iff:
  "i \<in> pp_exists_over D f \<longleftrightarrow> (\<exists>X \<in> D. i \<in> f X)"
  by (simp add: pp_exists_over_def)

lemma pp_forall_over_empty[simp]:
  "pp_forall_over {} f = UNIV"
  by (simp add: pp_forall_over_def)

subsection \<open>Variance in the domain\<close>

theorem pp_forall_over_antitone:
  assumes "D \<subseteq> E"
  shows "pp_forall_over E f \<subseteq> pp_forall_over D f"
  using assms by (auto simp: pp_forall_over_def)

theorem pp_exists_over_monotone:
  assumes "D \<subseteq> E"
  shows "pp_exists_over D f \<subseteq> pp_exists_over E f"
  using assms by (auto simp: pp_exists_over_def)

text \<open>
  The two variances are genuinely opposite, and both are realized.  So the map from a
  domain to the denotation of a term with alternating quantifiers is neither monotone
  nor antitone, which is exactly the obstruction to a Knaster--Tarski argument.
\<close>

subsection \<open>The limit value is determined by the stage values\<close>

theorem pp_forall_over_Union:
  "pp_forall_over (\<Union>n. D n) f = (\<Inter>n. pp_forall_over (D n) f)"
  by (auto simp: pp_forall_over_def)

theorem pp_exists_over_Union:
  "pp_exists_over (\<Union>n. D n) f = (\<Union>n. pp_exists_over (D n) f)"
  by (auto simp: pp_exists_over_def)

text \<open>
  Neither theorem needs the chain to be increasing.  They say that the limit
  denotation, while it need not equal any stage denotation, is always recoverable from
  the sequence of stage denotations.  That is the correct substitute for persistence
  in a fusion construction.
\<close>

subsection \<open>Persistence fails\<close>

definition pp_zeros :: "nat \<Rightarrow> pp_word" where
  "pp_zeros k = replicate k 0"

lemma pp_zeros_length[simp]:
  "length (pp_zeros k) = k"
  by (simp add: pp_zeros_def)

lemma pp_zeros_inj:
  "pp_zeros k = pp_zeros m \<Longrightarrow> k = m"
  by (metis pp_zeros_length)

definition pp_stage :: "nat \<Rightarrow> pp_sem_prop set" where
  "pp_stage n = (\<lambda>k. - {pp_zeros k}) ` {k. k < n}"

lemma pp_stage_increasing:
  "pp_stage n \<subseteq> pp_stage (Suc n)"
  by (auto simp: pp_stage_def)

lemma pp_stage_finite:
  "finite (pp_stage n)"
  by (simp add: pp_stage_def)

lemma pp_stage_Union:
  "(\<Union>n. pp_stage n) = range (\<lambda>k. - {pp_zeros k})"
  by (auto simp: pp_stage_def)

lemma pp_zeros_in_stage_value:
  "pp_zeros n \<in> pp_forall_over (pp_stage n) id"
proof (unfold pp_forall_over_iff, intro ballI)
  fix X
  assume "X \<in> pp_stage n"
  then obtain k where k: "k < n" and X: "X = - {pp_zeros k}"
    by (auto simp: pp_stage_def)
  have "pp_zeros n \<noteq> pp_zeros k"
    using k pp_zeros_inj by fastforce
  then show "pp_zeros n \<in> id X"
    using X by simp
qed

lemma pp_zeros_not_in_limit_value:
  "pp_zeros n \<notin> pp_forall_over (\<Union>m. pp_stage m) id"
proof
  assume mem: "pp_zeros n \<in> pp_forall_over (\<Union>m. pp_stage m) id"
  have all_stages: "\<forall>X \<in> (\<Union>m. pp_stage m). pp_zeros n \<in> id X"
    using mem by (simp add: pp_forall_over_iff)
  have witness: "- {pp_zeros n} \<in> (\<Union>m. pp_stage m)"
    by (simp add: pp_stage_Union)
  have "pp_zeros n \<in> id (- {pp_zeros n})"
    using all_stages witness by blast
  then show False by simp
qed

theorem pp_universal_denotation_does_not_persist:
  "(\<forall>n. pp_stage n \<subseteq> pp_stage (Suc n)) \<and>
   (\<forall>n. finite (pp_stage n)) \<and>
   (\<forall>n. pp_forall_over (pp_stage n) id \<noteq>
        pp_forall_over (\<Union>m. pp_stage m) id)"
proof (intro conjI allI)
  fix n
  show "pp_stage n \<subseteq> pp_stage (Suc n)"
    by (rule pp_stage_increasing)
next
  fix n
  show "finite (pp_stage n)"
    by (rule pp_stage_finite)
next
  fix n
  show "pp_forall_over (pp_stage n) id \<noteq>
      pp_forall_over (\<Union>m. pp_stage m) id"
    using pp_zeros_in_stage_value[of n]
      pp_zeros_not_in_limit_value[of n]
    by blast
qed

text \<open>
  So the term \<open>\<forall>X : Prop. X\<close> --- read semantically as \<open>pp_forall_over D id\<close> --- has a
  denotation that differs from its limit value at \emph{every} finite stage, along an
  increasing chain whose stages are even finite.  A stage-wise construction therefore
  cannot assume persistence; it has to earn it.
\<close>

subsection \<open>Persistence holds under a finite-image hypothesis\<close>

lemma pp_chain_mono:
  assumes step: "\<And>n. D n \<subseteq> D (Suc n)"
    and le: "k \<le> m"
  shows "D k \<subseteq> D m"
  using le
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "k \<le> m")
    case True
    then have "D k \<subseteq> D m" using Suc by simp
    then show ?thesis using step[of m] by blast
  next
    case False
    then have "k = Suc m" using Suc.prems by simp
    then show ?thesis by simp
  qed
qed

theorem pp_finite_image_persistence:
  fixes D :: "nat \<Rightarrow> pp_sem_prop set"
  assumes step: "\<And>n. D n \<subseteq> D (Suc n)"
    and finite_image: "finite (f ` (\<Union>n. D n))"
  shows "\<exists>N. \<forall>m \<ge> N.
    pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
proof -
  let ?U = "(\<Union>n. D n)"
  let ?F = "f ` ?U"
  have choose_witness: "\<exists>X. X \<in> ?U \<and> f X = v" if "v \<in> ?F" for v
    using that by blast
  obtain W where W: "\<And>v. v \<in> ?F \<Longrightarrow> W v \<in> ?U \<and> f (W v) = v"
    using choose_witness by metis
  have choose_stage: "\<exists>k. W v \<in> D k" if "v \<in> ?F" for v
    using W[OF that] by blast
  obtain nn where nn: "\<And>v. v \<in> ?F \<Longrightarrow> W v \<in> D (nn v)"
    using choose_stage by metis
  let ?N = "Max (insert 0 (nn ` ?F))"
  have finite_set: "finite (insert 0 (nn ` ?F))"
    using finite_image by simp
  have bound: "nn v \<le> ?N" if "v \<in> ?F" for v
    using finite_set that by (simp add: Max_ge)
  have stabilises:
      "pp_forall_over (D m) f = pp_forall_over ?U f" if m: "?N \<le> m" for m
  proof
    show "pp_forall_over (D m) f \<subseteq> pp_forall_over ?U f"
    proof
      fix i
      assume i: "i \<in> pp_forall_over (D m) f"
      show "i \<in> pp_forall_over ?U f"
      proof (unfold pp_forall_over_iff, intro ballI)
        fix X
        assume X: "X \<in> ?U"
        then have v: "f X \<in> ?F" by blast
        have "W (f X) \<in> D (nn (f X))"
          using nn[OF v] .
        moreover have "D (nn (f X)) \<subseteq> D m"
        proof (rule pp_chain_mono)
          fix n
          show "D n \<subseteq> D (Suc n)" by (rule step)
        next
          show "nn (f X) \<le> m"
            using bound[OF v] m by simp
        qed
        ultimately have "W (f X) \<in> D m" by blast
        then have "i \<in> f (W (f X))"
          using i by (simp add: pp_forall_over_iff)
        then show "i \<in> f X"
          using W[OF v] by simp
      qed
    qed
  next
    show "pp_forall_over ?U f \<subseteq> pp_forall_over (D m) f"
      by (rule pp_forall_over_antitone) blast
  qed
  show ?thesis
    using stabilises by blast
qed

subsection \<open>Persistence is exactly finite attainment\<close>

text \<open>
  For an increasing chain the stage values decrease, so eventual stabilization is the
  same thing as the limit value being reached at some single finite stage.  This turns
  persistence from a statement about tails into a concrete attainment question about
  one stage.
\<close>

theorem pp_persistence_iff_attained:
  fixes D :: "nat \<Rightarrow> pp_sem_prop set"
  assumes step: "\<And>n. D n \<subseteq> D (Suc n)"
  shows "(\<exists>N. \<forall>m. N \<le> m \<longrightarrow>
            pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f) \<longleftrightarrow>
         (\<exists>N. pp_forall_over (D N) f = pp_forall_over (\<Union>n. D n) f)"
proof
  assume "\<exists>N. \<forall>m. N \<le> m \<longrightarrow>
      pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
  then obtain N where N: "\<And>m. N \<le> m \<Longrightarrow>
      pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
    by blast
  have "pp_forall_over (D N) f = pp_forall_over (\<Union>n. D n) f"
    by (rule N) simp
  then show "\<exists>N. pp_forall_over (D N) f = pp_forall_over (\<Union>n. D n) f"
    by blast
next
  assume "\<exists>N. pp_forall_over (D N) f = pp_forall_over (\<Union>n. D n) f"
  then obtain N where N: "pp_forall_over (D N) f =
      pp_forall_over (\<Union>n. D n) f"
    by blast
  have "pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
    if m: "N \<le> m" for m
  proof
    have "D N \<subseteq> D m"
      using step m by (rule pp_chain_mono)
    then have "pp_forall_over (D m) f \<subseteq> pp_forall_over (D N) f"
      by (rule pp_forall_over_antitone)
    then show "pp_forall_over (D m) f \<subseteq> pp_forall_over (\<Union>n. D n) f"
      using N by simp
  next
    show "pp_forall_over (\<Union>n. D n) f \<subseteq> pp_forall_over (D m) f"
      by (rule pp_forall_over_antitone) blast
  qed
  then show "\<exists>N. \<forall>m. N \<le> m \<longrightarrow>
      pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
    by blast
qed

text \<open>
  The hypothesis is checkable and is exactly what the counterexample violates: there
  the body is the identity and takes infinitely many values over the limit domain.
  Read back into the construction, it says a quantified term persists as soon as the
  quantifier only ever sees finitely many distinct propositions in the body --- which
  is a condition on the term and the limit domain together, not on the chain.

  This is therefore the shape of the remaining obligation.  A fusion construction does
  not need full persistence; it needs, for each term of the countable syntax, either a
  finite-image bound of this kind or the intersection form of
  \<open>pp_forall_over_Union\<close>.  Establishing which terms of the Bacon--Dorr language admit
  such a bound is the next question, and it is a question about the language rather
  than about the witness.
\<close>

end
