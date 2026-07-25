theory Bacon_PP_Attainment
  imports Bacon_PP_Domain_Persistence
begin

section \<open>Henkin closure chains and the finite-image bound\<close>

text \<open>
  \<open>Bacon_PP_Domain_Persistence\<close> shows that persistence fails along a general
  increasing chain, and holds when the quantified body has a finite image over the
  limit domain.  The question is then whether the chains that actually arise from
  Henkin closure over a seed admit such a bound.

  The answer has two halves.

  The finite-image bound itself is \emph{useless} here.  The simplest quantified term
  of all, \<open>\<forall>X : Prop. X\<close>, has the identity as its body, so its image over the limit
  domain is the limit domain, which is infinite in any nondegenerate model.  So no
  Henkin chain satisfies the hypothesis for that term.

  But finite image was never the right condition.  What the proof of
  \<open>pp_finite_image_persistence\<close> actually uses is that some \emph{finite} part of the
  domain already cuts the intersection down to its limit value.  That is attainment,
  and attainment is exactly what Henkin closure supplies, because comprehension puts
  the limit value itself into the domain.  In the identity case the limit value
  \<open>\<forall>X. X\<close> is a proposition, so it belongs to the domain at the quantified type, and
  the intersection is attained by that single element at whatever stage it enters.

  That also explains why the counterexample of the previous theory is not a Henkin
  chain: its limit value is provably not a member of its limit domain, so it is not
  closed under comprehension.  The counterexample refutes persistence for arbitrary
  chains, not for the chains we care about.
\<close>

subsection \<open>Attainment by a finite part of the domain\<close>

definition pp_finitely_attained ::
    "pp_sem_prop set \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool"
  where
  "pp_finitely_attained U f \<longleftrightarrow>
    (\<exists>S. S \<subseteq> U \<and> finite S \<and>
      pp_forall_over S f \<subseteq> pp_forall_over U f)"

theorem pp_finitely_attained_persistence:
  fixes D :: "nat \<Rightarrow> pp_sem_prop set"
  assumes step: "\<And>n. D n \<subseteq> D (Suc n)"
    and attained: "pp_finitely_attained (\<Union>n. D n) f"
  shows "\<exists>N. \<forall>m \<ge> N.
    pp_forall_over (D m) f = pp_forall_over (\<Union>n. D n) f"
proof -
  let ?U = "(\<Union>n. D n)"
  obtain S where S_sub: "S \<subseteq> ?U" and S_fin: "finite S"
    and S_cuts: "pp_forall_over S f \<subseteq> pp_forall_over ?U f"
    using attained unfolding pp_finitely_attained_def by blast
  have choose_stage: "\<exists>k. X \<in> D k" if "X \<in> S" for X
    using that S_sub by blast
  obtain kk where kk: "\<And>X. X \<in> S \<Longrightarrow> X \<in> D (kk X)"
    using choose_stage by metis
  let ?N = "Max (insert 0 (kk ` S))"
  have finite_set: "finite (insert 0 (kk ` S))"
    using S_fin by simp
  have bound: "kk X \<le> ?N" if "X \<in> S" for X
    using finite_set that by (simp add: Max_ge)
  have stabilises:
      "pp_forall_over (D m) f = pp_forall_over ?U f" if m: "?N \<le> m" for m
  proof
    have S_in: "S \<subseteq> D m"
    proof
      fix X
      assume X: "X \<in> S"
      have "D (kk X) \<subseteq> D m"
      proof (rule pp_chain_mono)
        fix n
        show "D n \<subseteq> D (Suc n)" by (rule step)
      next
        show "kk X \<le> m" using bound[OF X] m by simp
      qed
      then show "X \<in> D m" using kk[OF X] by blast
    qed
    have "pp_forall_over (D m) f \<subseteq> pp_forall_over S f"
      using S_in by (rule pp_forall_over_antitone)
    then show "pp_forall_over (D m) f \<subseteq> pp_forall_over ?U f"
      using S_cuts by blast
  next
    show "pp_forall_over ?U f \<subseteq> pp_forall_over (D m) f"
      by (rule pp_forall_over_antitone) blast
  qed
  show ?thesis
    using stabilises by blast
qed

subsection \<open>Finite image is a special case, and a weak one\<close>

theorem pp_finite_image_gives_attainment:
  assumes finite_image: "finite (f ` U)"
  shows "pp_finitely_attained U f"
proof -
  have choose_witness: "\<exists>X. X \<in> U \<and> f X = v" if "v \<in> f ` U" for v
    using that by blast
  obtain W where W: "\<And>v. v \<in> f ` U \<Longrightarrow> W v \<in> U \<and> f (W v) = v"
    using choose_witness by metis
  let ?S = "W ` (f ` U)"
  have S_sub: "?S \<subseteq> U"
    using W by blast
  have S_fin: "finite ?S"
    using finite_image by simp
  have "pp_forall_over ?S f \<subseteq> pp_forall_over U f"
  proof
    fix i
    assume i: "i \<in> pp_forall_over ?S f"
    show "i \<in> pp_forall_over U f"
      unfolding pp_forall_over_iff
    proof (intro ballI)
      fix X
      assume X: "X \<in> U"
      then have v: "f X \<in> f ` U" by blast
      have inS: "W (f X) \<in> ?S" using v by blast
      from i have all_S: "\<forall>Z \<in> ?S. i \<in> f Z"
        by (simp add: pp_forall_over_iff)
      then have "i \<in> f (W (f X))" using inS by blast
      then show "i \<in> f X" using W[OF v] by simp
    qed
  qed
  then show ?thesis
    unfolding pp_finitely_attained_def
    using S_sub S_fin by blast
qed

text \<open>
  The finite-image hypothesis is unusable for the term \<open>\<forall>X : Prop. X\<close>, whose body is
  the identity: its image is the whole domain.
\<close>

theorem pp_identity_image_is_the_domain:
  "id ` U = U"
  by simp

corollary pp_identity_body_has_no_finite_image_bound:
  assumes "infinite U"
  shows "\<not> finite (id ` U)"
  using assms by simp

subsection \<open>Closure supplies attainment where finite image fails\<close>

text \<open>
  Comprehension puts the value of \<open>\<forall>X. X\<close> into the domain at the quantified type.
  That single element attains the intersection, so persistence holds for the identity
  body no matter how large the domain is.
\<close>

theorem pp_closed_domain_attains_identity:
  assumes closed: "pp_forall_over U id \<in> U"
  shows "pp_finitely_attained U id"
proof -
  let ?V = "pp_forall_over U id"
  have "pp_forall_over {?V} id = ?V"
    by (auto simp: pp_forall_over_iff)
  then show ?thesis
    unfolding pp_finitely_attained_def
    using closed by blast
qed

corollary pp_closed_domain_identity_persistence:
  fixes D :: "nat \<Rightarrow> pp_sem_prop set"
  assumes step: "\<And>n. D n \<subseteq> D (Suc n)"
    and closed: "pp_forall_over (\<Union>n. D n) id \<in> (\<Union>n. D n)"
  shows "\<exists>N. \<forall>m \<ge> N.
    pp_forall_over (D m) id = pp_forall_over (\<Union>n. D n) id"
  using step pp_closed_domain_attains_identity[OF closed]
  by (rule pp_finitely_attained_persistence)

text \<open>
  More generally, a body that is monotone attains at the least proposition and a body
  that is antitone attains at the greatest, and every domain closed under the Boolean
  connectives contains both.
\<close>

theorem pp_monotone_body_attains:
  assumes bot: "{} \<in> U"
    and mono: "\<And>X Y. X \<subseteq> Y \<Longrightarrow> f X \<subseteq> f Y"
  shows "pp_finitely_attained U f"
proof -
  have "pp_forall_over {{}} f \<subseteq> pp_forall_over U f"
  proof
    fix i
    assume "i \<in> pp_forall_over {{}} f"
    then have "i \<in> f {}" by (simp add: pp_forall_over_iff)
    show "i \<in> pp_forall_over U f"
      unfolding pp_forall_over_iff
    proof (intro ballI)
      fix X
      assume "X \<in> U"
      have "f {} \<subseteq> f X" by (rule mono) simp
      then show "i \<in> f X" using \<open>i \<in> f {}\<close> by blast
    qed
  qed
  then show ?thesis
    unfolding pp_finitely_attained_def using bot by blast
qed

theorem pp_antitone_body_attains:
  assumes top: "UNIV \<in> U"
    and anti: "\<And>X Y. X \<subseteq> Y \<Longrightarrow> f Y \<subseteq> f X"
  shows "pp_finitely_attained U f"
proof -
  have "pp_forall_over {UNIV} f \<subseteq> pp_forall_over U f"
  proof
    fix i
    assume "i \<in> pp_forall_over {UNIV} f"
    then have "i \<in> f UNIV" by (simp add: pp_forall_over_iff)
    show "i \<in> pp_forall_over U f"
      unfolding pp_forall_over_iff
    proof (intro ballI)
      fix X
      assume "X \<in> U"
      have "f UNIV \<subseteq> f X" by (rule anti) simp
      then show "i \<in> f X" using \<open>i \<in> f UNIV\<close> by blast
    qed
  qed
  then show ?thesis
    unfolding pp_finitely_attained_def using top by blast
qed

subsection \<open>The earlier counterexample is not a Henkin chain\<close>

text \<open>
  The chain of \<open>Bacon_PP_Domain_Persistence\<close> refutes persistence, but its limit domain
  is not closed under comprehension: the value of \<open>\<forall>X. X\<close> over it is not one of its
  members.  So it is not a Henkin closure chain, and the refutation does not transfer.
\<close>

theorem pp_counterexample_domain_not_closed:
  "pp_forall_over (\<Union>n. pp_stage n) id \<notin> (\<Union>n. pp_stage n)"
proof
  assume mem: "pp_forall_over (\<Union>n. pp_stage n) id \<in> (\<Union>n. pp_stage n)"
  then obtain k where k: "pp_forall_over (\<Union>n. pp_stage n) id =
      - {pp_zeros k}"
    by (auto simp: pp_stage_Union)
  have "length (pp_zeros (Suc k)) \<noteq> length (pp_zeros k)"
    by simp
  then have "pp_zeros (Suc k) \<noteq> pp_zeros k"
    by (rule contrapos_nn) simp
  then have "pp_zeros (Suc k) \<in> - {pp_zeros k}"
    by simp
  then have "pp_zeros (Suc k) \<in>
      pp_forall_over (\<Union>n. pp_stage n) id"
    using k by simp
  moreover have "pp_zeros (Suc k) \<notin>
      pp_forall_over (\<Union>n. pp_stage n) id"
    by (rule pp_zeros_not_in_limit_value)
  ultimately show False by simp
qed

subsection \<open>What this settles, and what it leaves\<close>

text \<open>
  Settled.  Henkin closure chains do \emph{not} admit finite-image bounds --- the
  identity body defeats that hypothesis outright --- but finite image is a needlessly
  strong condition.  The condition the argument actually needs is finite attainment,
  and closure supplies it for the identity body, for every monotone body, and for
  every antitone body.  Since a domain closed under the Boolean connectives contains
  \<open>{}\<close> and \<open>UNIV\<close>, the monotone and antitone cases are unconditional in practice.

  Left open.  Bodies at the quantified type \<open>Prop\<close> that are neither monotone nor
  antitone.  For those, closure does give the limit value \<open>V\<close> back as a member of the
  domain, but instantiation supplies \<open>V \<subseteq> f V\<close>, which is the wrong inclusion for
  attainment; one needs some \<open>X\<^sub>0\<close> in the domain with \<open>f X\<^sub>0 \<subseteq> V\<close>.  Whether the
  Bacon--Dorr language can express a body defeating that is the precise remaining
  question, and it is now a question about a single inclusion rather than about
  chains, domains or witnesses.

  Note also that at a quantified type of the form \<open>\<sigma> \<rightarrow> Prop\<close> the difficulty does not
  arise, because the domain contains the constant function with value \<open>V\<close> and the
  body attains \<open>V\<close> there.  So any counterexample must quantify over \<open>Prop\<close> itself.
\<close>

end
