theory Bacon_PP_Coherence
  imports Bacon_PP
begin

section \<open>Audit: the C-purity coherence diagram is CEV-inconsistent\<close>

text \<open>
  This theory is an external audit of \<open>pp_CEV_purity_coherence_consistent\<close>.
  It refutes that claim.  Nothing in \<open>Bacon_PP\<close> or its ancestors is changed.

  (1) Object-level Booleanism.  \<open>CEV_proves.ContextVectorEquivalence\<close>
  instantiated at the empty vector yields the object-language schema
  \<open>(A \<longleftrightarrow> B) \<longrightarrow> A = B\<close>, not merely the theorem-level Equivalence rule
  of \<open>CE\<close>.  With Leibniz's Law this forces \<open>Pure\<close> at type \<open>Prop\<close> to be a
  truth function of its argument.

  (2) The diagram is hyperintensional.  It classifies purity by
  \<open>C\<close>-provable observational equivalence, and \<open>C\<close> has neither the
  Equivalence rule nor zeta.  \<open>ObjTrue\<close> and \<open>ObjFalse\<close> are both \<open>r\<close>-free,
  hence both classified pure, while \<open>pp_r\<close> is not.

  (3) Unconditionality.  If \<open>pp_r\<close> were C-observationally pure then \<open>C\<close>
  itself would prove \<open>ObjFalse\<close>, and the diagram would be CEV-inconsistent
  for that reason instead.  So no consistency assumption is used.
\<close>

subsection \<open>Propositional plumbing\<close>

lemma CEV_imp_trans:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
    and BC: "\<Gamma> \<turnstile>\<^sub>CEV Imp B C"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A C"
proof -
  have taut: "prop_tautology \<Gamma> (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
    unfolding prop_tautology_def
    using A_type B_type C_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A B) (Imp (Imp B C) (Imp A C))"
    using taut by (rule CEV_prop_tautology)
  then have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp B C) (Imp A C)"
    by (rule CEV_proves.MP[OF AB])
  then show ?thesis
    by (rule CEV_proves.MP[OF BC])
qed

lemma consts_of_ObjTrue[simp]:
  "consts_of ObjTrue = {}"
  by (simp add: ObjTrue_def)

lemma consts_of_ObjFalse[simp]:
  "consts_of ObjFalse = {}"
  by (simp add: ObjFalse_def)

subsection \<open>Object-level Booleanism is a CEV theorem\<close>

lemma CEV_bicond_imp_Eq:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Eq Prop A B)"
proof -
  have bicond_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (A \<longleftrightarrow>\<^sub>o B))"
    unfolding prop_tautology_def
    using bicond_type by auto
  have body: "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (A \<longleftrightarrow>\<^sub>o B)"
    using taut by (rule CEV_prop_tautology)
  have prem: "[] @ \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift_by (length ([] :: otype list)) (A \<longleftrightarrow>\<^sub>o B))
        (zeta_body [] A B)"
    using body by (simp add: zeta_body_def fresh_vars_def)
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (A \<longleftrightarrow>\<^sub>o B) (Eq (arrow_type [] Prop) A B)"
    by (rule CEV_proves.ContextVectorEquivalence
        [where \<sigma>s = "[]" and A = "(A \<longleftrightarrow>\<^sub>o B)" and F = A and G = B])
       (use bicond_type A_type B_type prem in simp_all)
  then show ?thesis
    by simp
qed

subsection \<open>Leibniz congruence for the \<open>Pure\<close> predicate\<close>

lemma CEV_Eq_imp_pure:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> A B) (Imp (pp_pure \<sigma> A) (pp_pure \<sigma> B))"
proof -
  have "\<Gamma> \<turnstile>\<^sub>H
      Imp (Eq \<sigma> A B) (Imp (App (pp_Pure \<sigma>) A) (App (pp_Pure \<sigma>) B))"
    using A_type B_type typed_pp_Pure by (rule H_proves.LL)
  then show ?thesis
    unfolding pp_pure_def
    by (intro CEV_proves.CE CE_proves.C C_proves.H)
qed

lemma CEV_bicond_imp_pure:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (pp_pure Prop A) (pp_pure Prop B))"
proof (rule CEV_imp_trans)
  show "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Eq Prop A B)"
    using A_type B_type by (rule CEV_bicond_imp_Eq)
next
  show "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq Prop A B) (Imp (pp_pure Prop A) (pp_pure Prop B))"
    using A_type B_type by (rule CEV_Eq_imp_pure)
next
  show "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
next
  show "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using A_type B_type by auto
next
  show "\<Gamma> \<turnstile> Imp (pp_pure Prop A) (pp_pure Prop B) : Prop"
    using typed_pp_pure[OF A_type] typed_pp_pure[OF B_type] by auto
qed

subsection \<open>\<open>Pure\<close> at type \<open>Prop\<close> is forced to be two-valued\<close>

theorem CEV_pure_two_valued:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (pp_pure Prop ObjTrue)
      (Imp (pp_pure Prop ObjFalse) (pp_pure Prop A))"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have false_type: "\<Gamma> \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  let ?T = "Imp (ObjTrue \<longleftrightarrow>\<^sub>o A)
      (Imp (pp_pure Prop ObjTrue) (pp_pure Prop A))"
  let ?F = "Imp (ObjFalse \<longleftrightarrow>\<^sub>o A)
      (Imp (pp_pure Prop ObjFalse) (pp_pure Prop A))"
  let ?G = "Imp (pp_pure Prop ObjTrue)
      (Imp (pp_pure Prop ObjFalse) (pp_pure Prop A))"
  have top: "\<Gamma> \<turnstile>\<^sub>CEV ?T"
    using true_type A_type by (rule CEV_bicond_imp_pure)
  have bot: "\<Gamma> \<turnstile>\<^sub>CEV ?F"
    using false_type A_type by (rule CEV_bicond_imp_pure)
  have taut: "prop_tautology \<Gamma> (Imp ?T (Imp ?F ?G))"
  proof (unfold prop_tautology_def, rule conjI)
    show "\<Gamma> \<turnstile> Imp ?T (Imp ?F ?G) : Prop"
      using A_type true_type false_type
        typed_pp_pure[OF A_type] typed_pp_pure[OF true_type]
        typed_pp_pure[OF false_type]
      by (blast intro: has_type.Imp has_type.Conj)
  next
    show "\<forall>v. prop_eval v (Imp ?T (Imp ?F ?G))"
      by (auto simp: ObjFalse_def pp_pure_def)
  qed
  have chain: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?T (Imp ?F ?G)"
    using taut by (rule CEV_prop_tautology)
  have step: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?F ?G"
    using chain by (rule CEV_proves.MP[OF top])
  show ?thesis
    using step by (rule CEV_proves.MP[OF bot])
qed

subsection \<open>Both truth values are in the diagram, positively\<close>

lemma pure_term_ObjTrue:
  "pp_r_free_closed_pure_term_at Prop ObjTrue"
  unfolding pp_r_free_closed_pure_term_at_def pp_expanded_pure_vocabulary_def
  using typed_ObjTrue by simp

lemma pure_term_ObjFalse:
  "pp_r_free_closed_pure_term_at Prop ObjFalse"
  unfolding pp_r_free_closed_pure_term_at_def pp_expanded_pure_vocabulary_def
  using typed_ObjFalse by simp

lemma pp_pure_ObjTrue_in_diagram:
  "pp_pure Prop ObjTrue \<in> pp_C_purity_coherence_diagram"
proof (rule pp_C_purity_coherence_positive_iff)
  show "[] \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
next
  show "pp_project_vocabulary ObjTrue"
    unfolding pp_project_vocabulary_def by simp
next
  show "pp_C_observationally_pure Prop ObjTrue"
    using pure_term_ObjTrue
    by (rule pp_r_free_term_is_C_observationally_pure)
qed

lemma pp_pure_ObjFalse_in_diagram:
  "pp_pure Prop ObjFalse \<in> pp_C_purity_coherence_diagram"
proof (rule pp_C_purity_coherence_positive_iff)
  show "[] \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
next
  show "pp_project_vocabulary ObjFalse"
    unfolding pp_project_vocabulary_def by simp
next
  show "pp_C_observationally_pure Prop ObjFalse"
    using pure_term_ObjFalse
    by (rule pp_r_free_term_is_C_observationally_pure)
qed

subsection \<open>The diagram proves \<open>Pure\<close> of every closed proposition\<close>

theorem pp_C_purity_coherence_diagram_derives_pure:
  assumes A_type: "[] \<turnstile> A : Prop"
  shows "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop A"
proof -
  have top: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s
      pp_pure Prop ObjTrue"
    using pp_pure_ObjTrue_in_diagram typed_pp_pure[OF typed_ObjTrue]
    by (rule CEV_set_derivable.Assumption)
  have bot: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s
      pp_pure Prop ObjFalse"
    using pp_pure_ObjFalse_in_diagram typed_pp_pure[OF typed_ObjFalse]
    by (rule CEV_set_derivable.Assumption)
  have two_valued: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s
      Imp (pp_pure Prop ObjTrue)
        (Imp (pp_pure Prop ObjFalse) (pp_pure Prop A))"
    using CEV_pure_two_valued[OF A_type] by (rule CEV_set_derivable.Theorem)
  have step: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s
      Imp (pp_pure Prop ObjFalse) (pp_pure Prop A)"
    using top two_valued by (rule CEV_set_derivable.Derive_MP)
  show ?thesis
    using bot step by (rule CEV_set_derivable.Derive_MP)
qed

subsection \<open>\<open>r\<close> is not C-observationally pure, on pain of C-inconsistency\<close>

lemma C_ObjFalse_of_C_pure_r:
  assumes pure: "pp_C_observationally_pure Prop pp_r"
  shows "[] \<turnstile>\<^sub>C ObjFalse"
proof -
  obtain Q where Q_pure: "pp_r_free_closed_pure_term_at Prop Q"
    and equiv: "pp_C_observational_equivalence Prop pp_r Q"
    using pure unfolding pp_C_observationally_pure_def by blast
  have Q_type: "[] \<turnstile> Q : Prop"
    using Q_pure unfolding pp_r_free_closed_pure_term_at_def by blast
  have Q_vocab: "consts_of Q \<subseteq> {pp_pure_name}"
    using Q_pure
    unfolding pp_r_free_closed_pure_term_at_def
      pp_expanded_pure_vocabulary_def
    by blast
  have r_fresh: "pp_r_name \<notin> consts_of Q"
    using Q_vocab by (auto simp: pp_pure_name_def pp_r_name_def)
  have bicond: "[] \<turnstile>\<^sub>C (pp_r \<longleftrightarrow>\<^sub>o Q)"
    using equiv by simp
  have sub_true: "[] \<turnstile>\<^sub>C (ObjTrue \<longleftrightarrow>\<^sub>o Q)"
  proof -
    have "[] \<turnstile>\<^sub>C subst_const pp_r_name Prop ObjTrue (pp_r \<longleftrightarrow>\<^sub>o Q)"
      using bicond typed_ObjTrue by (rule C_proves_subst_const)
    then show ?thesis
      by (simp add: pp_r_def r_fresh)
  qed
  have sub_false: "[] \<turnstile>\<^sub>C (ObjFalse \<longleftrightarrow>\<^sub>o Q)"
  proof -
    have "[] \<turnstile>\<^sub>C subst_const pp_r_name Prop ObjFalse (pp_r \<longleftrightarrow>\<^sub>o Q)"
      using bicond typed_ObjFalse by (rule C_proves_subst_const)
    then show ?thesis
      by (simp add: pp_r_def r_fresh)
  qed
  have taut: "prop_tautology []
      (Imp (ObjTrue \<longleftrightarrow>\<^sub>o Q) (Imp (ObjFalse \<longleftrightarrow>\<^sub>o Q) ObjFalse))"
  proof (unfold prop_tautology_def, rule conjI)
    show "[] \<turnstile> Imp (ObjTrue \<longleftrightarrow>\<^sub>o Q)
        (Imp (ObjFalse \<longleftrightarrow>\<^sub>o Q) ObjFalse) : Prop"
      using Q_type typed_ObjTrue typed_ObjFalse
      by (blast intro: has_type.Imp has_type.Conj)
  next
    show "\<forall>v. prop_eval v
        (Imp (ObjTrue \<longleftrightarrow>\<^sub>o Q) (Imp (ObjFalse \<longleftrightarrow>\<^sub>o Q) ObjFalse))"
      by (auto simp: ObjFalse_def)
  qed
  have chain: "[] \<turnstile>\<^sub>C
      Imp (ObjTrue \<longleftrightarrow>\<^sub>o Q) (Imp (ObjFalse \<longleftrightarrow>\<^sub>o Q) ObjFalse)"
    using taut by (intro C_proves.H H_proves.PC)
  have step: "[] \<turnstile>\<^sub>C Imp (ObjFalse \<longleftrightarrow>\<^sub>o Q) ObjFalse"
    using sub_true chain by (rule C_proves.MP)
  show ?thesis
    using sub_false step by (rule C_proves.MP)
qed

subsection \<open>The refutation\<close>

lemma pp_pure_r_explosion:
  assumes pos: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop pp_r"
    and neg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Neg (pp_pure Prop pp_r)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  have taut: "prop_tautology \<Gamma>
      (Imp (pp_pure Prop pp_r) (Imp (Neg (pp_pure Prop pp_r)) ObjFalse))"
  proof (unfold prop_tautology_def, rule conjI)
    show "\<Gamma> \<turnstile> Imp (pp_pure Prop pp_r)
        (Imp (Neg (pp_pure Prop pp_r)) ObjFalse) : Prop"
      using typed_pp_pure[OF typed_pp_r] typed_ObjFalse
      by (blast intro: has_type.Imp has_type.Neg)
  next
    show "\<forall>v. prop_eval v
        (Imp (pp_pure Prop pp_r)
          (Imp (Neg (pp_pure Prop pp_r)) ObjFalse))"
      by (auto simp: ObjFalse_def pp_pure_def)
  qed
  have refute: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
      Imp (pp_pure Prop pp_r) (Imp (Neg (pp_pure Prop pp_r)) ObjFalse)"
    using CEV_prop_tautology[OF taut] by (rule CEV_set_derivable.Theorem)
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Neg (pp_pure Prop pp_r)) ObjFalse"
    using pos refute by (rule CEV_set_derivable.Derive_MP)
  show ?thesis
    using neg step by (rule CEV_set_derivable.Derive_MP)
qed

theorem pp_CEV_purity_coherence_inconsistent:
  "\<not> pp_CEV_purity_coherence_consistent"
proof (unfold pp_CEV_purity_coherence_consistent_def CEV_consistent_def,
    simp only: not_not)
  show "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  proof (cases "pp_C_observationally_pure Prop pp_r")
    case True
    have "[] \<turnstile>\<^sub>C ObjFalse"
      using True by (rule C_ObjFalse_of_C_pure_r)
    then have "[] \<turnstile>\<^sub>CEV ObjFalse"
      by (intro CEV_proves.CE CE_proves.C)
    then show ?thesis
      by (rule CEV_set_derivable.Theorem)
  next
    case False
    have neg_in: "Neg (pp_pure Prop pp_r) \<in> pp_C_purity_coherence_diagram"
    proof (rule pp_C_purity_coherence_negative_iff)
      show "[] \<turnstile> pp_r : Prop"
        by (rule typed_pp_r)
    next
      show "pp_project_vocabulary pp_r"
        unfolding pp_project_vocabulary_def pp_r_def by simp
    next
      show "\<not> pp_C_observationally_pure Prop pp_r"
        using False .
    qed
    have neg: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s
        Neg (pp_pure Prop pp_r)"
      using neg_in typed_pp_pure[OF typed_pp_r] by auto
    have pos: "[] ; pp_C_purity_coherence_diagram \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop pp_r"
      using typed_pp_r by (rule pp_C_purity_coherence_diagram_derives_pure)
    show ?thesis
      using pos neg by (rule pp_pure_r_explosion)
  qed
qed

corollary pp_no_CEV_purity_coherent_Henkin_theory:
  "\<not> (\<exists>T. pp_CEV_purity_coherent_Henkin_theory T)"
  using pp_CEV_purity_coherent_Henkin_exists_iff
    pp_CEV_purity_coherence_inconsistent
  by blast

subsection \<open>The minimal explicit core\<close>

theorem pp_purity_coherence_minimal_core_inconsistent:
  "\<not> CEV_consistent []
    {pp_pure Prop ObjTrue, pp_pure Prop ObjFalse, Neg (pp_pure Prop pp_r)}"
proof (unfold CEV_consistent_def, simp only: not_not)
  let ?D = "{pp_pure Prop ObjTrue, pp_pure Prop ObjFalse,
    Neg (pp_pure Prop pp_r)}"
  have top: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop ObjTrue"
    using typed_pp_pure[OF typed_ObjTrue] by auto
  have bot: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop ObjFalse"
    using typed_pp_pure[OF typed_ObjFalse] by auto
  have neg: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s Neg (pp_pure Prop pp_r)"
    using typed_pp_pure[OF typed_pp_r] by auto
  have two_valued: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s
      Imp (pp_pure Prop ObjTrue)
        (Imp (pp_pure Prop ObjFalse) (pp_pure Prop pp_r))"
    using CEV_pure_two_valued[OF typed_pp_r]
    by (rule CEV_set_derivable.Theorem)
  have step1: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s
      Imp (pp_pure Prop ObjFalse) (pp_pure Prop pp_r)"
    using top two_valued by (rule CEV_set_derivable.Derive_MP)
  have pos: "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop pp_r"
    using bot step1 by (rule CEV_set_derivable.Derive_MP)
  show "[] ; ?D \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using pos neg by (rule pp_pure_r_explosion)
qed

end
