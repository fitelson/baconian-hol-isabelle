theory Bacon_PP_Fresh_CEVplus_Closure
  imports "Goodman_CEVplus.Bacon_CEV_Axiom_Extension"
begin

section \<open>The consequences of adding principles as axioms\<close>

text \<open>
  Fix a context and a stock of additional principles.  Its CEV+ closure is the
  set of propositions obtainable when Generalization, Instantiation, and
  vector Equivalence remain available above those principles.
\<close>

definition CEV_axiom_closure :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_axiom_closure \<Gamma> T = {A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A}"

lemma CEV_axiom_closure_iff:
  "A \<in> CEV_axiom_closure \<Gamma> T \<longleftrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  unfolding CEV_axiom_closure_def by simp

lemma CEV_axiom_closure_typed:
  "typed_theory \<Gamma> (CEV_axiom_closure \<Gamma> T)"
  unfolding typed_theory_def CEV_axiom_closure_def
  using CEV_axiom_proves_formula by blast

text \<open>
  A local derivation from the full CEV+ closure can be flattened into one
  CEV+ derivation from the original additional principles.  This is the key
  bridge between the relative axiom calculus and the existing canonical-world
  construction.
\<close>

lemma CEV_set_derivable_below_axiom_closure:
  assumes derivable: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
    and below: "U \<subseteq> CEV_axiom_closure \<Gamma> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A U \<Gamma>)
  have "A \<in> CEV_axiom_closure \<Gamma> T"
    using Assumption.hyps(1) Assumption.prems by blast
  then show ?case
    unfolding CEV_axiom_closure_def by simp
next
  case (Theorem \<Gamma> A U)
  show ?case
    using Theorem.hyps
    by (rule CEV_axiom_proves.Base)
next
  case (Derive_MP \<Gamma> U A B)
  have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  show ?case
    using d_A d_imp by (rule CEV_axiom_proves.MP)
qed

lemma CEV_set_derivable_from_axiom_closure:
  assumes "\<Gamma> ; CEV_axiom_closure \<Gamma> T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms order_refl by (rule CEV_set_derivable_below_axiom_closure)

theorem CEV_axiom_closure_locally_consistent:
  assumes "CEV_axiom_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (CEV_axiom_closure \<Gamma> T)"
proof (unfold CEV_consistent_def, intro notI)
  assume "\<Gamma> ; CEV_axiom_closure \<Gamma> T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    by (rule CEV_set_derivable_from_axiom_closure)
  then show False
    using assms unfolding CEV_axiom_consistent_def by blast
qed

subsection \<open>A canonical world containing every CEV+ consequence\<close>

theorem CEV_axiom_closure_has_locally_maximal_extension:
  assumes consistent: "CEV_axiom_consistent \<Gamma> T"
  obtains U where
    "CEV_locally_maximal_consistent \<Gamma> U"
    "CEV_axiom_closure \<Gamma> T \<subseteq> U"
proof -
  obtain enum where enum: "enumerates_formulas \<Gamma> enum"
    using enumerates_formulas_exists by blast
  let ?U =
    "CEV_lindenbaum_extension \<Gamma> (CEV_axiom_closure \<Gamma> T) enum"
  have local: "CEV_locally_maximal_consistent \<Gamma> ?U"
    using CEV_axiom_closure_typed
      CEV_axiom_closure_locally_consistent[OF consistent] enum
    by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  have extends: "CEV_axiom_closure \<Gamma> T \<subseteq> ?U"
    by (rule CEV_lindenbaum_extension_extends)
  show ?thesis
    using that local extends by blast
qed

corollary CEV_axiom_consequences_have_common_canonical_world:
  assumes consistent: "CEV_axiom_consistent \<Gamma> T"
  obtains U where
    "CEV_locally_maximal_consistent \<Gamma> U"
    "\<And>A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> U"
proof -
  obtain U where local: "CEV_locally_maximal_consistent \<Gamma> U"
    and closure_sub: "CEV_axiom_closure \<Gamma> T \<subseteq> U"
    using consistent
    by (rule CEV_axiom_closure_has_locally_maximal_extension)
  have consequence_in:
      "\<And>A. \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow> A \<in> U"
    using closure_sub unfolding CEV_axiom_closure_def by blast
  show ?thesis
    using that local consequence_in by blast
qed

subsection \<open>Clean Henkin extensions of finite stocks\<close>

text \<open>
  The clean witness construction starts from a finite typed consistent stock.
  We record the corresponding extension theorem independently of any
  particular formula whose failure is to be witnessed.
\<close>

theorem CEV_clean_Henkin_extension_of_finite_consistent:
  assumes finite_S: "finite S"
    and typed_S: "typed_theory \<Gamma> S"
    and consistent_S: "CEV_consistent \<Gamma> S"
  obtains U where
    "CEV_clean_Henkin_theory \<Gamma> U"
    "S \<subseteq> U"
proof -
  obtain body_enum where
      body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?H = "staged_henkin_extension \<Gamma> S body_enum"
  have S_sub_H: "S \<subseteq> ?H"
    by (rule staged_henkin_extension_extends)
  have typed_H: "typed_theory \<Gamma> ?H"
    using typed_S by (rule staged_henkin_extension_typed)
  have consistent_H: "CEV_consistent \<Gamma> ?H"
    using finite_S typed_S consistent_S
    by (rule CEV_staged_henkin_extension_consistent_clean)
  have available_H: "Henkin_witness_axioms_available \<Gamma> ?H"
    using body_enum
    by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where
      formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?U = "CEV_lindenbaum_extension \<Gamma> ?H formula_enum"
  have H_sub_U: "?H \<subseteq> ?U"
    by (rule CEV_lindenbaum_extension_extends)
  have local_U: "CEV_locally_maximal_consistent \<Gamma> ?U"
    using typed_H consistent_H formula_enum
    by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  have available_U: "Henkin_witness_axioms_available \<Gamma> ?U"
    using available_H H_sub_U
    by (rule Henkin_witness_axioms_available_mono)
  have witnessed_U: "Henkin_witnessed \<Gamma> ?U"
    using local_U available_U
    by (rule Henkin_witnessed_of_CEV_local_maximal_available_clean)
  have clean_U: "CEV_clean_Henkin_theory \<Gamma> ?U"
    using local_U witnessed_U
    unfolding CEV_clean_Henkin_theory_def by blast
  have S_sub_U: "S \<subseteq> ?U"
    using S_sub_H H_sub_U by blast
  show ?thesis
    using that clean_U S_sub_U by blast
qed

theorem finite_CEV_axiom_consequences_have_clean_Henkin_extension:
  assumes consistent: "CEV_axiom_consistent \<Gamma> T"
    and finite_S: "finite S"
    and consequences: "S \<subseteq> CEV_axiom_closure \<Gamma> T"
  obtains U where
    "CEV_clean_Henkin_theory \<Gamma> U"
    "S \<subseteq> U"
proof -
  have typed_closure: "typed_theory \<Gamma> (CEV_axiom_closure \<Gamma> T)"
    by (rule CEV_axiom_closure_typed)
  have typed_S: "typed_theory \<Gamma> S"
    using typed_closure consequences unfolding typed_theory_def by blast
  have consistent_closure:
      "CEV_consistent \<Gamma> (CEV_axiom_closure \<Gamma> T)"
    using consistent by (rule CEV_axiom_closure_locally_consistent)
  have consistent_S: "CEV_consistent \<Gamma> S"
    using consistent_closure consequences by (rule CEV_consistent_mono)
  show ?thesis
    using finite_S typed_S consistent_S that
    by (rule CEV_clean_Henkin_extension_of_finite_consistent)
qed

corollary finite_batch_of_CEV_axiom_proofs_has_clean_Henkin_extension:
  assumes consistent: "CEV_axiom_consistent \<Gamma> T"
    and finite_S: "finite S"
    and consequences: "\<And>A. A \<in> S \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  obtains U where
    "CEV_clean_Henkin_theory \<Gamma> U"
    "S \<subseteq> U"
proof -
  have "S \<subseteq> CEV_axiom_closure \<Gamma> T"
    using consequences unfolding CEV_axiom_closure_def by blast
  then have ex:
      "\<exists>U. CEV_clean_Henkin_theory \<Gamma> U \<and> S \<subseteq> U"
  proof -
    assume subset: "S \<subseteq> CEV_axiom_closure \<Gamma> T"
    show ?thesis
      apply (rule finite_CEV_axiom_consequences_have_clean_Henkin_extension[
          OF consistent finite_S subset])
      by blast
  qed
  then obtain U where clean_U: "CEV_clean_Henkin_theory \<Gamma> U"
    and S_sub_U: "S \<subseteq> U"
    by blast
  show ?thesis
    using that clean_U S_sub_U by blast
qed

text \<open>
  The common canonical world above contains the entire CEV+ closure.  The
  clean Henkin conclusion is presently obtained for each finite batch.  The
  existing staged witness construction assumes a finite initial stock, so the
  results here do not yet supply one clean Henkin world containing the whole
  (generally infinite) CEV+ closure.
\<close>

end
