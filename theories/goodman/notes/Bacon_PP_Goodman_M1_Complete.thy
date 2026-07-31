theory Bacon_PP_Goodman_M1_Complete
  imports
    Bacon_PP_Goodman_M3_Complete
    Bacon_PP_T6_Encoding
begin

section \<open>Completion of Goodman M1: the footnote-59 term\<close>

definition pp_M1_fn59_liar :: oterm where
  "pp_M1_fn59_liar =
    Lam Prop
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun Prop (Var 0))
                (Eq Prop
                  (Var 2)
                  (App (Var 1) (Var 0)))))
            (Neg (App (Var 1) (Var 2))))))"

text \<open>
  Under the inner binders, this is
  \<open>D p \<longleftrightarrow> \<forall>X q.
    Pure(X) \<and> Fun(q) \<and> p = X q \<longrightarrow> \<not> X p\<close>.
  Unique proposition-level fundamentality reduces the quantified \<open>q\<close> to
  the distinguished fundamental proposition, yielding exactly the semantic
  diagonal used in \<open>pp_M1_fn59_diagonal_contradiction\<close>.
\<close>

lemma typed_pp_M1_fn59_liar:
  "\<Gamma> \<turnstile> pp_M1_fn59_liar : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_M1_fn59_liar_def pp_unary_ty_def
      pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def lookup_def)

definition pp_M1_fn59_builder :: oterm where
  "pp_M1_fn59_builder =
    Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      (Lam (Prop \<rightarrow>\<^sub>o Prop)
        (Lam Prop
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (App (Var 4) (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))))"

abbreviation pp_M1_fn59_instance :: oterm where
  "pp_M1_fn59_instance \<equiv>
    App
      (App pp_M1_fn59_builder (pp_Pure pp_unary_ty))
      (pp_Fun Prop)"

definition pp_M1_fn59_after_pure :: oterm where
  "pp_M1_fn59_after_pure =
    Lam (Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop
        (Forall pp_unary_ty
          (Forall Prop
            (Imp
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (Conj
                  (App (Var 3) (Var 0))
                  (Eq Prop
                    (Var 2)
                    (App (Var 1) (Var 0)))))
              (Neg (App (Var 1) (Var 2)))))))"

lemma pp_M1_fn59_builder_constant_free:
  "consts_of pp_M1_fn59_builder = {}"
  by (simp add: pp_M1_fn59_builder_def)

lemma typed_pp_M1_fn59_builder:
  "\<Gamma> \<turnstile> pp_M1_fn59_builder :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_M1_fn59_builder_def pp_unary_ty_def lookup_def)

lemma typed_pp_M1_fn59_instance:
  "\<Gamma> \<turnstile> pp_M1_fn59_instance : pp_unary_ty"
  using typed_pp_M1_fn59_builder
    typed_pp_Pure[of \<Gamma> pp_unary_ty]
    typed_pp_Fun[of \<Gamma> Prop]
  by (intro has_type.App)

lemma typed_pp_M1_fn59_after_pure:
  "\<Gamma> \<turnstile> pp_M1_fn59_after_pure :
    (Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_M1_fn59_after_pure_def pp_unary_ty_def
      pp_pure_def pp_Pure_def lookup_def)

lemma pp_M1_fn59_first_beta:
  "beta_contract
    (App pp_M1_fn59_builder (pp_Pure pp_unary_ty))
    pp_M1_fn59_after_pure"
proof -
  have "beta_contract
      (App pp_M1_fn59_builder (pp_Pure pp_unary_ty))
      (subst0 (pp_Pure pp_unary_ty)
        (Lam (Prop \<rightarrow>\<^sub>o Prop)
          (Lam Prop
            (Forall pp_unary_ty
              (Forall Prop
                (Imp
                  (Conj
                    (App (Var 4) (Var 1))
                    (Conj
                      (App (Var 3) (Var 0))
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))))
                  (Neg (App (Var 1) (Var 2)))))))))"
    unfolding pp_M1_fn59_builder_def
    by (rule beta_contract.beta)
  then show ?thesis
    by (simp add: pp_M1_fn59_after_pure_def subst0_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      eval_nat_numeral)
qed

lemma pp_M1_fn59_second_beta:
  "beta_contract
    (App pp_M1_fn59_after_pure (pp_Fun Prop))
    pp_M1_fn59_liar"
proof -
  have "beta_contract
      (App pp_M1_fn59_after_pure (pp_Fun Prop))
      (subst0 (pp_Fun Prop)
        (Lam Prop
          (Forall pp_unary_ty
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))))
                (Neg (App (Var 1) (Var 2))))))))"
    unfolding pp_M1_fn59_after_pure_def
    by (rule beta_contract.beta)
  then show ?thesis
    by (simp add: pp_M1_fn59_liar_def subst0_def
      pp_fun_def pp_Fun_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def eval_nat_numeral)
qed

lemma pp_M1_fn59_instance_beta_eta:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty pp_M1_fn59_instance pp_M1_fn59_liar"
proof -
  have instance_type:
      "\<Gamma> \<turnstile> pp_M1_fn59_instance : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_M1_fn59_instance
    by (simp add: pp_unary_ty_def)
  have liar_type:
      "\<Gamma> \<turnstile> pp_M1_fn59_liar : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_M1_fn59_liar
    by (simp add: pp_unary_ty_def)
  have pointwise:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App (shift pp_M1_fn59_instance) (Var 0)
          \<longleftrightarrow>\<^sub>o
         App (shift pp_M1_fn59_liar) (Var 0))"
  proof -
    have left_type:
        "Prop # \<Gamma> \<turnstile>
          App pp_M1_fn59_instance (Var 0) : Prop"
      using typed_pp_M1_fn59_instance typed_var0
      unfolding pp_unary_ty_def by (rule has_type.App)
    have right_type:
        "Prop # \<Gamma> \<turnstile>
          App pp_M1_fn59_liar (Var 0) : Prop"
      using typed_pp_M1_fn59_liar typed_var0
      unfolding pp_unary_ty_def by (rule has_type.App)
    have middle_type:
        "Prop # \<Gamma> \<turnstile>
          App (App pp_M1_fn59_after_pure (pp_Fun Prop)) (Var 0) :
            Prop"
      using typed_pp_M1_fn59_after_pure typed_pp_Fun typed_var0
      unfolding pp_unary_ty_def by (intro has_type.App)
    have first_step:
        "compatible_step beta_contract
          (App pp_M1_fn59_instance (Var 0))
          (App (App pp_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))"
      by (intro compatible_step.App_left compatible_step.App_left
          compatible_step.root pp_M1_fn59_first_beta)
    have second_step:
        "compatible_step beta_contract
          (App (App pp_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))
          (App pp_M1_fn59_liar (Var 0))"
      by (intro compatible_step.App_left compatible_step.root
          pp_M1_fn59_second_beta)
    have first_beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App pp_M1_fn59_instance (Var 0))
          (App (App pp_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))"
      using left_type middle_type first_step
      by (rule beta_eta_equiv.Beta)
    have second_beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App (App pp_M1_fn59_after_pure (pp_Fun Prop)) (Var 0))
          (App pp_M1_fn59_liar (Var 0))"
      using middle_type right_type second_step
      by (rule beta_eta_equiv.Beta)
    have beta:
        "beta_eta_equiv (Prop # \<Gamma>) Prop
          (App pp_M1_fn59_instance (Var 0))
          (App pp_M1_fn59_liar (Var 0))"
      using first_beta second_beta by (rule beta_eta_equiv.Trans)
    have
        "Prop # \<Gamma> \<turnstile>\<^sub>CEV
          (App pp_M1_fn59_instance (Var 0)
            \<longleftrightarrow>\<^sub>o
           App pp_M1_fn59_liar (Var 0))"
      using beta by (rule CEV_beta_eta_equiv)
    then show ?thesis
      by (simp add: shift_def pp_M1_fn59_builder_def
          pp_M1_fn59_liar_def pp_pure_def pp_Pure_def
          pp_fun_def pp_Fun_def shift_by_def shift_ren_def
          eval_nat_numeral)
  qed
  have
      "\<Gamma> \<turnstile>\<^sub>CEV
        Eq (Prop \<rightarrow>\<^sub>o Prop)
          pp_M1_fn59_instance pp_M1_fn59_liar"
    using instance_type liar_type pointwise
    by (rule CEV_unary_equivalence)
  then show ?thesis
    by (simp add: pp_unary_ty_def)
qed

definition pp_M1_fn59_axioms :: "oterm set" where
  "pp_M1_fn59_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_target_PP, pp_purity_of_fun Prop}"

lemma pp_M1_fn59_builder_purity_axiom:
  "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o pp_unary_ty)
      pp_M1_fn59_builder \<in> pp_M1_fn59_axioms"
  unfolding pp_M1_fn59_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
  using typed_pp_M1_fn59_builder
    pp_M1_fn59_builder_constant_free
  by blast

lemma pp_M1_fn59_application_closure:
  "pp_application_closure \<sigma> \<tau> \<in> pp_M1_fn59_axioms"
  unfolding pp_M1_fn59_axioms_def
    pp_application_closure_schema_def by blast

lemma pp_M1_fn59_PP:
  "pp_target_PP \<in> pp_M1_fn59_axioms"
  unfolding pp_M1_fn59_axioms_def by blast

lemma pp_M1_fn59_purity_of_fun:
  "pp_purity_of_fun Prop \<in> pp_M1_fn59_axioms"
  unfolding pp_M1_fn59_axioms_def by blast

theorem pp_M1_fn59_liar_pure:
  "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_M1_fn59_liar"
proof -
  let ?builder_ty =
    "(pp_unary_ty \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o pp_unary_ty"
  let ?after_pure_ty =
    "(Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  have builder_pure:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure ?builder_ty pp_M1_fn59_builder"
    using pp_M1_fn59_builder_purity_axiom
      typed_pp_pure[OF typed_pp_M1_fn59_builder]
    by (rule CEV_axiom_proves.Axiom)
  have Pure_pure:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop)
          (pp_Pure pp_unary_ty)"
  proof -
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_pure_def pp_Pure_def pp_unary_ty_def lookup_def)
    have
        "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using pp_M1_fn59_PP target_type
      by (rule CEV_axiom_proves.Axiom)
    then show ?thesis
      by (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_unary_ty_def)
  qed
  have first_pure:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure ?after_pure_ty
          (App pp_M1_fn59_builder (pp_Pure pp_unary_ty))"
    using pp_M1_fn59_application_closure[
        of "pp_unary_ty \<rightarrow>\<^sub>o Prop" ?after_pure_ty]
      typed_pp_M1_fn59_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
      builder_pure Pure_pure
    by (rule pp_axiom_application_closed)
  have Fun_pure:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (Prop \<rightarrow>\<^sub>o Prop) (pp_Fun Prop)"
  proof -
    have fun_purity_type:
        "\<Gamma> \<turnstile> pp_purity_of_fun Prop : Prop"
      by (rule infer_type_sound)
        (simp add: pp_purity_of_fun_def pp_pure_def pp_Pure_def
          pp_Fun_def lookup_def)
    show ?thesis
      using pp_M1_fn59_purity_of_fun fun_purity_type
      unfolding pp_purity_of_fun_def
      by (rule CEV_axiom_proves.Axiom)
  qed
  have first_type:
      "\<Gamma> \<turnstile>
        App pp_M1_fn59_builder (pp_Pure pp_unary_ty) :
          ?after_pure_ty"
    using typed_pp_M1_fn59_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
    by (rule has_type.App)
  have instance_pure:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty pp_M1_fn59_instance"
    using pp_M1_fn59_application_closure[
        of "Prop \<rightarrow>\<^sub>o Prop" pp_unary_ty]
      first_type typed_pp_Fun first_pure Fun_pure
    by (rule pp_axiom_application_closed)
  have identity:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Eq pp_unary_ty pp_M1_fn59_instance pp_M1_fn59_liar"
    using pp_M1_fn59_instance_beta_eta
    by (rule CEV_axiom_proves.Base)
  have transfer:
      "\<Gamma> ; pp_M1_fn59_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_pure pp_unary_ty pp_M1_fn59_instance)
          (pp_pure pp_unary_ty pp_M1_fn59_liar)"
  proof -
    have ll:
        "\<Gamma> \<turnstile>\<^sub>CEV
          Imp
            (Eq pp_unary_ty
              pp_M1_fn59_instance pp_M1_fn59_liar)
            (Imp
              (pp_pure pp_unary_ty pp_M1_fn59_instance)
              (pp_pure pp_unary_ty pp_M1_fn59_liar))"
      using typed_pp_M1_fn59_instance typed_pp_M1_fn59_liar
        typed_pp_Pure
      unfolding pp_pure_def
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
    show ?thesis
      using identity CEV_axiom_proves.Base[OF ll]
      by (rule CEV_axiom_proves.MP)
  qed
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_proves.MP)
qed

theorem pp_M1_fn59_unique_fun_diagonal_contradiction:
  fixes Stock :: "('p \<Rightarrow> 'p) set"
    and truth :: "'p \<Rightarrow> bool"
    and Fun :: "'p \<Rightarrow> bool"
    and r :: 'p
    and D :: "'p \<Rightarrow> 'p"
  assumes D_pure: "D \<in> Stock"
    and qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and r_fun: "Fun r"
    and unique_fun: "\<And>q. Fun q \<Longrightarrow> q = r"
    and diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. \<forall>q.
          Fun q \<longrightarrow> p = X q \<longrightarrow> \<not> truth (X p))"
  shows False
proof -
  have reduced_diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. p = X r \<longrightarrow> \<not> truth (X p))"
    using diagonal r_fun unique_fun by blast
  show False
    using D_pure qss reduced_diagonal
    by (rule pp_M1_fn59_diagonal_contradiction)
qed

corollary pp_M1_fn59_unique_fun_diagonal_contradiction_sem:
  fixes Stock :: "(pp_sem_prop \<Rightarrow> pp_sem_prop) set"
    and truth :: "pp_sem_prop \<Rightarrow> bool"
    and Fun :: "pp_sem_prop \<Rightarrow> bool"
    and r :: pp_sem_prop
    and D :: "pp_sem_prop \<Rightarrow> pp_sem_prop"
  assumes D_pure: "D \<in> Stock"
    and qss:
      "\<And>F G. F \<in> Stock \<Longrightarrow> G \<in> Stock \<Longrightarrow>
        F r = G r \<Longrightarrow> F = G"
    and r_fun: "Fun r"
    and unique_fun: "\<And>q. Fun q \<Longrightarrow> q = r"
    and diagonal:
      "\<And>p. truth (D p) =
        (\<forall>X \<in> Stock. \<forall>q.
          Fun q \<longrightarrow> p = X q \<longrightarrow> \<not> truth (X p))"
  shows False
  using assms
  by (rule pp_M1_fn59_unique_fun_diagonal_contradiction)

text \<open>
  This completes the object-language half of the bridge left open in
  \<open>Bacon_PP_Goodman_M1\<close>.  The footnote-59 diagonal is an explicit well-typed
  term; abstracting its occurrences of \<open>Pure\<close> and \<open>Fun\<close> yields a closed
  constant-free builder; PP, Purity of Fun, and two applications of
  application closure certify the liar itself as pure.  A separate semantic
  instantiation is required to turn this abstract contradiction into a claim
  about any particular model.
\<close>

end
