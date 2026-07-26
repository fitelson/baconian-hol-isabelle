theory Bacon_PP_Goodman_Heredity
  imports Bacon_PP_Goodman_T2f_Verified
begin

section \<open>Goodman T3: Heredity\<close>

text \<open>
  QSS says that two pure proposition-valued unary operators which agree on a
  fundamental proposition are identical.  In an axiom extension, QSS can be
  necessitated by \<open>CEV_axiom_necessitation\<close>.  Goodman T3 additionally uses
  Persistence to conclude that anything which is possibly fundamental is a
  \<open>fun\<acute>\<close> proposition.
\<close>

definition pp_QSS :: oterm where
  "pp_QSS =
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 2))
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop (App (Var 2) (Var 0))
                (App (Var 1) (Var 0)))
              (Eq pp_unary_ty (Var 2) (Var 1))))))"

lemma typed_pp_QSS:
  "[] \<turnstile> pp_QSS : Prop"
  by (rule infer_type_sound)
    (simp add: pp_QSS_def pp_unary_ty_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def lookup_def)

definition pp_T3_axioms :: "oterm set" where
  "pp_T3_axioms =
    pp_T6_core_PP_axioms \<union> pp_persistence_schema \<union> {pp_QSS}"

lemma pp_persistence_schema_typed_T3:
  assumes "A \<in> pp_persistence_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_persistence
  unfolding pp_persistence_schema_def by blast

lemma pp_T3_axioms_typed:
  assumes "A \<in> pp_T3_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed pp_application_closure_schema_typed
    typed_pp_target_PP pp_persistence_schema_typed_T3 typed_pp_QSS
  unfolding pp_T3_axioms_def pp_T6_core_PP_axioms_def
  by blast

definition pp_T3_heredity :: oterm where
  "pp_T3_heredity =
    Forall Prop
      (Imp
        (\<diamond>\<^sub>o (pp_fun Prop (Var 0)))
        (pp_fun_prime (Var 0)))"

lemma typed_pp_T3_heredity:
  "[] \<turnstile> pp_T3_heredity : Prop"
  unfolding pp_T3_heredity_def
  by (intro has_type.Forall has_type.Imp typed_ObjDiamond
      typed_pp_fun typed_pp_fun_prime has_type.Var)
    (simp_all add: lookup_def)

text \<open>
  Formal target:

  \<open>[] ; pp_T3_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity\<close>.

  The remaining proof obligation is to internalize Goodman's modal passage
  from possible fundamentality, necessitated QSS, persistent purity, and the
  rigidity of identity to the injectivity clause in \<open>fun\<acute>\<close>.
\<close>

end
