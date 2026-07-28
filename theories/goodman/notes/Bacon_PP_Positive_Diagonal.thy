theory Bacon_PP_Positive_Diagonal
  imports "Higher_Order_Metaphysics_PP.Bacon_PP_Diagonal"
begin

section \<open>The positive diagonal, and a refutation attempt\<close>

text \<open>
  Step two of the agreed plan is a time-boxed attempt to \emph{refute} consistency by
  deriving falsity in the axiom-extension calculus, with first attention to the
  argument-under-\<open>Pure\<close> seam.  This theory reports the attempt.  It did not find a
  contradiction.  What it did find is recorded here, together with a precise account
  of where the two candidate branches stop, which is the other thing a failed
  refutation is supposed to deliver.

  First, an observation about the base camp that reshaped the attempt.  The seam is
  not unexplored: \<open>pp_diagonal_operator\<close> is already \<open>pp_diagonal_builder\<close> applied to
  \<open>Pure\<close>, and \<open>pp_diagonal_builder\<close> abstracts a variable that occurs under the
  classifier argument.  So the existing derivations already run through
  argument-under-\<open>Pure\<close>.  What was missing is its \emph{positive} form.  The existing
  operator is \<open>\<lambda>q. \<not> Pure (K q)\<close>; the negation is what makes it a diagonal, and it is
  also what limits the conclusions to possibility claims.  The operator below drops
  the negation.
\<close>

subsection \<open>The positive diagonal operator\<close>

definition pp_positive_builder :: oterm where
  "pp_positive_builder =
    Lam pp_unary_classifier_ty
      (Lam Prop
        (App (Var 1)
          (App pp_constant_builder (Var 0))))"

definition pp_positive_diagonal :: oterm where
  "pp_positive_diagonal =
    App pp_positive_builder (pp_Pure pp_unary_ty)"

text \<open>
  Read: \<open>pp_positive_diagonal\<close> is \<open>\<lambda>q. Pure (K q)\<close>, the operator sending a
  proposition to the claim that the constant operator with that value is pure.
\<close>

lemma typed_pp_positive_builder:
  "\<Gamma> \<turnstile> pp_positive_builder :
    pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_positive_builder_def pp_constant_builder_def
      pp_unary_classifier_ty_def pp_unary_ty_def lookup_def)

lemma typed_pp_positive_diagonal:
  "\<Gamma> \<turnstile> pp_positive_diagonal : pp_unary_ty"
  unfolding pp_positive_diagonal_def
  using typed_pp_positive_builder
    typed_pp_Pure[of \<Gamma> pp_unary_ty]
  unfolding pp_unary_classifier_ty_def
  by (rule has_type.App)

subsection \<open>It lies in the pure stock\<close>

text \<open>
  The builder is a closed term with no constants, so the purity schema applies to it
  directly.  \<open>Pure\<close> is pure by the target instance.  One application of application
  closure then puts the positive diagonal into the pure stock.  This is the seam:
  a pure unary operator whose argument occurs under a \<open>Pure\<close>.
\<close>

lemma pp_positive_builder_purity_axiom:
  "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_positive_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_positive_builder :
      pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_positive_builder)
  show "consts_of pp_positive_builder = {}"
    by (simp add: pp_positive_builder_def pp_constant_builder_def)
  show "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_positive_builder =
      pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_positive_builder"
    by simp
qed

theorem pp_positive_diagonal_pure_recombination:
  "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_positive_diagonal"
proof -
  have builder_axiom:
    "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_positive_builder
      \<in> pp_recombination_PP_axioms"
    using pp_positive_builder_purity_axiom
    by (rule pp_purity_axiom_in_recombination)
  have builder_pure:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_positive_builder"
    using builder_axiom
      typed_pp_pure[OF typed_pp_positive_builder, of \<Gamma>]
    by (rule CEV_axiom_proves.Axiom)
  have classifier_pure:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_classifier_ty (pp_Pure pp_unary_ty)"
  proof -
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def
          pp_Pure_def pp_unary_ty_def lookup_def)
    have target:
      "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using pp_target_in_recombination target_type
      by (rule CEV_axiom_proves.Axiom)
    show ?thesis
      using target
      by (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_unary_classifier_ty_def pp_unary_ty_def)
  qed
  have closure:
    "pp_application_closure pp_unary_classifier_ty pp_unary_ty
      \<in> pp_recombination_PP_axioms"
    by (rule pp_application_closure_in_recombination)
  have classifier_type:
    "\<Gamma> \<turnstile> pp_Pure pp_unary_ty : pp_unary_classifier_ty"
    using typed_pp_Pure[of \<Gamma> pp_unary_ty]
    unfolding pp_unary_classifier_ty_def .
  show ?thesis
    unfolding pp_positive_diagonal_def
    using closure
      typed_pp_positive_builder[of \<Gamma>]
      classifier_type
      builder_pure classifier_pure
    by (rule pp_axiom_application_closed)
qed

corollary pp_positive_diagonal_pure_full_QLN:
  "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_positive_diagonal"
  using pp_positive_diagonal_pure_recombination
    pp_recombination_PP_axioms_subset_full_QLN
  by (rule CEV_axiom_proves_mono)

subsection \<open>Its Recombination instance\<close>

lemma pp_positive_diagonal_recombination_instance:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty pp_positive_diagonal)
        (pp_fun Prop R))
      (Imp
        (\<box>\<^sub>o (App pp_positive_diagonal R))
        (Forall Prop
          (App (shift pp_positive_diagonal) (Var 0))))"
proof -
  have qln_type: "\<Gamma> \<turnstile> pp_unary_recombination : Prop"
    by (rule infer_type_sound)
      (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d_qln:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_unary_recombination"
    using pp_unary_recombination_in_recombination qln_type
    by (rule CEV_axiom_proves.Axiom)
  have diagonal_type_raw:
    "\<Gamma> \<turnstile> pp_positive_diagonal : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_positive_diagonal[of \<Gamma>]
    unfolding pp_unary_ty_def .
  have d_outer_raw:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      subst0 pp_positive_diagonal
        (Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
              (pp_fun Prop (Var 0)))
            (Imp
              (\<box>\<^sub>o (App (Var 1) (Var 0)))
              (Forall Prop (App (Var 2) (Var 0))))))"
  proof (rule CEV_axiom_UI_typed)
    show "\<Gamma> \<turnstile>
        Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              (Imp
                (\<box>\<^sub>o (App (Var 1) (Var 0)))
                (Forall Prop (App (Var 2) (Var 0)))))) : Prop"
      using qln_type unfolding pp_unary_recombination_def .
  next
    show "\<Gamma> \<turnstile> pp_positive_diagonal : Prop \<rightarrow>\<^sub>o Prop"
      by (rule diagonal_type_raw)
  next
    show "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              (Imp
                (\<box>\<^sub>o (App (Var 1) (Var 0)))
                (Forall Prop (App (Var 2) (Var 0))))))"
      using d_qln unfolding pp_unary_recombination_def .
  qed
  have d_outer:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_positive_diagonal)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_positive_diagonal (Var 0)))
            (Forall Prop
              (App (shift pp_positive_diagonal) (Var 0)))))"
    using d_outer_raw
    by (simp add: pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def subst0_def shift_def
        pp_positive_diagonal_def pp_positive_builder_def
        pp_constant_builder_def pp_unary_classifier_ty_def
        One_nat_def numeral_2_eq_2)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_positive_diagonal)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_positive_diagonal (Var 0)))
            (Forall Prop
              (App (shift pp_positive_diagonal) (Var 0))))) : Prop"
    using CEV_axiom_proves_formula[OF d_outer] .
  have d_inner_raw:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      subst0 R
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_positive_diagonal)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_positive_diagonal (Var 0)))
            (Forall Prop
              (App (shift pp_positive_diagonal) (Var 0)))))"
    using outer_type R_type d_outer by (rule CEV_axiom_UI_typed)
  show ?thesis
    using d_inner_raw
    by (simp add: pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def subst0_def shift_def
        pp_positive_diagonal_def pp_positive_builder_def
        pp_constant_builder_def pp_unary_classifier_ty_def)
qed

subsection \<open>Where the refutation stops\<close>

text \<open>
  With the positive diagonal in the pure stock, unary Recombination applies to it at
  the fundamental proposition \<open>R\<close>, giving

  \begin{center}
  \<open>\<box> (Pure (K R))  \<longrightarrow>  \<forall>q. Pure (K q)\<close>,
  \end{center}

  and the attempt divides into two branches.  Neither closes, and it is worth being
  exact about why, since that is what a failed refutation has to leave behind.

  \emph{Branch one: the consequent holds.}  Suppose every constant operator is pure.
  In the full-QLN set, unary Exhaustion then applies to each \<open>K q\<close> at \<open>R\<close> and yields
  \<open>q \<longrightarrow> \<box>q\<close> for every \<open>q\<close> --- modal collapse.  That is a striking consequence but it
  is not a contradiction: collapse is satisfied by any one-world structure, and
  nothing in the axiom set asserts that some proposition is contingent.  The base
  camp's \<open>pp_fundamental_forces_diagonal_nonnecessity\<close> does not help, because under
  collapse it reduces to \<open>\<not> \<not> Pure (K R)\<close>, which is consistent with branch one rather
  than against it.  To close this branch one would have to derive contingency from the
  background, and no such derivation is available: the axioms constrain purity and
  fundamentality, not the modal profile of arbitrary propositions.

  \emph{Branch two: the antecedent fails.}  Then \<open>\<not> \<box> (Pure (K R))\<close>, that is
  \<open>\<diamond> \<not> Pure (K R)\<close>.  The base camp independently gives
  \<open>\<diamond> Pure (K R)\<close> (\<open>pp_fundamental_forces_possible_constant_purity\<close>), so together
  these say only that \<open>Pure (K R)\<close> is contingent.  That is consistent.  Adding the
  persistence schema \<open>Pure(x) \<longrightarrow> \<box> Pure(x)\<close> --- which the repository defines but which
  belongs to \<open>pp_full_QLN_PP_persistence_axioms\<close>, not to the sets at issue --- turns
  branch two into \<open>\<not> Pure (K R)\<close>, still consistent with a mere possibility claim.

  \emph{The missing principle, named exactly.}  Both branches would close if the
  calculus proved a Brouwerian or 5 principle, since \<open>\<diamond> Pure (K R)\<close> plus persistence
  would then deliver \<open>\<box> Pure (K R)\<close> and fire Recombination.  The modal theory stated
  in \<open>Bacon_Modal\<close> is K, T and 4 only; no 5 or B principle is stated or derived
  anywhere in the development.  Whether CEV \emph{proves} one is not settled here, and
  it is worth settling, because it cuts both ways: if CEV proves 5, this refutation
  branch may close \emph{and} the word-action model fails the background modelhood
  obligation, since \<open>pp_sem_box\<close> is S4 but not S5 --- its \<open>\<box>\<close>-images are up-closed
  under the accessibility order, and the complement of an up-closed set is not
  up-closed unless it is trivial.  That single question therefore bears on both the
  refutation and the model programme, and it is the natural next thing to decide.

  \emph{What was not tried.}  The search here was confined to operators of type
  \<open>Prop \<rightarrow> Prop\<close> built from \<open>Pure\<close> and the constant builder.  It did not attempt
  operators at higher types, iterated \<open>Pure\<close>, or joint use of the
  no-other-fundamentals schema, and it made no use of the unique-fundamentality axiom
  beyond what the base camp already extracts.  A negative result here is therefore
  weak evidence, and should not be read as raising the consistency credence by much.
\<close>

end
