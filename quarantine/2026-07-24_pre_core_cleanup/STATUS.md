# Formalization Status

This file separates verified Isabelle results from conditional interfaces and
remaining paper-level obligations. The status below is for release `v0.1.0`
under Isabelle2025-2.

## Verified foundations

- A deep embedding of the Bacon-style typed object language, including de
  Bruijn syntax, typing, renaming, substitution, and beta-eta conversion.
- Hilbert systems `H`, `C`, `CE`, and `CEV`, with formula preservation.
- Restricted necessitation for the weaker systems and unrestricted
  necessitation for `CEV` through theorem-to-truth equivalence.
- The `CEV` modal `K`, `T`, and `4` schemata, packaged as `CEV_S4_package`.
- Full `H` soundness for `valid_in_context`, with relative soundness results
  for `C`, `CE`, and `CEV` in the corresponding semantic locales.

## Completeness

- `H` and `C` have verified Henkin and substitutional term-model completeness
  results, including `H_Henkin_valid_in_context_iff_proves`,
  `C_Henkin_valid_in_context_iff_proves`,
  `H_term_model_valid_iff_proves`, `C_term_model_valid_iff_proves`, and the
  corresponding strong-completeness theorems.
- Completeness for the earlier general `valid_in_context` interface remains
  conditional on its stated countermodel properties.
- `CEV` now has unconditional canonical completeness:
  `CEV_Henkin_valid_in_context_iff_proves` and
  `CEV_term_model_valid_iff_proves`. The proof includes verified
  prefix-equivalence internalization, theory-relative conservativity of the
  auxiliary context-equivalence calculus, and
  `CEV_context_equiv_abstract_const_admissible_holds`.
- `CEV_Henkin_extension_exists` gives the theory-relative model-existence
  bridge for every typed CEV-consistent theory whose constant vocabulary is
  finite. The theory itself may be infinite.

## Purity of Pure consistency project

- `Bacon_PP.thy` formalizes type-indexed `Pure` and `Fun`, ordinary
  constant-free logical Purity, application closure, target PP at the
  `(t -> t)` level, Persistence, unique fundamentality, the relevant
  zero-ary and unary Recombination/Exhaustion/QLN principles, and QSS.
- `pp_full_QLN_axioms` is the target theory without Purity of Fun.
  `pp_purity_of_fun_not_in_full_QLN` verifies that exclusion, and
  `pp_consistency_question` states its `CEV` consistency.
- `pp_negative_answer_iff_derives_contradiction` makes the negative target
  exact: a negative answer is equivalent, by definition of syntactic
  consistency, to deriving `ObjFalse` from `pp_full_QLN_axioms`.
- `pp_negative_answer_iff_finite_inconsistent_core` proves that any negative
  answer has a finite inconsistent subtheory, and conversely.
- `pp_consistency_iff_Henkin_model_exists` closes the corresponding semantic
  bridge: PP consistency is equivalent to the existence of a CEV Henkin
  theory/model containing all the target axioms. The finite-vocabulary side
  condition is verified for the infinite PP schemas.
- `pp_Henkin_model_exists_iff_finitely_consistent` reduces construction to
  consistency of every finite target subtheory.
  `pp_finite_fragments_construct_term_model` defines the resulting chosen
  canonical Henkin term model and proves that it satisfies every target axiom
  and does not satisfy `ObjFalse`, conditional on that finite-fragment
  obligation.
- `pp_consistency_from_concrete_model` gives the complementary direct semantic
  route suggested by Bacon's Chapters 15, 17, and 18. In any concrete
  `vector_equivalence_structure`, validity of every target axiom proves PP
  consistency. The supporting theorem `CEV_set_derivable_sound` proves
  assumption-set soundness, and `ObjFalse_not_valid` verifies the required
  nontriviality of every such semantic structure.
- `Bacon_PP_Action_Model.thy` constructs and verifies the algebraic base of
  Bacon's model route: the finite-word monoid, the right-division action on
  propositions, surjectivity of each division map, and a concrete generic
  proposition with an injective substitution orbit.
- `bacon_full_invariance_QSS_collision` proves that genericity does not suffice
  for QSS. Two distinct equivariant unary operators agree at the generic
  proposition. Thus interpreting every invariant as pure is formally ruled
  out, rather than merely suspected.
- `bacon_certified_purity_seed` is a lower-type diagnostic. It certifies
  `Pure_Prop`, which represents `Pure(Pure_Prop)`, not the target
  `Pure(Pure_{Prop->Prop})`. This distinction is now explicit in the formal
  model layer.
- `bacon_logical_unary_core_package` verifies the ordinary constant-free unary
  logical core: identity, complement, constant truth, and constant falsity are
  equivariant, preserve the certified extreme propositions, satisfy unary QLN
  at every word/world, and satisfy QSS at the generic proposition.
- `bacon_lower_PP_unary_core_package` proves that adjoining and certifying
  `Pure_Prop` preserves equivariance, application closure, and world-indexed
  QLN but destroys QSS: `Pure_Prop` and constant falsity agree at the generic
  proposition. This refutes only the stronger lower-type PP extension, not the
  target conjecture.
- `bacon_typed_target_PP_seed_package` introduces the correctly typed unary
  classifier `Pure_{Prop->Prop}`, certifies that classifier at the next level,
  and verifies the two adjacent application-closure instances and invariant
  classifier outputs.
- `bacon_boolean_target_PP_package` extends the target classifier level to all
  truth-valued characteristic classifiers. It contains
  `Pure_{Prop->Prop}`, is closed under application to unary operators, has
  invariant outputs, and is closed under classifier complement, conjunction,
  and disjunction.
- `bacon_PP_diagonal_not_unary_QLN_valid` identifies the first exact failure of
  this concrete seed. PP and application closure force
  `F(P) = not Pure(K P)` to be pure, but the current generic proposition has
  no extreme view, so `F(r) = UNIV`; unary QLN fails for `F`. This rules out
  the present seed, not the abstract PP theory.
- `bacon_QLN_forces_diagonal_transition` and
  `bacon_QLN_forces_nonactual_transition_world` isolate the repair condition:
  if the diagonal is actually true and unary QLN holds, its underlying purity
  proposition must be actually false but nonempty. Thus some nonactual
  substitution must make the relevant `Pure(K r)` claim true.
- `bacon_faithful_orbit_views_nonextreme` proves that every quotient of a
  proposition with an injective word orbit is nonempty and nonuniversal.
  Therefore the required nonactual `Pure(K r)` transition cannot be obtained
  by letting a view of `r` become an extreme pure proposition.
- `bacon_minimal_nonactual_constant_transition` constructs the tempting
  alternative explicitly. It selects a nonempty word `i`, leaves `i dot r`
  nonextreme, certifies `K(i dot r)`, preserves QSS at `r`, and makes the
  resulting diagonal satisfy actual-world unary QLN. The induced classifier is
  equivariant.
- This alternative is not a full model step.
  `bacon_application_closure_for_constant_forces_value` proves in general that
  application closure transfers purity from a constant operator to its value
  as soon as any pure proposition is available.
  `bacon_transition_stock_not_application_closed` verifies the resulting
  failure for the explicit transition stock.
  `bacon_zeroary_QLN_and_complement_closure_force_extreme` strengthens the
  diagnosis: in the word model, zero-ary QLN and logical complement closure
  force every pure proposition to be empty or universal.
- `bacon_identity_QLN_valid_forces_no_universal_view` and
  `bacon_complement_QLN_valid_forces_no_empty_view` show the opposing
  constraint imposed by world-indexed unary QLN for the logically pure
  identity and complement operators. Every substitution view of the
  fundamental proposition must be nonextreme.
  `bacon_word_action_constant_transition_no_go` combines the two sides: no
  right-division powerset action model can realize the required certified
  constant-operator transition while also satisfying application closure,
  zero-ary QLN, complement closure, and world-indexed unary QLN for identity
  and complement. This no-go theorem does not prove the abstract theory
  inconsistent; it rules out the current concrete semantic architecture.
- `pp_action_model_obligations` and
  `pp_consistency_from_action_model_obligations` factor the final model check
  into the exact purity-schema, application-closure, PP, fundamentality, and
  QLN validity obligations and connect their satisfaction to
  `pp_consistency_question`.
- `pp_full_QLN_derives_pure_F` verifies the decisive diagonal step:
  PP, ordinary logical Purity, and application closure derive `Pure(F)` for
  `F(p) = not Pure(K_p)`.
- `pp_full_QLN_derives_not_F_true` and
  `pp_full_QLN_derives_not_F_universal` verify `not F(true)` and
  `not (forall p. F(p))`. For the exact full-QLN theory with a named
  fundamental witness, `pp_QLN_r_derives_not_box_F` derives
  `not box F(r)` directly from the QLN biconditional.
- The QSS audit layer proves `not (r = true)`, `not Pure(K_r)`, and `F(r)`.
  The pointwise repair is stronger: the corresponding theorems over
  `pp_unary_recombination_r_axioms` derive all three from the core axioms,
  unary Recombination, and a named fundamental `r`, without assuming QSS.
  `pp_named_r_boomerang` lifts this result to the full named-r QLN package and
  proves `F(r) and not box F(r)` unconditionally.
- `CEV_proves_subst_const` proves theoremhood is closed under typed
  substitution for the full vector/zeta system. Conditional on the stated
  noncollapse hypotheses, `no_pure_rep_Kr` and
  `no_pure_rep_singleton_fun_role` establish the generic impurity tests for
  `K_r` and the singleton fundamental-role predicate.
- Neither `pp_consistency_question` nor its negation has been proved. The
  direct QSS and strict-Recombination routes to `F(r)` are complete, but do not
  yield a contradiction: QLN already derives `not box F(r)`, and local theory
  derivability does not license necessitation. The pointwise proof bypasses,
  rather than repairs, the printed Recombination-to-QSS boxing gap. The
  decisive remaining target is a full consistency/model construction or a
  valid independent derivation of `box F(r)` (or another contradiction). The
  word-action base, unary logical core, and correctly typed target-PP seed now
  exist, but they are not yet a complete typed applicative model. The live
  positive route can no longer use the present right-division powerset
  semantics: dropping faithfulness alone does not evade
  `bacon_word_action_constant_transition_no_go`. A successful model must alter
  the proposition domain or its action/boxing realization while retaining the
  verified algebraic and typed constraints. It must then extend through every
  simple type so that the
  certified subcollection contains all denotations of closed constant-free
  logical terms and the denotation of `Pure` itself, excludes `Fun`, is closed under
  application, and preserves zero/unary QLN. QSS/injectivity remains an
  optional stronger target, not an axiom of the present consistency question.

## Caie application

- Caie's Appendix C formulas 32--40 are represented in the deep embedding.
- None of the nine theorem statements follows by definition and beta-eta
  conversion alone. The four definitional bridges are verified separately.
- Every Appendix C target is locally derivable from the explicit
  `caie_appendix_C_axiom_package`. The closure is recorded by
  `caie_appendix_C_axiom_package_closes_targets_from_verified` and the
  source-to-target bridge-pair layer.
- This establishes derivability from the stated package; it does not yet
  reduce every package member to a smallest philosophically natural basis.

## Finite M-star model

- `Bacon_Caie_Mstar.thy` verifies the finite Name, emptiness, rigidity,
  coverage, and plenitude claims collected in
  `Mstar_proposition29_finite_bullets`.
- Proposition 29's theorem-truth bullet is currently conditional. The theorem
  `Mstar_proposition29_from_NDS_soundness` requires both
  `nds_background_soundness` and `mstar_nds_model_obligation`.

## Remaining milestones

1. Extend `bacon_typed_target_PP_seed_package` to a typed applicative
   substitution structure in a semantic architecture not covered by
   `bacon_word_action_constant_transition_no_go`. The immediate design target
   is an alternative proposition domain or action/boxing interpretation that
   makes `Pure(K r)` false at the actual world and true at a nonactual
   substitution, as required by
   `bacon_QLN_forces_nonactual_transition_world`, without identifying pure
   propositions with the two absorbing powerset extremes. Then iterate through
   all simple types, interpret `Pure` at every type, and preserve zero/unary
   QLN. QSS and orbit injectivity are not axioms of the exact target and should
   not constrain this first consistency model.
   Discharging
   `pp_action_model_obligations` then proves consistency. Alternatively derive
   `ObjFalse` from a finite PP/QLN core; the QSS and strict-Recombination
   `F(r)` routes are already complete.
2. Formalize and prove the NDS-model soundness result corresponding to Caie's
   Proposition 27.
3. Connect the finite M-star structure to the deep NDS semantics by proving
   `mstar_nds_model_obligation`.
4. Further decompose the Caie counterfactual and name principles where a
   smaller philosophically natural basis is available.
