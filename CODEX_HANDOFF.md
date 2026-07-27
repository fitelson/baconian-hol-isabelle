# Handoff: Goodman's PP consistency problem

## 0. New live checkpoint: the enumerator problem is one absorption fixed point

Two further theories are now included in
`Higher_Order_Metaphysics_PP_ZF_Model`:

- `zf_model/Bacon_PP_ZF_Tree_Range_Diagonal.thy`; and
- `zf_model/Bacon_PP_ZF_Tree_Range_Term_Basis.thy`.

The first proves that root PER equivalence is literal equality at every
object type (`pp_t_root_eqv_imp_eq`, `pp_t_root_eqv_iff_eq`).  Hence the
root basis stock is literally `D`, the root range stock is literally the
value set of `E`, and
`pp_t_range_complete_all_worlds_iff_root` proves that root
range-completeness is equivalent to all-world range-completeness.
`pp_t_range_complete_all_worlds_iff_exact_range` gives the exact raw-set
form:

```isabelle
D pp_t_unary_type =
  (\<lambda>n. E \<acute> n) ` {n. Elem n (pp_t_domain Ind)}.
```

This corrects the earlier warning below: future-world lifting is not an
additional premise once root exactness is used.

The diagonal file also isolates the strongest internal Cantor obstruction.
`pp_t_range_complete_basis_has_no_reflecting_map` rules out a stock member
`P : Ind \<rightarrow>\<^sub>o Prop` whose code equality reflects equality of
the corresponding `E`-values; injective codes are a corollary.  This is not
an unconditional refutation.  `pp_t_cone_invariant_prop_collapse` and
`pp_t_basis_ind_prop_value_collapse` prove that cone-natural stock
propositions are truth or falsity and stock-internal index codes are
two-valued.  The logical basis therefore does not generate the bridge the
diagonal needs.  At the external level,
`pp_b_generic_separator_for_countable_stock` is now checked for arbitrary
countable cone-equivariant unary stocks.

The term-basis theory supplies the promised explicit reduction.  For every
typed cone-natural candidate enumerator `E`,
`pp_t_enumerator_basis E` consists of finite applicative expressions over
all closed logical denotations, every natural individual, and `E`.
`pp_t_cone_natural_enumerator` proves that this is a
`pp_t_stock_basis`; it is countable, typed, cone-natural, includes every
logical denotation and every member of `Nat`, is application-closed, and
contains `E`.  The exact remaining theorem is
`pp_t_term_basis_range_complete_iff_fixed_point`: range-completeness holds
iff the unary part of this basis is exactly the raw value set of `E`.
`pp_t_term_basis_self_classifies_from_fixed_point` then supplies the PP
self-classifier.

Thus neither an enumerator nor an impossibility theorem has been obtained.
The sole open mathematical content is the absorption fixed point:

```isabelle
pp_t_enumerator_basis E pp_t_unary_type =
  (\<lambda>n. E \<acute> n) ` {n. Elem n (pp_t_domain Ind)}.
```

Do not restart generic basis or PER-lifting work.  The next attack must
construct this fixed point by homogeneity/genericity or refute it using a
new invariant of countable cone-equivariant operator algebras.  The standard
typed Cantor diagonal and naive stage iteration are now known not to settle
it.  The detailed joint record is
`reports/IND_ENUMERATOR_FRONTIER_2026-07-26.md`; Claude's independent audit
is `reports/CLAUDE_IND_ENUMERATOR_CONSULT_2026-07-26.md`.

The focused ZF session passes after the completed changes.

## 0. New live checkpoint: the sufficient-basis theorem and range criterion are checked

Two new theories are included in `Higher_Order_Metaphysics_PP_ZF_Model`.

### Uniform seeded-stock semantics

`zf_model/Bacon_PP_ZF_Tree_Seeded_Stock.thy` defines the locale
`pp_t_seeded_stock`.  Its hypotheses isolate the exact semantic data used by
the generic model: an admissible persistent stock, a typed world-indexed seed
that recombines the unary stock, logical-term containment, and application
closure.

Inside the locale Isabelle proves:

- typed interpretations of `Pure` and `Fun`;
- unique fundamentality at `Prop` and no fundamentals at every other type;
- every logical-purity and application-closure schema instance;
- zeroary and unary Recombination;
- `pp_t_seeded_recombination_background_gvalid`;
- `pp_t_seeded_recombination_PP_gvalid_iff`; and
- the root reduction
  `pp_t_seeded_recombination_PP_gvalid_iff_root`.

The locale `pp_t_stock_basis` is then instantiated by selecting the generic
root seed already constructed in `Bacon_PP_ZF_Tree_Basis_Stock` and
transporting it by cone lift.  The inherited aliases
`pp_t_basis_recombination_background_gvalid`,
`pp_t_basis_recombination_PP_gvalid_iff`, and
`pp_t_basis_recombination_PP_gvalid_iff_root` are the checked
sufficient-basis results.  The full PP theory for a basis is equivalent to
one root membership fact for that basis's unary classifier.

### `Ind`-indexed range classifier

`zf_model/Bacon_PP_ZF_Tree_Range_Classifier.thy` defines the closed logical
term

```isabelle
pp_range_classifier_builder :
  (Ind \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop))
    \<rightarrow>\<^sub>o ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop).
```

For every typed enumerator `E`, the theorem
`pp_t_range_classifier_builder_correct` proves that applying this term to
`E` is higher-order PER-equivalent to the classifier of the world-relative
equivalence saturation of `range E`.  This explicitly verifies the crucial
world-relative `Eq` semantics.

The sharp construction theorem is
`pp_t_range_complete_basis_self_classifies`.  If:

1. `E` belongs to the basis stock at its enumerator type; and
2. at **every world**, the unary basis stock equals the saturated range of
   `E`,

then the basis stock contains its own unary-stock classifier at the root.
Logicality of the builder plus application closure supplies the classifier
element; the theorem itself uses all-world equality to lift the computed
range classifier under the higher-order PER.  The later theorem
`pp_t_range_complete_all_worlds_iff_root` now supplies the previously missing
lifting theorem, so root range-completeness is sufficient in this model.

The focused ZF session and full project build pass; the two new theories have
no proof escapes and `git diff --check` is clean.

**Next exact move:** construct or refute a typed
`E : Ind \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)` together with
a countable cone-natural application-closed basis whose unary saturation is
the saturated range of `E` at every world.  A useful first attack is to
formalize an explicit metasyntactic enumeration of terms over one
enumerator constant, include all `Nat` indices in the `Ind` basis, and reduce
range completeness to a single range-level fixed-point equation.  Keep the
one-step `D1` unary-stabilization route as the parallel fallback.

## 0. New live checkpoint: the abstract basis and generic seed are checked

`zf_model/Bacon_PP_ZF_Tree_Basis_Stock.thy` is now the live frontier and is
included in `Higher_Order_Metaphysics_PP_ZF_Model`.

- `pp_t_basis_stock D σ w x` is the local-identity saturation of a
  type-indexed basis `D`.
- `pp_t_stock_basis` assumes basis typedness, countability, cone naturality,
  inclusion of every closed logical denotation, and application closure up
  to root equivalence.
- The saturation is proved typed, admissible, persistent, all-worlds iff
  root, closed under application, and exactly transportable through cones.
  Its characteristic classifier is cone-natural.
- `pp_t_generic_seed_recombines_basis_stock_at_root` generalizes the
  countable generic-witness construction from exact logical denotations to
  every basis satisfying the locale.
- `pp_t_basis_root_recombination_transports_to_cone` and
  `pp_t_basis_generic_seed_at_every_world` prove that one typed root seed has
  cone lifts satisfying unary Recombination at every corresponding world.
- `ClosedLogicalBasis` machine-checks every locale assumption for the basis
  of closed logical denotations.
  `pp_t_basis_stock_closed_logical_basis` proves its saturation equals
  `pp_t_closed_logical_stock`, so the abstraction conservatively recovers the
  previous construction.
- Both `isabelle build -D . Higher_Order_Metaphysics_PP_ZF_Model` and
  `isabelle build -D .` pass; the edited ZF theories contain no proof
  escapes.
- Next: define a uniform seeded-stock internal interpretation over this
  locale, validate the complete Recombination background, and prove
  `pp_t_basis_recombination_PP_gvalid_iff_root`.  Do not start either the
  `D1` or `Ind`-enumerator instantiation before this sufficient-basis theorem
  exists.

## 0. New live checkpoint: the entire Recombination background has a model

`zf_model/Bacon_PP_ZF_Tree_Generic_Seed.thy` remains the live frontier.

- The generic root seed is selected by `pp_t_generic_root_seed`, transported
  to each world by `pp_t_generic_seed_at`, and proved to satisfy exact-stock
  unary Recombination at every world.
- `pp_t_generic_internal_constants` interprets `Pure` by the exact
  closed-logical stock and `Fun` by the local identity class of the
  transported generic seed.
- The interpretation proves global unique fundamentality at `Prop`, no
  fundamentals at every other type, every closed-logical purity axiom, every
  application-closure axiom, zeroary Recombination, and unary Recombination.
  The bundled result is
  `pp_t_generic_recombination_background_gvalid`.
- `pp_t_generic_target_PP_holds_iff` reduces PP to the claim that the
  classifier of the exact closed-logical unary stock belongs to the
  next-type exact closed-logical stock.
- `pp_t_generic_recombination_PP_gvalid_iff` proves that this is the only
  remaining condition for global validity of
  `pp_recombination_PP_axioms`.
- Stock membership is persistent, so
  `pp_t_closed_logical_stock_all_worlds_iff_root` and
  `pp_t_generic_recombination_PP_gvalid_iff_root` reduce the residual
  condition to one root membership fact.
- The supporting naturality package is checked:
  `pp_t_closed_logical_prop_den_root_truth`,
  `pp_t_cone_invariant_eqv_root_iff`,
  `pp_t_closed_logical_stock_cone_iff`, and
  `pp_t_closed_logical_classifier_cone_related`.
- Do not describe this as a PP model yet.  Neither membership nor
  nonmembership of the classifier in the exact stock is proved.
- The next construction should first define a countable typed basis `D` and
  its local-equivalence saturation, then prove a sufficient-basis theorem:
  typedness, countability, cone naturality, inclusion of all closed logical
  denotations, application closure up to root equivalence, and root
  self-classification suffice for a full model.  After that, test two
  instantiations: the one-step basis generated by the old classifier, and an
  `Ind`-indexed range-complete basis with `Nat` explicitly included in its
  `Ind` component.
- The `Ind`-indexed route remains live because identity at `Ind` is rigid
  equality and the object language can define the world-relative classifier
  of an enumerator's range.  Its correct self-classification criterion needs
  (i) a theorem lifting root range-completeness to all worlds and (ii)
  membership of the closed logical range-classifier builder.  Application
  closure alone supplies neither premise in an arbitrary basis.
- Merely adjoining the old classifier is circularly insufficient.
  Application closure creates new unary operators; PP for the enlarged stock
  concerns the new classifier.  Unary-fragment stabilization would suffice,
  but it is an open obligation, and the singleton-test construction is only
  a one-sided obstruction probe, not a complete characterization.
- The Claude/Codex audit is
  `reports/CONSENSUS_PP_CLASSIFIER_FRONTIER_2026-07-26.md`, with checkpoints
  in the adjacent `..._PROGRESS_...` file.  The parties agreed on the checked
  frontier and the “basis theorem first” strategy.  The runner's final
  no-consensus status records the two missing premises in the proposed
  range-complete corollary; it is not disagreement about the main route.

## 0. New live checkpoint: all-type cone gluing is complete

`zf_model/Bacon_PP_ZF_Tree_Generic_Seed.thy` is now the live frontier.

- The Boolean reserved-cone diagonal construction is machine-checked for
  every countable stock of cone-equivariant unary proposition operators.
- The exact stock of closed, typed, constant-free unary denotations is
  countable.
- Exact semantic correspondences and equivariance are proved for the three
  operators that killed earlier candidates: `λq.¬□q`, `λq.◇□q`, and the
  settling operator `λq.(◇□q ∨ ◇□¬q)`.  One generic seed handles all three.
- `pp_t_cone_rel` is the type-indexed logical relation between the whole tree
  and a cone.  Full constant-free term parametricity was already conditional
  on two-sided cone totality; that condition is now proved.
- The outside-cone obstruction is solved by
  `pp_t_sibling_component`: two values lie in the same component when they
  admit a common bridge on the two immediate sibling cones.  It is literal
  equality at `Ind`, universal at `Prop`, and preserved by application.
  The recursive merge theorem
  `pp_t_sibling_component_iff_logical` proves that this bridge relation is
  exactly its induced higher-order logical relation.
- `pp_t_support_rel` combines three cases: ordinary local equality inside
  the support cone, root equality above it, and sibling-component equality
  on incomparable cones.  `pp_t_support_rel_app` proves the resulting
  higher-order application law.
- `pp_t_cone_transform_invariant_all` is the simultaneous all-type induction.
  It proves typed-domain closure and congruence for both mutually recursive
  transformations, `pp_t_cone_restrict` and `pp_t_cone_extend`.
- `pp_t_cone_canonical_invariant_all` proves that these transformations
  actually realize `pp_t_cone_rel`.  The extracted theorems
  `pp_t_cone_left_total_all`, `pp_t_cone_right_total_all`, and
  `pp_t_cone_compatible_all` hold for every object type and every cone.
- `UnconditionalCone` instantiates the old `pp_t_cone_totality` locale.
  Therefore
  `pp_t_generic_seed_recombines_exact_closed_logical_stock` is now an
  unconditional theorem: one typed proposition satisfies root unary
  Recombination for the full exact closed-logical stock.
- Next: transport the root generic seed to each world by cone lift; interpret
  `Fun_Prop` as the local identity class of that transported seed; prove
  global unique fundamentality, no fundamentals at other types, and global
  closed-logical Recombination.  Once that repaired central stock is in the
  actual internal model, attack PP itself.

## 0. New live checkpoint: the moving-seed tree route is refuted

`zf_model/Bacon_PP_ZF_Tree_Logical_Stock.thy` is now the live frontier.

- `pp_t_closed_logical_stock` is the local-identity closure of every closed,
  well-typed, constant-free denotation.  Isabelle proves admissibility,
  containment of every actual evaluation, leastness among admissible
  containing stocks, and closure under application.
- `pp_t_closed_logical_purity_gvalid` and
  `pp_t_closed_logical_application_closure_gvalid` verify the corresponding
  object-language axiom instances under this `Pure` interpretation.
- The closed logical operator `λq.(◇□q ∨ ◇□¬q)` is in the stock.  The
  true-child-cone fundamental seed eventually settles on every future branch,
  whereas `pp_t_parity_prop`, whose truth alternates with word length, never
  settles on any future cone.
- Consequently the settling operator holds necessarily of the fundamental
  seed but not universally.  The semantic failure is
  `pp_t_closed_logical_stock_not_recombines`; the exact object-language result
  is `pp_t_closed_logical_unary_recombination_not_gvalid`.
- This refutes the present moving-seed tree model before PP is reached.  Do
  not spend time trying to prove PP for this interpretation as a central-stock
  witness.
- Preserve the Boolean-tree HOL-ZF domains, evaluator, and
  `henkin_action_model` instance.  The next positive route is to replace the
  seed by a logically generic proposition whose future copies realize every
  proposition behavior relevant to closed logical operators.  The matching
  negative route is a theorem that no such generic seed is compatible with
  unique fundamentality on the prefix frame.

## 0. Live checkpoint: branching HOL-ZF model scaffold is active

Codex has resumed as driver.

- `zf_model/Bacon_PP_ZF_Tree_Frame.thy` is now the live positive frontier.
  Finite Boolean words are the semantic worlds, ordered by prefix, and a
  proved bijection with `Nat` supplies the coordinates of `Power Nat`.
  There are no unused or duplicated proposition coordinates.
- The complete typed-domain layer is checked.  `pp_t_domain` and `pp_t_eqv`
  give preconstructed domains and the branching logical relation;
  application closure, persistence, nonemptiness, and all equivalence laws
  hold at every object type.
- The terminating structural evaluator is complete.
  `pp_t_eval_fundamental` proves typing and relational invariance
  simultaneously, including lambdas and both higher-order quantifiers.
  `DefaultTreeConstants.TreeHenkin` is a concrete `henkin_action_model`.
- `pp_t_moving_seed w` is the true-child cone rooted at `w@[True]`.
  `pp_t_moving_internal_parameters` interprets `Fun` as its local identity
  class.  `pp_t_moving_unique_fundamental_gvalid` and
  `pp_t_moving_no_fundamentals_gvalid` discharge the complete fundamentality
  component globally.
- The old directed-frame killers have now been tested inside the actual
  evaluator.  `pp_t_eval_not_box_logical_operator` and
  `pp_t_eval_diamond_box_logical_operator` identify the denotations of the
  closed logical terms `λq.¬□q` and `λq.◇□q` with their semantic
  classifiers.  Their local identity classes form the admissible fragment
  `pp_t_obstruction_pair_pure`.
- `pp_t_moving_obstruction_pair_recombines` proves unary Recombination for
  that entire fragment at every world.  The true branch defeats necessary
  not-box; the incomparable false branch defeats necessary possible-box.
- This is not yet a central-stock model.  **Next exact tranche:** construct
  the admissible closure containing every closed logical denotation and
  closed under application; test global unary Recombination there; then prove
  PP for the closure's classifier.  Base CEV soundness and
  vector-Equivalence come later.
- The natural-number-tail material below is retained as a checked negative
  control and as the source of the abstract directedness no-go.
- The structural evaluator tranche is complete.
  `pp_h_eval_fundamental` simultaneously proves type preservation and
  invariance under the world-indexed logical relation, including the lambda
  case.  `pp_h_constants.HHenkin` is therefore a checked
  `henkin_action_model`; do not repeat this work.
- The first internal `Fun` interpretation selected the local identity class of
  one globally fixed proposition `r`.  It validates unique fundamentality and
  every no-other-fundamentals instance, but
  `pp_h_internal_frame_not_central_stock` proves that it cannot validate the
  literal central stock.  The proof uses the actual purity-schema members
  `λq.(q=⊤)` and `λq.¬(q=⊤)` and the actual object-language unary
  Recombination formula.
- This first result was **not** a general inconsistency result.  The central
  axioms require one fundamental identity class at each world, not one fixed
  representative at every world.
- The replacement uses
  `pp_h_moving_seed w = {v | w<v}`.  It is contingent at `w` and necessary
  from `Suc w` onward.  Its world-varying fundamentality predicate is
  admissible, its constants again instantiate `henkin_action_model`, and
  `pp_h_moving_unique_fundamental_gvalid` plus
  `pp_h_moving_no_fundamentals_gvalid` discharge the complete fundamentality
  component.
- `pp_h_box_pair_pure` is an admissible purity fragment consisting of the
  local identity classes of the box and not-box classifiers.
  `pp_h_moving_box_pair_recombines` proves unary Recombination for the whole
  fragment.  This machine-checks only that the moving seed neutralizes the
  original box/complement obstruction.
- The full logical-purity schema closes that route.
  `pp_h_diamond_box_logical_operator = λq.◇□q` is typed, is in the literal
  purity schema, and has exact denotation
  `pp_h_diamond_box_classifier`.
  `pp_h_not_box_diamond_box_block_recombination` proves that, at any world
  and for any typed candidate `p`, unary Recombination is incompatible with
  purity of `λq.¬□q` and `λq.◇□q`.
- The proof splits exhaustively.  If `□p` never becomes true,
  Recombination for `λq.¬□q` makes that operator universal, contradicting
  `q=⊤`.  Otherwise some future world has `□p`; directedness and persistence
  of the natural-number tail then make `◇□p` necessary, so Recombination for
  `λq.◇□q` makes it universal, contradicting `q=⊥`.
- `pp_h_moving_internal_frame_not_central_stock` lifts this semantic
  argument to the exact object-language purity instances and unary
  Recombination member of `pp_recombination_PP_axioms`.  It is independent
  of the choice of admissible `Pure`.  PP and application closure are not
  used.
- `pp_directed_frame_not_box_diamond_box_obstruction` abstracts the proof.
  Any reflexive, transitive frame in which every two futures of a world have
  a common successor has the same problem.  Linearity is stronger than
  needed.
- The first branching replacement test is complete.
  `pp_tree_access` is the prefix order on finite Boolean words;
  `pp_tree_seed w` is the cone rooted at `w@[True]`.
  `pp_tree_split_no_common_successor` proves that the two immediate branches
  never reconverge.  `pp_tree_local_seed_escapes_directed_obstruction`
  proves at every node that the seed falsifies both relevant necessary
  antecedents: `□p` holds on the true branch, while `◇□p` fails everywhere
  on the false branch.
- Therefore `zf_model/Bacon_PP_ZF_Hyper_Frame.thy` is now a checked negative
  control for the natural-tail interpretation, while its abstract definitions
  now also contain the positive tree-frame seed.  The no-go remains
  frame-level, not a proof that Goodman's central stock is inconsistent.
- **Next exact tranche:** lift the Boolean-word prefix frame into the
  preconstructed HOL-ZF semantics.  Parameterize or rebuild proposition
  identity as agreement on accessible extensions, together with arrow
  domains and the structural evaluator, then test the complete closed-logical
  purity fragment against unary Recombination before spending effort on PP,
  application closure, base CEV soundness, or vector-Equivalence.
- Do not search for a `Pure` parameter in
  `Bacon_PP_ZF_Full_Frame.thy`.
  `pp_zf_extensional_identity_blocks_recombination` proves that its rigid
  metalanguage equality is incompatible with logical purity plus unary
  Recombination for every proposed fundamental proposition.  The witnesses are
  the closed logical operators `λq.(q=⊤)` and `λq.¬(q=⊤)`.
- `zf_model/Bacon_PP_ZF_Hyper_Frame.thy` remains the reusable evaluator and
  domain scaffold.  Its domains are preconstructed HOL-ZF sets.  Its identity
  relation `pp_h_eqv` is world-indexed: proposition identity is agreement on
  the future tail, and arrow identity is the induced logical relation.
  Arrow domains contain genuine set-theoretic functions that respect that
  relation at every world.
- The hyperintensional scaffold already proves domain nonemptiness, typed
  application, persistence, and the equivalence laws at every type.
  `pp_h_prop_eqv_truth_iff` identifies `P≈_w⊤` with truth of `P` at every
  future world, giving the intended S4 box while allowing present
  distinctness to disappear.
- `pp_h_eval` is now the structural evaluator over `pp_h_domain`.  Its `Eq`
  clause denotes `{w | pp_h_eqv σ w x y}`, and
  `pp_h_eval_Eq_holds` proves the exact world-level equivalence.  The logical
  and quantifier truth clauses are also proved.
- The earlier evaluator/domain milestone described below is complete; the
  moving-fundamental purity construction above is the live frontier.
- `zf_model/Bacon_PP_ZF_Full_Frame.thy` is retained as the extensional
  negative-control theory.
  Its session `Higher_Order_Metaphysics_PP_ZF_Model` imports Isabelle's
  `HOL-ZF`; all results in that session are explicitly relative to the
  axiomatized ZFC universe supplied there.
- The domains are preconstructed:
  `D(Ind)=Nat`, `D(Prop)=Power Nat`, and
  `D(σ→τ)=Fun (D σ) (D τ)`.  Every domain has a canonical inhabitant.
  Set-theoretic application and lambda abstraction are closed and satisfy beta
  and eta.  The restricted-equality PER has those domains exactly as its
  diagonal, so every PER domain is nonempty.
- `pp_zf_eval` gives structural denotation for every object-language
  constructor.  Quantifier evaluation ranges over the fixed `D σ`; it never
  calls an evaluator through a closure.  Type preservation, renaming, shift,
  all four logical clauses, and nonempty domains instantiate
  `henkin_action_model` as `pp_zf_constants.ZFHenkin`.
- `pp_zf_internal_constants Pure` interprets `Pure_σ` as the characteristic
  function of an explicit type-indexed relation `Pure σ`.  It interprets
  `Fun_Prop` as selecting exactly `Empty` and every other `Fun_σ` as empty.
  The constants are proved typed, and application lemmas reduce object-language
  `Pure(M)` and `Fun(M)` to their corresponding internal predicates.
- Its internal `Pure` search is closed by
  `pp_zf_logical_purity_blocks_recombination`; do not treat its
  `henkin_action_model` interpretation as a candidate central model.
- `frontier/Bacon_PP_Central_Model_Obligations.thy` is the live model theory.
  Its locale `pp_central_stock_model` is the exact positive certificate:
  denotable Henkin semantics, base CEV soundness, vector-Equivalence soundness,
  and global validity of every member of `pp_recombination_PP_axioms`.
  `central_stock_answers_Goodman` converts any interpretation into the desired
  consistency theorem.
- The theory proves that no such central model can validate any complete T6
  stock, using the four existing object-language contradictions.  These are
  diagnostics only; the central stock itself contains none of the T6
  classification principles.
- The orbit-classifier control is now checked in its strongest useful stock
  form.  `pp_orbit_classifier_falsifies_recombination` and
  `pp_all_invariant_operator_indices_fail_recombination` rule out every unary purity
  stock containing the orbit classifier's index.  This formally excludes the
  all-invariant-operators shortcut.
- The universal representation is no longer finite-level:
  `pp_uval` contains word-set propositions and recursively captured typed
  closures at arbitrary object types.  For any proposed application operation,
  `pp_uval_per` defines the type-indexed PER by recursion on `otype`.
  Symmetry, transitivity, tag soundness, and application compatibility are
  proved.  `DefaultClosurePER` supplies a concrete nonempty interpretation of
  the representation contract; it is a non-vacuity control, not the model.
- Do **not** resume the proposed terminating closure evaluator.
  `pp_quantifier_cycle_term_typed`,
  `pp_quantifier_cycle_closure_tagged`, and
  `pp_quantifier_cycle_closure_self_related` formalize the obstruction.
  For `F = λa. ∀P^(Ind→Prop). P a`, tag-correct total application forces
  `F`'s closure into `dom (Ind→Prop)`.  Evaluating `F a` and taking the
  instance `P := F` repeats the identical call.  This is a semantic
  quantifier-instantiation loop, not a beta-reduction loop, so strong
  normalization does not help.
- The evaluator/domain equations are also definitionally nonmonotone:
  quantifier evaluation uses the diagonal of `pp_uval_per app`, while that PER
  is itself defined from `app`.  Fuel, step indexing, and a least fixed point do
  not satisfy the exact classical quantifier biconditional.
- The HOL-ZF preconstructed-domain route was selected explicitly.  It remains
  relative to HOL-ZF's additional assumptions; domains and application predate
  structural denotation throughout.
- Instantiating `henkin_action_model` is not by itself enough to interpret
  `Pure` and `Fun` or prove modelhood.  That locale has no clauses for
  `Const`, `App`, `Lam`, `Eq`, `Conj`, or `Disj`.  The stronger
  `pp_central_stock_model` obligations `central_base_sound`,
  `central_zeta_sound`, and `central_stock_valid` remain essential.
- Claude independently confirmed all of these points.  Detailed report:
  `reports/CLAUDE_CLOSURE_EVALUATOR_CONSULT_2026-07-26.md`; progress log:
  `reports/CLAUDE_CLOSURE_EVALUATOR_CONSULT_PROGRESS_2026-07-26.md`.
  A finite full-function shortcut remains non-viable because the
  higher-order vocabulary can define the orbit/cardinality class of a candidate
  fundamental, recreating the orbit-classifier failure.
- The frontier session builds cleanly after these additions.

## Bridge checkpoint: the Recombination--QSS--T6 result is machine-proved

- `frontier/Bacon_PP_QSS_Recombination_Bridge.thy` proves the precise
  Recombination-only core of Goodman's QSS argument:
  `CEV_QSS_modal_core_from_recombination` obtains both pointwise identity
  `∀q(Xq=Yq)` and pointwise necessary identity `∀q□(Xq=Yq)`, but not the
  stronger `□∀q(Xq=Yq)`.
- Adding exactly zeroary Exhaustion gives the repaired central stock
  `pp_recombination_zeroary_exhaustion_axioms`.
  `CEV_QSS_from_recombination_with_zeroary_exhaustion` proves QSS in every
  ambient context.  The proof explicitly establishes purity of the universal
  identity sentence before applying Exhaustion.
- `CEV_fun_prime_from_contextual_QSS` proves `Fun(p) → fun′(p)`.
  `CEV_exists_fun_prime_from_QSS_and_unique_fundamentality` combines that
  implication with unique fundamentality to prove `∃fun′`; the central-stock
  corollary is
  `CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion`.
- All four T6 routes are replayed over the repaired central stock:
  `CEV_Goodman_T6_Inv_repaired_central_stock`,
  `CEV_Goodman_T6_TU_repaired_central_stock`,
  `CEV_Goodman_T6_WI_repaired_central_stock`, and
  `CEV_Goodman_T6_RS_repaired_central_stock`.  Inv/TU/WI no longer assume
  `∃fun′`; it is derived.  RS is inherited monotonically because its original
  exact stock did not contain that existential.
- Clean verification completed with `isabelle build -c -D .`.  The dedicated
  audit session in `reports/audit_qss_bridge/` inspected the nine principal
  theorem objects and found zero oracles, hypotheses, flex-flex pairs, and
  sort hypotheses.
- `frontier/Bacon_PP_Modalized_Functionality_Derived.thy` proves, in bare CEV,
  `[] ⊢CEV pp_modalized_functionality σ Prop`. Claude Opus 5 adversarially
  audited every rule and the de Bruijn closing step: correct and non-circular.
  This is the proposition-valued unary member only, not the full `σ,τ` schema.
- `frontier/Bacon_PP_T6_Encoding.thy` faithfully encodes `fun′`, composition,
  reversible operators, `G`, `≈`, weak L2, Inv, and Goodman's liar `D`.
- The T6-Inv axiom set is now exact and QLN-free: purity schema, application
  closure, PP at `t→t`, `∃fun′`, weak L2, and Inv. It contains no
  Recombination, Exhaustion, fundamentality assumptions, Persistence, or
  Purity of Fun.
- The same theory machine-proves `Pure(D)` using an explicit constant-free
  abstraction over `Pure_{t→t}`.
- `frontier/Bacon_PP_Goodman_T6_Inv.thy` proves
  `[] ; pp_T6_Inv_axioms ⊢CEV+ ⊥`.  The axiom stock is exact: purity schema,
  application closure, PP at `t→t`, `∃fun′`, weak L2, and Inv.  Both the
  same-kind witness and the `fun′` witness are eliminated in the
  object-language calculus.  No QLN, Recombination, Exhaustion,
  fundamentality, Persistence, Purity of Fun, WI, TU, RS, or strong-L2 enters.
- `frontier/Bacon_PP_Goodman_T6_TU.thy` proves
  `[] ; pp_T6_TU_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and TU.  The truth-flipping case eliminates the inverse existential and
  uses the conjugate `Z∘D∘Z⁻¹`; it imports no Inv, WI, strong-L2, RS, QLN,
  fundamentality, Persistence, or Purity of Fun.
- `frontier/Bacon_PP_Goodman_T6_WI.thy` proves
  `[] ; pp_T6_WI_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and WI.  The key theorem `CEV_axiom_WI_implies_TU` derives TU directly:
  every WI witness has the form `λp.(p↔A)`, hence is truth-preserving if `A`
  and truth-flipping if `¬A`.  This uses neither the stronger T1 stock nor
  Exhaustion.  An explicit axiom translation then reuses the verified TU
  contradiction.  No Inv, strong-L2, RS, QLN, Recombination, fundamentality,
  Persistence, or Purity of Fun enters.
- `frontier/Bacon_PP_Goodman_T6_WI_Master.thy` formalizes Goodman's advertised
  family `a_A ↔ ∀C(Pure(C) → (a_C ↔ ¬A))`, with
  `a_A = D((Dr) ↔ A)`, and proves the family propositionally inconsistent.
  `CEV_T6_WI_master_family_inconsistent` needs only `Pure(⊤)` once the family
  is available; `CEV_T6_WI_advertised_master_inconsistent` specializes this
  to Goodman's concrete `a_A`. Vampire finds the same minimal refutation in
  `vampire/goodman_t6_wi_master_inconsistent.in`. The remaining
  route-specific target is to derive the family from WI, weak L2, the liar
  matrix, and `fun′(r)`. Literal derivability from the exact, already
  inconsistent WI stock is separately recorded as
  `CEV_Goodman_T6_WI_advertised_master_claim_ex_falso`; its name prevents
  confusing explosion with Goodman's intended derivation.
- `frontier/Bacon_PP_Goodman_Composition.thy` now machine-proves the
  composition beta law, left and right identity, associativity, and purity of
  composition from the exact T6 core. It also provides versions of application
  closure and equality reasoning that are sound under temporary local
  assumptions.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Closure.thy` proves Goodman T2a:
  `fun′(p) ∧ G(Z) → fun′(Zp)`, `G(¬)`, and
  `fun′(p) → fun′(¬p)`, over every extension of the §4 core.
  The existential inverse in `G` is eliminated inside the object-language
  calculus.  The sharper intermediate result needs only a right inverse and
  does not use purity of the inverse or the left-inverse equation.
- Claude Opus 5 adversarially audited T2a and returned PASS.  It independently
  clean-built the frontier, found zero proof escapes, inspected the exported
  theorem objects (zero oracles or residual hypotheses), checked the crucial
  de Bruijn and local-assumption steps, and machine-checked exclusion of the
  stronger Goodman principles from the core.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2A_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Nontriviality.thy` proves Goodman T2b:
  `¬fun′(⊤)`, `¬fun′(⊥)`, and
  `fun′(p) → (p ≠ ⊤ ∧ p ≠ ⊥ ∧ p ≠ ¬p)` for every typed proposition `p`.
  The last inequality is proved already in bare CEV.
- Claude Opus 5 adversarially audited T2b and returned PASS.  Its independent
  audit theory proved the sharper dependency claim: the two refutations use
  only `Pure(id)`, `Pure(K⊤)`, and `Pure(K⊥)`; PP and application closure are
  not used.  It also generalized the argument to every closed constant-free
  proposition `M`, for which `¬fun′(M)` follows.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2B_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Attainment.thy` proves Goodman T2c in
  both parameter and exact quantified form:
  `fun′(r) → ∀p(Pure(p) → ◇(r=p))`.  Its diagonal proof identifies
  `λq.¬(q=p)` with the constant-truth operator under the supposition
  `□¬(r=p)`, then evaluates at `p` to contradict reflexivity.
- Claude Opus 5 adversarially audited T2c and returned PASS.  It independently
  clean-built the frontier, inspected the theorem objects, recomputed both
  beta reductions and the final binder shift, and machine-reproved the entire
  theorem over only `pp_purity_schema ∪ pp_application_closure_schema`.
  Thus PP itself, QSS, Recombination, Persistence, fundamentality, L2, Inv,
  and classification are all unused.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2C_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Possibly_Pure.thy` proves T2d,
  `fun′(r) → ◇Pure(r)`, from T2c at `⊤`, identity transport for purity, and
  derived possibility monotonicity.  Neither PP nor Persistence is needed:
  the required `Pure(⊤)` instance is a purity-schema axiom and is therefore
  necessitable in CEV's axiom-extension calculus.
- Claude Opus 5 adversarially audited T2d and returned PASS.  It independently
  re-proved the modal and identity-transport lemmas, machine-reproved the
  PP-free strengthening, and also machine-checked Goodman's original
  arbitrary-pure-`p` derivation using Persistence.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2D_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Noncontingency.thy` machine-proves
  T2e using the literal modal rendering `□r ∨ □¬r`.
  `frontier/Bacon_PP_Goodman_T2f_Verified.thy` machine-proves T2f as one
  conditional object-language theorem containing all fifteen pairwise
  inequalities among `⊤`, `⊥`, `r`, `¬r`, `(r=⊤)`, and `(r=⊥)`.
  Claude Opus 5 independently rebuilt these results and replayed the entire
  T2a--T2f chain over the PP-free core consisting only of the purity schema
  and application closure.  PP and Persistence are unused; application
  closure is genuinely needed.
- `frontier/Bacon_PP_Goodman_Pure_Proposition_Triviality.thy`,
  `frontier/Bacon_PP_Goodman_Biconditional_Classification.thy`, and
  `frontier/Bacon_PP_Goodman_WI_Collapse.thy` machine-prove all three stages
  of T1: every pure proposition is `⊤` or `⊥`, each pure-indexed
  biconditional operator is `id` or `¬`, and WI collapses to Inv.
  Claude Opus 5 independently audited both consequence derivations and
  returned PASS.
- The T3 theories now machine-prove the exact modal core and both calibrated
  repairs.  Necessitated QSS plus Persistence yields only
  `◇(Y=Z)`, not the actual `Y=Z` required by `fun′`.  Exact T3 follows from
  zeroary Exhaustion (`CEV_Goodman_T3_heredity_with_exhaustion`) or, more
  sharply, from pure-identity rigidity
  (`CEV_Goodman_T3_heredity_rigid`).  The unrestricted rigidity repair is
  refuted by `CEV_unrestricted_rigidity_refuted`.  The literal Section 4
  stock, with the globally assumed `∃fun′`, is now
  `pp_T3_advertised_axioms`, and
  `CEV_Goodman_T3_advertised_with_exhaustion` proves the repaired theorem
  over that exact stock.  The strengthened two-world theorem
  `Goodman_T3_advertised_modal_abstraction_countermodel` includes an actual
  `fun′` witness, unique fundamentality, global QSS, Persistence, Necessity
  of Identity, and Modalized Functionality while still refuting T3.  Claude's
  independent audit confirms that Goodman's advertised premise list omits
  this rigidity commitment.  Exact non-derivability from every unbounded
  member of `pp_T3_advertised_axioms` remains open pending a full model rather
  than only the strengthened modal abstraction.  The separate semantic
  theorem `pp_stock_fun_prime_hereditary` proves that T3 does hold in Bacon's
  substitution action when the certified pure operators are function-space
  members fixed by every substitution.  This identifies the implicit
  semantic premise precisely: invariance of the operators themselves, which
  is stronger than object-language Persistence of the predicate `Pure`.
  The sharpened theorem
  `pp_failed_heredity_requires_noninvariant_pure_pair` extracts distinct pure
  operators `F,G` from any failed semantic heredity instance and proves that
  at least one must be substitution-noninvariant.  Consequently an exact T3
  countermodel must use a nonstandard purity extension containing an exotic
  noninvariant operator; Bacon's intended closed-denotation interpretation
  cannot supply it.
- `frontier/Bacon_PP_Goodman_Higher_Type_Diagonal.thy` machine-proves T4 in
  the stronger object-language form
  `∀C(Pure(C) → ¬fun′_{t→t}(C(r)))`.  Its exact closed stock is
  `pp_T4_axioms = pp_purity_schema ∪ pp_application_closure_schema`;
  PP, `fun′(r)`, QSS, Persistence, and Exhaustion are unused.  The proof
  explicitly constructs Goodman's two distinct pure predicates that agree at
  `C(r)`. Claude Opus 5 independently clean-built and fully unfolded the
  theorem, checked the proof graph for oracles and residual hypotheses, and
  returned PASS WITH QUALIFICATIONS.  The qualifications concern semantic
  non-vacuity of the weak stock and the generic open-axiom interface, not the
  T4 derivation. Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T4_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse.thy` records a crucial
  consistency qualification found by Claude: if `fun′(r)` is inserted into
  the theorem-level axiom stock rather than retained as an antecedent, Rule
  of Equivalence collapses `(r=⊤)` and `(r=⊥)` to `⊥`; T2f fails and the
  resulting theory proves `⊥`.
- `frontier/Bacon_PP_Goodman_Proliferation.thy` machine-proves T5:
  `fun′(r) → ∃q(fun′(q) ∧ q ≠ r ∧ q ≠ ¬r)`.  Its exact headline stock is
  `pp_purity_schema ∪ pp_application_closure_schema ∪ {pp_target_PP}`.
  The existence of a `fun′` proposition remains an object-language
  antecedent, never a theorem-level axiom.  No L2, Inv, WI, TU, RS,
  Exhaustion, Persistence, Recombination, fundamentality, or Purity of Fun
  enters the derivation.
- Claude Opus 5 adversarially audited T5 and returned PASS WITH
  QUALIFICATIONS.  It independently reconstructed both liar refutations,
  checked every binder shift and the local-assumption boundary, clean-built
  the session, verified all ten theorem objects have no oracles or residual
  hypotheses, and machine-checked decisive controls for a missing negation,
  a reversed composition, and deletion of `fun′(r)`.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T5_2026-07-25.md`.
- Standing qualification: T2a--T2d are conditional derivability results in
  repository CEV.
  Non-vacuity of CEV plus the core is not yet proved.  Moreover,
  repository CEV takes ζ-Equivalence as primitive, whereas Goodman's `T₀`
  obtains it through Modalized Functionality; their identification remains a
  prose audit rather than a theorem internal to Isabelle.
- Claude's full audit is
  `reports/CLAUDE_AUDIT_MF_T6_2026-07-25.md`; the T1--T9 controlling matrix is
  `reports/GOODMAN_OBJECT_LANGUAGE_VERIFICATION_2026-07-25.md` (both local and
  gitignored by project policy).
- `frontier/Bacon_PP_Goodman_T6_RS_Encoding.thy` and
  `frontier/Bacon_PP_Goodman_T6_RS.thy` machine-prove the remaining T6 route.
  `CEV_Goodman_T6_RS` establishes `T₀ + PP + strong-L2 + RS ⊢ ⊥` from the
  exact stock. RS itself supplies a nonempty `fun′`-only specification, so no
  separate `∃fun′` axiom is present. The proof derives collision injectivity,
  proves the existential diagonal pure, verifies both directions of its liar
  law, and eliminates both existential witnesses object-linguistically.
- T7a is now machine-proved in
  `frontier/Bacon_PP_Goodman_T7_Absorption.thy`.
  `CEV_Goodman_T7a` establishes the exact closed absorption result from
  `T₀ + PP + ∃fun′ + L2`, with no Inv/WI/TU/RS classification axiom.
  The object-language proof extracts the liar counterexample witnesses,
  obtains same-kind via weak L2, transports truth to `D(Zd)`, and eliminates
  all witnesses.
- T8 now has an exact 31-object encoding in
  `frontier/Bacon_PP_Goodman_T8_Encoding.thy`: the five advertised base
  operators, their 31 nonempty subsets, the corresponding kind properties,
  and literal pairwise-distinctness formulas for both operators and values.
  The file proves both lists have length 31 and type-checks the full target.
- T8b is machine-proved by `CEV_Goodman_T8_kind_uniqueness` in
  `frontier/Bacon_PP_Goodman_T8_Kind_Uniqueness.thy`.
- T8a is machine-proved by `CEV_Goodman_T8a` in
  `frontier/Bacon_PP_Goodman_T8_Base_Kinds.thy`.  The theorem packages all
  ten base-pair separations and uses no L2 or group-classification principle.
  The nonconstant cases use `fun′` closure under arbitrary group members;
  the constant cases use the checked left-absorption equations for `K⊤` and
  `K⊥`.
- T8c is machine-proved in
  `frontier/Bacon_PP_Goodman_T8_Growth.thy`.
  `CEV_Goodman_T8c` proves the witness-parametric 31-operator/31-value claim;
  `CEV_Goodman_T8c_closed` proves the exact closed existential from
  `pp_T8_full_axioms = {∃fun′, L2} ∪ pp_T6_core_PP_axioms`. The proof
  explicitly abstracts the `Pure` constant in every generated kind property,
  derives its purity via PP plus application closure, separates different
  subsets using a selected base-kind witness, excludes omitted kinds via T8b
  plus the ten T8a separations, and then lifts operator inequalities to
  values at a `fun′` witness.
  The consolidated audit initially found that two finite-list distinctness
  lemmas used `by eval`, giving both exported T8c theorems one
  `Code_Generator.holds_by_evaluation` oracle. They have been replaced by
  structural proofs from `distinct_set_subseqs`, injectivity of the
  generated kind atoms, and a syntactic disjunction decoder. A focused
  post-repair theorem-object audit confirms zero oracles, hypotheses, and
  flex-flex constraints for `CEV_Goodman_T8c` and
  `CEV_Goodman_T8c_closed`.
- T7b is source-underspecified rather than an outstanding determinate
  Isabelle theorem. Goodman's PDF gives only the sentence that a
  “diagonal-on-kinds likewise has no fixed point but a shifted one,” without
  defining the diagonal, fixed/shifted point, binder structure, or exact
  stock beyond PP at `(t→t)→t`. Do not invent a formula and attribute it to
  Goodman; request an exact statement if this companion result is to be
  formalized.
- T9 remains, as advertised by Goodman, a meta-level cardinal-counting
  argument rather than a single object-language derivation. The advertised
  WI master family is now encoded and derived directly from Goodman's WI/L2
  stock.  The derivation in `Bacon_PP_Goodman_T6_WI_Master.thy` proves the
  forward direction from the liar matrix and core PP principles, proves the
  reverse direction using WI and L2, transports both sides through the
  lambda-encoded operator, and closes the exact quantified advertised claim.
  It does not pass through `ObjFalse`.  The older ex-falso derivation remains
  separately named for comparison. The exact WI contradiction is also
  independently checked via WI⇒TU.
- The single consolidated adversarial audit is complete as a preserved
  report. It returned PASS WITH QUALIFICATIONS. Its T8c evaluation-oracle
  finding was correct and has been repaired. Its purported second finding
  was not: `CEV_Goodman_T3_heredity_with_exhaustion` exists as the corollary
  over the full stock, while `CEV_Goodman_T3_heredity_min` is the sharper
  theorem over a smaller stock. All other principal theorem objects were
  clean. T7b remains
  source-underspecified, T9 remains meta-level, and the original PP
  consistency question remains open because every T6 contradiction is
  conditional on L2 plus a classification principle (or strong-L2 plus RS).
- The next major verification phase should cover Goodman's model-theoretic
  M-claims in a parallel matrix. This is likely to be the most useful source
  of constraints for the later consistency attack, especially through a
  semantic calibration of L2 and the pure reversible group `G`.

Written 2026-07-25 at the end of a Claude session, for whoever drives next
(immediately: Codex). `STATUS.md` is the long-form record; this is the
orientation document. Read this, then `STATUS.md`, then the sources in §6.

---

## 1. The problem, stated precisely

Background logic is **CEV** = H + Classicism + propositional Equivalence +
vector (ζ) Equivalence. It is the turnstile, not part of the axiom set.
Vocabulary: constants `Pure_σ, Fun_σ : σ →ₒ Prop` at each type. Defined:
`⊤ := ∀p:Prop. p → p` and `□A := (A = ⊤)`.

**X** (the statement whose consistency is in question) —

```
X  =  Pure_{(Prop→Prop)→Prop} ( Pure_{Prop→Prop} )
```

**A** (the assumptions) —

| | |
|---|---|
| A1 Purity schema | `Pure_σ M` for every closed constant-free `M : σ` |
| A2 Application closure | `∀F:σ→τ. ∀x:σ. (Pure F ∧ Pure x) → Pure (F x)` |
| A3 Exactly one fundamental proposition | `∃x:Prop. Fun x ∧ ∀y:Prop. (Fun y → y = x)` |
| A4 No fundamentals elsewhere (σ ≠ Prop) | `∀x:σ. ¬ Fun x` |
| A5 Unary Recombination | `∀F:Prop→Prop.∀p:Prop. (Pure F ∧ Fun p) → (□(F p) → ∀q. F q)` |

**The question:** is `A ∪ {X}` consistent?

Three things about this statement that are easy to get wrong:

- **Zeroary Recombination is redundant** and is *not* in A. CEV proves modal T
  unrestrictedly, so the purity antecedent is idle. Checked:
  `CEV_proves_zeroary_recombination` in `frontier/Bacon_PP_Minimal_Axioms.thy`.
- **Purity of Fun is deliberately absent.** `pp_purity_of_fun` is defined but in
  no axiom set. That omission *is* the question.
- **CEV⁺, not CEV.** Goodman writes `T₀ + PP + ∃fun′ + L2 + Inv ⊢ ⊥`, i.e.
  added principles are *axioms*, closed under the rules. So the target is
  `CEV_axiom_consistent` (`⊬CEV⁺ ⊥`), which is strictly stronger than the
  set-derivability version the repo's `pp_recombination_consistency_question`
  uses. Say which one you mean whenever you claim consistency.

Variants: adding Exhaustion gives the full-QLN question; further adding the
persistence schema gives the third. A5-only is the philosophically central one.

---

## 2. The single most important fact about this repo

**Goodman's own notes (`../PP_project_notes copy.pdf`, July 2026) are the
specification.** They are far ahead of this repo on the refutation side. His T1–T9
(object-language) and M1–M7 (model-theoretic) results are *hand-verified within
his collaboration, not machine-checked* — "checked n×" means exactly that.
Refereeing them is what this infrastructure is actually good for.

His T6 gives **four** routes to `⊥`: `T₀ + PP + ∃fun′` plus L2 with any of Inv,
WI, TU, and `strong-L2 + RS`. The contrapositive is the live state of play: any
model of the theory + PP must contain either cross-input collisions of pure
operators on `fun′` propositions (¬L2), or pure invertible operators that are
neither uniformly truth-preserving nor truth-flipping (¬TU). **The remaining
distance to refuting PP is a classification of G**, the group of pure reversible
operators.

His open problem **#1 is explicitly flagged "well-suited to mechanization"**:
calibrate L2 in Bacon's appendix model — do two non-≈ pure operators ever agree
on `fun′` inputs there? That model *is* this repo's word action (§4). This is
probably the highest-value target available and it is not what the internal
consensus plan recommended (that plan predates the notes).

---

## 3. Audit of this repo against the notes, §2 — results

Fifteen of seventeen items matched. Both apparent divergences were resolved, one
of them *against* my own initial finding:

- **Modalized Functionality — NOT missing.** I first recorded it as absent and
  added it as an axiom. Wrong. *Classicism* footnote 18 (p. 16): "C includes
  Modalized Functionality (see §1.5)", and §1.5 (p. 17) proves **Intensionality**
  `□∀z⃗(Xz⃗ ↔ Yz⃗) → X = Y` is a theorem of C. Intensionality has the weaker
  antecedent, so it implies MF. Bridge to this repo, p. 15: any H-theory closed
  under Propositional Equivalence together with ξ or ζ is closed under Logical
  Equivalence — and the repo has both, its `zeta_body` *being* Bacon–Dorr's
  ζ-Equivalence. So repo-CEV ⊇ Classicism ⊢ MF.
- **The `C_proves` axiom stock — not extra.** *Classicism* Figures 3 and 4 match
  it exactly, are "instances of Logical Equivalence", and Appendix A proves the
  converse. Equivalent axiomatizations.
- **H matches.** Book Def 5.1 gives PC1–3, UI, β, η, MP, Gen; the Classicism
  paper adds Ref, LL, EG as H-axioms, which is the repo's `H_proves`. The book's
  Rule of Substitution for non-logical constants is `CEV_proves_subst_const`.

**Net: the repo's theory is exactly T₀.** Not weaker, not stronger. Transfer is
unobstructed in both directions.

### The one divergence that stands

**The repo used the invariance reading of purity.** `pp_purity_operator F =
{i. pp_fun_invariant (pp_fun_view i F)}`. Goodman's M2 is titled *"the invariance
reading of purity is not an option"*, and his M1 says **PP fails at t→t in this
very model**. So `pp_purity_of_pure_holds_in_word_action` — which correctly
proves `pp_second_order_invariant pp_purity_operator` — does **not** show PP holds
in the word action, and the claim attached to it is false. Withdrawn.

Fix 2 is in `frontier/Bacon_PP_Definable_Purity.thy`: `pp_definable_purity L F =
{i. pp_fun_view i F ∈ L}` with the logical stock `L` a parameter (pinning it down
needs the `oterm` denotation bridge; everything proved is uniform in `L`), plus
`pp_definable_purity_subset_invariance`, `pp_readings_differ_of_proper_stock`,
and `pp_invariant_operators_outnumber_propositions` — M2's counting argument,
machine-checked.

Reassuringly the *model* is faithful and only the reading was wrong: M1 computes
`Pure_t` at the bottom type as `λp.(□p ∨ □¬p)`, and `pp_purity_of_meet`
independently gives `pp_purity_operator (λP. b ∩ P) = pp_decided b` with
`pp_decided X = □X ∪ □(−X)` — the same operator.

---

## 4. Ground rules — please keep these

1. **`isabelle build -D .` must stay green.** Baseline ~7s.
2. **`options [timeout = 60]` in ROOT.** The frontier outgrew the former
   15-second whole-session limit after all four T6 routes were added. A clean
   eight-thread build still takes about seven seconds. If a command is slow,
   **bisect** rather than waiting for the session limit.
3. **No `sorry`, `oops`, `admit`, `quick_and_dirty`.** A claim counts as proved
   only when a checked Isabelle theorem represents it.
4. **Do not use Caie or `ContextVectorEquivalence`.** Not part of this problem.
5. Sessions are split (`Higher_Order_Metaphysics`, `..._PP` in `pp/`,
   `..._PP_Frontier` in `frontier/`) specifically to keep iteration short. New
   work goes in `frontier/`; avoid editing the base session, which forces a
   full rebuild.
6. **Beware bare `auto`.** The `H_proves`/`C_proves`/`CE_proves`/`CEV_proves`/
   `compatible_step` constructors are all `[intro]`, so `auto` on goals in this
   development can search enormously. Prefer explicit `rule`/`intro`.

---

## 5. First Codex checkpoint: Unary Intensionality is complete

**Unary Intensionality in repo-CEV**, `frontier/Bacon_PP_Intensionality.thy`.
Codex completed it after this handoff was written. Machine-checked theorem:

```
CEV_unary_intensionality:
  Γ ⊢CEV Imp (□ (intens_condition σ X Y))
             (Eq (σ →ₒ Prop) X Y)
```

Route (Classicism §1.5): ζ is theorem-level and so cannot be applied to the
hypothesis. Instantiate ζ at the **guarded** pair `F := λz.(Xz ∧ C)`,
`G := λz.(Yz ∧ C)` with `C := ∀z.(Xz ↔ Yz)`, whose pointwise biconditional *is*
an H-theorem (from the UI instance `C → (Xz ↔ Yz)`); then use `□C`, i.e.
`C = ⊤`, with LL to replace `C` by `⊤`; then discharge `λz.(Xz ∧ ⊤) = X`; then
assemble by identity transitivity. This is now exactly what the theory proves.

**Checked infrastructure:** `subst_rename_to_rename`,
`subst_lift_shift_by_2`, `subst0_var0_shift_by_2`, `subst0_var0_lift_ren_Suc`,
`shift_ObjTrue` (de Bruijn infrastructure the repo lacked — it had only the
identity case, `subst_rename_inverse`); `intens_conj`, `intens_pred`, their
typing lemmas, `typed_shift_ctx`/`typed_var0`/`typed_shift_app`; and
`intens_pred_beta`.

The expensive biconditional tautology was avoided, not optimized. New helper
`CEV_biconditional_trans` follows the identity route:
`CEV_zeroary_equivalence` → `CEV_eq_trans_from` → Leibniz at `prop_id`.
The guarded ζ theorem is `CEV_intens_guarded_eq`; guard transport is
`CEV_intens_guarded_true_from_box`; truth discharge is
`CEV_intens_conj_true_eq`. The full project remains green under the 60-second
session timeout.

**Completed central target:** unary Modalized Functionality, the repaired QSS
bridge, `QSS +` unique fundamentality `→ ∃fun′`, and all four repaired-stock
T6 translations are now formalized.  The next mathematical target should be
chosen from the remaining consistency/model-theoretic frontier rather than
repeating this derivation.

---

## 6. Sources, all local

| What | Where |
|---|---|
| Goodman's project notes — **the specification** | `../PP_project_notes copy.pdf` |
| Bacon & Dorr, *Classicism* | `../Bacon_Dorr_Classicism.pdf` |
| Bacon, *Logical Combinatorialism* | `../tmp/pdfs/Bacon_Logical_Combinatorialism.pdf` |
| Bacon, *A Philosophical Introduction to Higher Order Logics* | `../Bacon_A Philosophical Introduction to Higher Order Logics.pdf` |
| Consensus debate 1 | `reports/PP_consensus_stocktaking_2026-07-25.md` |
| Consensus debate 2 | `reports/PP_consensus_stocktaking_2_2026-07-25.md` |

---

## 7. Where to go next

Ranked, with the notes taken into account. The internal consensus plan in
`STATUS.md` predates the notes and its top items are stale.

1. **Mechanize Goodman's open problem #1** — calibrate L2 in Bacon's appendix
   model. He flags it as suited to mechanization; the model is this repo's word
   action; the machinery largely exists. Either refutes L2 (killing the main
   refutation route) or supports seeking an object-language derivation of it.
2. **Attack the consistency question with the repaired dependency graph.**
   The central Recombination stock alone stops at the modal core; zeroary
   Exhaustion supplies QSS and `∃fun′`; each T6 contradiction still requires
   L2 plus Inv/TU/WI, or strong-L2 plus RS.  Determine which of those added
   principles can hold in a verified Isabelle model of the repaired stock.
3. **Replace the purity interpretation throughout** with the definability
   reading and sweep every result that leaned on invariance (§3).
4. **A model of A + ¬X.** Lower value for Goodman — M1 already settles that PP
   fails at t→t in Bacon's model, so A is consistent and X is independent, and
   the question is non-degenerate. Worth it only as infrastructure validation.

## 8. Claims withdrawn during this session — do not resurrect

- PP holds in the word action (contradicts M1; used the invariance reading).
- The repo's theory is weaker than T₀ (it is exactly T₀).
- The CEV⁺ step-2 null result is evidence for consistency (it is evidence the
  search space was too small).
- `base_sound` fails for the word action (only conditional: it fails **if** CEV
  proves 5 — and CEV almost certainly does *not*, at ~0.99; Bacon–Dorr show
  Classicism's propositional modal fragment is exactly S4, and Prop 2.2
  identifies necessity of distinctness with 5 and B and denies it is a theorem).
- The constant-substitution lemma is missing (it exists:
  `CEV_proves_subst_const`).
- All consistency credences (~0.55, ~0.40–0.45). They were computed against a
  mis-specified theory and a wrong reading of `Pure`.
