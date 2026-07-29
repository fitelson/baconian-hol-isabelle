# Handoff: Goodman's PP consistency problem

## 0. Current repository layout and L2 status

The source tree now has three explicit layers:

1. `theories/base/`, session `Bacon_Base`;
2. `theories/classicism/`, session `Bacon_Classicism`, including CE and CEV;
3. `theories/goodman/`, session `Goodman_CEVplus`, with all Goodman proof,
   model, canonical, and bridge sessions beneath it.

All active project sessions are declared in the root `ROOT`.  The full serial
build command is `isabelle build -j 1 -D .`.  The authoritative map is
`docs/REPOSITORY_STRUCTURE.md`.

Goodman's semantic L2 calibration is complete.  The closed logical operator
\(Z\), which compares the truth values at the two immediate successor worlds,
is formalized in
`theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_L2_Child_Xor.thy`
and is proved surjective, noninjective, right-cancellative among the
denotations of closed logical terms, and nonreversible.  The theorem
`pp_b_child_xor_refutes_exact_L2` refutes L2 in Bacon's appendix model under
that interpretation of purity.  Strong L2 fails there as well.  This does not settle
Goodman's consistency question because the model independently fails PP.
Sections below that call global L2 open are chronological records of an
earlier frontier and are superseded by this checkpoint.

## 0. New live checkpoint: staged Vampire analysis of L2 from PP

The proposed derivation of weak L2 from
\(T_0+\mathrm{PP}+\exists\mathsf{fun}'\) is now divided into separate THF
obligations.  Vampire proves:

1. a collision \(X(p)=Y(q)\) on `fun'` propositions forces \(X\) and \(Y\)
   to agree on every equation obtained by composition on the left by pure
   operators;
2. if that agreement determines sameness of kind, then weak L2;
3. if every two `fun'` propositions lie in one reversible orbit, then weak
   L2; and
4. the weaker \(Y\)-relative reversible transport condition also implies
   weak L2.

The final combined target admits only lemmas proved in the preceding split
targets.  The remaining PP-to-premise conjectures are not admitted.

The hard step remains unresolved.  Sixty-second, six-core searches did not
derive any of the three sufficient conditions from the represented
\(T_0+\mathrm{PP}+\exists\mathsf{fun}'\) background, either with genuine
higher-order function types or with operators reified into a multisorted
first-order sort.  The earlier monolithic higher-order search also returned
no proof after one hour.  None of these timeouts is a nonderivability result
or a countermodel.  Further work on this route should seek a substantive
PP-specific reason for one of the three conditions rather than repeat the
monolithic search.

## 0. New live checkpoint: verified-model cutoff and failure of the
\(J+D\) stabilization

The reader-facing report deliberately stops its verified model sequence at
`theories/goodman/models/fragments/higher_order_quantified/Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model.thy`.
That model contains the Boolean stock, necessity, possibility, and the six
higher-order quantified unary operators.  Do not add the later \(J\) or
T6-diagonal stages to the report's list of verified models unless a joint
stabilization theorem is proved.

The later work is a machine-checked investigation, not a new reported model:

1. `theories/goodman/models/fragments/fun_prime/Bacon_PP_ZF_Fresh_Fun_Prime_Fragment_Model.thy` adds the
   closed operator \(J=\lambda p.\mathit{fun}'(p)\).  The theorem
   `pp_t_fun_prime_stabilizes` proves that recomputing
   \(\mathit{fun}'\) after this one-step enlargement does not change its
   extension.
2. `theories/goodman/models/fragments/t6_diagonal/Bacon_PP_ZF_Fresh_T6_Diagonal_Fragment_Model.thy` evaluates
   Goodman's T6 diagonal \(D\) against the \(J\)-enlarged stock.  The theorem
   `pp_t_fun_prime_T6_collision_only_negation_like` proves that every harmful
   old-stock collision at a \(\mathit{fun}'\) proposition is represented by
   negation, necessary falsity, or possible falsity.
3. `pp_t_T6_diagonal_absorbs_fun_prime_iff_three_classes` proves that
   preservation of the old \(\mathit{fun}'\) propositions is equivalent to
   three local harmlessness implications, one for each of those classes.
   `pp_t_T6_diagonal_absorption_failure_iff` gives the exact counterexample
   form.
4. `theories/goodman/models/fragments/t6_diagonal/Bacon_PP_ZF_Fresh_T6_Collisions.thy` settles the
   three-class test negatively.  Its recurrent proposition \(R\) is
   \(\mathit{fun}'\) along an infinite branch and settled on every side
   cone.  At the root \(D(R)\) is equivalent to necessary falsity applied
   to \(R\), while \(D\) and necessary falsity are not equivalent operators.
   The same witness has neither the negation nor the possible-falsity
   collision.  Therefore
   `pp_t_T6_diagonal_does_not_absorb_fun_prime`,
   `pp_t_T6_diagonal_fun_prime_operator_does_not_stabilize`, and
   `pp_t_T6_diagonal_no_joint_fixed_point` refute the proposed fixed point.
5. The one-step \(D\) interpretation verifies unary Recombination and
   Exhaustion, application closure, Modalized Functionality, unique
   proposition-level fundamentality, and the displayed PP instance.  These
   results do not establish that the denotation of \(J\), the denotation of
   \(D\), and the pure stock are jointly fixed after simultaneous
   reevaluation.

The three-collision frontier is therefore closed for this construction:
necessary falsity supplies an explicit harmful collision.  Do not try to
complete its joint stabilization.  The next exact task is to determine
whether a materially different interpretation can avoid this obstruction,
or whether an abstract argument derives the same obstruction from Goodman's
principles.

## 0. New live checkpoint: complete Goodman-claims audit

The controlling ledger is
`reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md`.  Its associated
Isabelle session, `Goodman_Complete_Audit_2026_07_27`, audits 128 theorem
objects supporting the current report and matrix, including the completed
M5 rebuilt model and the refutation of L2, and
passes with zero oracles, zero undischarged logical
hypotheses, and zero flex-flex pairs.  T9's single sort hypothesis is ordinary
polymorphism and is reported separately.

The M5 rebuilding step is complete, not open.  The theory
`theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model.thy`
constructs the least application-closed pure stock containing all closed
logical denotations and Goodman's displayed exotic operator.  The operator's
denotation is typed, commutes with taking views, is self-inverse, is not
truth-uniform, and is not a biconditional operator.  A rebuilt fundamental
proposition supplies Recombination and fun-prime separation at every world,
and the interpretation validates Bacon's Recombination background.  It is
not a PP model: PP would further require the classifier of this enlarged
stock to occur at the next type.

Six significant additions are now checked:

1. `theories/goodman/notes/Bacon_PP_Goodman_T9.thy` proves the PC map injective from its
   specification, constructs injective codes of kind-fibres from Goodman's
   representation hypothesis, and derives the advertised cardinal dichotomy.
2. `theories/goodman/notes/Bacon_PP_Goodman_M7_Invariant_Reachability.thy` proves that
   universal invariant reachability is equivalent to injectivity of the
   orbit map.
3. `theories/goodman/notes/Bacon_PP_Goodman_M5_Orbit_Avoidance.thy` repairs a false
   countability argument in Goodman's M5.  For every proposed fundamental
   proposition `R`, it diagonally constructs a two-element pair avoiding
   every view of `R`, proves all proper views of the pair extreme, and builds
   an invariant nonidentity transposition fixing `R`.
4. `theories/goodman/notes/Bacon_PP_Goodman_M1_Fn60.thy` proves that the infinitary join
   exists and has exactly the intended extension, while the PP diagonal and
   QSS prevent it from being certified pure.
5. `theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_M1_Fn60.thy` identifies that join with the
   interpretation of `Pure` at the next type and proves that PP there is
   equivalent to membership of the classifier in the next pure stock.  It
   does not prove nonmembership directly in Bacon's exact generic model; the
   available exclusion theorem is conditional on the additional
   PP-diagonal/QSS assumptions.
6. `theories/goodman/notes/Bacon_PP_Goodman_M5_Collision.thy` proves the displayed collision:
   `λp.(p ↔ NC(p))` agrees at `NC(r)` and truth even though those inputs are
   distinct, assuming `fun-prime(r)`.

Every determinate claim in the notes is now proved, refuted and repaired, or
stated with the qualification on which it is true.  Do not turn this into a
blanket PASS for every sentence.  T3 has the documented modal gap; T7b and the
wide-Fun discussion in M4 are underspecified.  The proposed unrestricted M5
collision generalization is refuted, and the rebuilt M5 model for Bacon's
Recombination background is complete.  The main consistency question remains
open.  Global semantic L2 is refuted by the child-XOR theorem recorded in the
current checkpoint above.

The earlier adversarial audit is
`reports/CONSENSUS_GOODMAN_FINAL_AUDIT_2026-07-27.md`.  Its three precision
repairs are incorporated.  A final adversarial re-audit of the newly completed
M1, M5, and T9 results and of the Goodman-facing report is pending.

The reader-facing Goodman report is
`reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf`, with
self-contained Forbes/Lucida source in the adjacent `.tex` file.  It contains
the complete T1--T9 and M1--M7 audit, the T3 and M5 corrections, and a separate
account of the new theorems that advance the open question.

## 0. New live checkpoint: recurrence-module role-swap debate complete

Claude and Codex completed eight adversarial rounds, with the positive and
negative roles swapped on every turn.  The result is unresolved: there is
neither a typed cone-natural absorbing enumerator nor an unconditional
generated escape theorem.

The best positive program is no longer the global no-preimage invariant.
Instead, close a countable cone-natural operator stock `S` under the full
recurrence module

```text
{Rec_p o F | F in S}.
```

Under the proposed anti-recurrent separator recipe, symmetric-difference
partners make ordinary uniqueness hold exactly on recurrence support, which
gives the paper-level identity `M_E = not o Rec_p`.  The first nested
uniqueness operator also collapses modulo a support-local preimage condition.
The material-truth quotient diagonal is constantly true on recurrence
support because identity and complement provide truth-opposite
representations there.

Failure of no-preimage is not itself a refutation.  Composition satisfies

```text
(Rec_p o F) o G = Rec_p o (F o G),
```

so all iterated preimage-recurrence obligations remain in the same countable
module.  If `X` is an equivariant bijection, then

```text
Rec_p o X = Rec_(inv X p).
```

Surjective stock members also transport separators.  Thus exotic generated
bijections need not be classified as identity or complement; their
signatures can in principle be absorbed by the module.

The next Isabelle tranche is:

1. `pp_b_preimage_recurrence_compose`;
2. `pp_b_recurrence_transport_bijection`;
3. `pp_b_separator_transport_surjection`; and
4. `pp_b_countable_recurrence_module_closed_extension`.

The fourth theorem is the decisive construction test: can one extend an
arbitrary countable equivariant logical stock to a countable stock that is
still separated by `p`, whose separator operator is `Rec_p`, and which is
closed under `F |-> Rec_p o F`?

The sharp falsification target is one closed logical unary `F` such that
`Rec_p o F` is not `Kbot` globally but agrees with `Kbot` at `p`.  Closure
would then add two distinct stock members agreeing at the proposed separator,
immediately refuting the recurrence-module extension.  Test the existing
mixed modal operators first, then the range-classifier probe, the inverse
builder on generated bijections, and the material-truth quotient diagonal.
No such `F` is presently known.

All recurrence-separator, uniqueness-collapse, and transport results from
this debate are paper-level until formalized.  Previously checked results
retain their status.  The transcript is
`reports/CONSENSUS_ABSORPTION_ROLESWAP_2026-07-27.md`, with Claude's
checkpoints in
`reports/CONSENSUS_ABSORPTION_ROLESWAP_PROGRESS_2026-07-27.md`.

## 0. New live checkpoint: soundness complete; only absorption remains

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_CEV_Soundness.thy` is included in
`Higher_Order_Metaphysics_PP_ZF_Model` and discharges the two semantic
assumptions left open by the preceding checkpoint.

Inside `pp_t_constants`, the theory proves the structural evaluator lemmas
needed for soundness: extensionality, environment agreement, shift,
substitution, beta, eta, and compatibility with the object-language
conversion relation.  It then verifies the six Boolean identities, four
quantifier identities, Leibniz identity, C, CE, and typed
vector-Equivalence.  The exported conclusions are:

```text
pp_t_base_sound
pp_t_zeta_sound
```

For the repaired term-basis constants, the theorem
`pp_t_term_basis_fixed_point_answers_Goodman` therefore has only the
absorption equation as a substantive premise.  No independent `base_sound`
or `zeta_sound` assumption remains.

The same theory proves
`pp_t_term_basis_fixed_point_has_closed_L2_or_TU_failure`: any absorbing
enumerator gives a model in which the closed object-language formula `pp_L2`
or the closed formula `pp_TU` fails globally already at the empty context.
The companion theorem
`pp_t_term_basis_fixed_point_has_L2_or_TU_counterworld` extracts an actual
tree world falsifying one of those two closed denotations.
The result is deliberately disjunctive.  Selecting L2 would require proving
TU for every generated pure reversible; selecting TU would require proving
global semantic L2.  Neither classification is presently available.

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Range_Term_Basis.thy` now also names the exact
remaining fixed-point burden:

1. `pp_t_enumerator_range_subset_basis` proves that every range value `E n`
   is automatically generated by the application expression `E n`.
2. `pp_t_term_basis_fixed_point_iff_absorbs_generated` reduces equality to
   the converse inclusion.
3. `pp_t_term_basis_fixed_point_iff_expression_surjective` says that the
   converse inclusion is exactly: every well-typed generated unary
   expression denotes `E n` for some `n`.
4. `pp_t_term_basis_fixed_point_has_no_reflecting_expression` and its
   separating corollary show that any solution must defeat every generated
   typed Cantor tag.

Thus the positive and negative frontiers are now clean.  Positively,
construct a typed cone-natural `E` with expression-surjective range.
Negatively, force an `E`-reflecting `Ind -> Prop` expression from the same
syntax.  The existing cone-collapse results explain why the naive separating
tags do not do this.  No construction or unconditional refutation is
currently claimed.

## 0. New live checkpoint: repaired stock and the T6 escape are exact

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Repaired_Central_Stock.thy` is included in
`Higher_Order_Metaphysics_PP_ZF_Model`.

The semantic self-reference condition forced by PP is now named
`pp_t_self_applicative_pure`.  It says exactly that the classifier of the
pure unary stock is itself pure at the next type.  It does not impose the
stronger and unjustified requirement that every pure stock be exactly its own
denotational range.

For every `pp_t_stock_basis`, the theory proves
`pp_t_basis_pure_prop_truth_implies_necessary`.  A pure proposition is
locally equivalent to a cone-natural basis representative, and every such
representative collapses to global truth or global falsity.  Therefore
zeroary Exhaustion is globally valid:

```text
pp_t_basis_zeroary_exhaustion_gvalid
```

The combined theorem
`pp_t_basis_repaired_central_gvalid_iff` now says:

```text
gvalid_set pp_recombination_zeroary_exhaustion_axioms
  iff pp_t_self_applicative_pure (pp_t_basis_stock D).
```

For the explicit enumerator-generated term basis,
`pp_t_term_basis_repaired_central_gvalid_from_fixed_point` discharges the
entire repaired stock from the same raw absorption equation already isolated
in `Bacon_PP_ZF_Tree_Range_Term_Basis`.  Zeroary Exhaustion therefore creates
no new fixed-point condition.

The generic theorems
`repaired_central_stock_forces_L2_or_TU_failure` and
`repaired_central_stock_has_explicit_L2_or_TU_failure` prove the precise
semantic T6 alternative.  Given `base_sound`, `zeta_sound`, and global
validity of the repaired central stock, global validity of `{L2,TU}` is
impossible; equivalently, some context falsifies L2 or TU.  The theorem
`pp_t_term_basis_fixed_point_forces_L2_or_TU_failure` combines this with the
enumerator absorption equation.

This checkpoint has been superseded in one respect by the entry above:
`base_sound` and `zeta_sound` are now proved.  The absorption fixed point is
the sole remaining model-existence obligation.

The focused ZF session and the full project build pass, and the new theory
contains no proof escapes.

## 0. New live checkpoint: `R_stab` is the actual tree stabilizer action

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Stabilizer_Orbit.thy` is included in
`Higher_Order_Metaphysics_PP_ZF_Model`.  It supplies both the semantic
action and its closed object-language relation.

The semantic operation

```text
pp_t_qd_precompose G psi = G o psi
```

is a typed unary operator whenever `G` and `psi` are typed.  The theorem
`pp_b_operator_of_precompose` proves that this is the actual Boolean-tree
action:

```text
pp_b_operator_of (pp_t_qd_precompose G psi)
  = pp_b_operator_of G o pp_b_operator_of psi.
```

The closed logical term `pp_qd_stabilizer_relation` expresses

```text
R_stab(q,F,G) :=
  Exists psi. (Bij psi and F = G o psi and psi q = q).
```

Its typing, logical vocabulary, domain membership, and denotational truth
condition are checked.  The load-bearing bridge is
`pp_t_qd_world_bijective_root_iff`: for each typed `psi`, the internal root
injectivity/surjectivity clause holds iff `pp_b_operator_of psi` is literally
bijective on Boolean-tree propositions.  Thus the object quantifier ranges
over the full ambient respecting-bijection group.  The existing ambient
theorem then gives cone-profile bijectivity and a view-respecting inverse.
`pp_t_qd_stabilizer_orbit_root_iff_ambient` identifies the whole root
relation with this raw action.

Two consequences delimit the route:

1. `pp_t_qd_stabilizer_orbit_truth_congruent` proves the exact congruence
   premise required by the quotient diagonal at every world.
2. `pp_t_qd_stabilizing_precomposition_relation_holds` proves that every
   representation produced by precomposition with a bijection fixing the
   tag is automatically `R_stab`-related.  These colliders therefore cannot
   violate the diagonal guard.

The relation itself is a closed logical generated-stock member, and
`pp_t_qd_stabilizer_diagonal_in_generated_stock` puts
`D_Rstab(E,H)` in the repaired central stock for every generated `H`.

This does not prove tag homogeneity.  The remaining negative-route question
is whether every representation of a suitable diagonal tag lies in one
stabilizer orbit modulo `R_stab`; group-generated representations are only
a known subclass.  Either prove that representation-completeness statement
for one generated `H`, or construct an explicit non-orbit representation.
The absorbing-enumerator construction remains the parallel positive route.

## 0. New live checkpoint: the closed `D_R` term is generated

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Quotient_Diagonal_Builder.thy` is now included
in `Higher_Order_Metaphysics_PP_ZF_Model`.  It defines the constant-free
closed term `pp_qd_builder` at type

```text
(Ind -> U) -> (Prop -> Prop -> Prop) ->
  (Prop -> U -> U -> Prop) -> U
```

with `U = Prop -> Prop`.  The term is machine-checked as typed and logical.
Its semantic theorem `pp_t_qd_builder_apply_holds` proves, for typed
`E,H,R,q`, that `D_R(E,H,R) q` holds at `w` exactly when every separated
`H`-representation of `q` to whose representing operator all other
representatives are `R`-related is false at `q`.  The theorem retains the model's
intended semantics: object equality is the world-relative PER and
`R q F G` is evaluated for truth at `w`.

Two closure theorems remove the syntactic-stock obligation:

1. `pp_t_qd_den_in_enumerator_basis` gives exact membership in the raw
   applicative term basis if `H` and `R` are raw generated expressions.
2. `pp_t_qd_den_in_generated_stock` gives membership in the repaired,
   root-equivalence-saturated central stock if `H` and `R` are members of
   that stock.

The second theorem uses only logical containment, the distinguished
enumerator's stock membership, and three applications of the already
verified stock application-closure theorem.  Therefore `D_R` generation is
no longer an open premise.

The consistency problem itself remains open.  The contradiction route now
has one precise missing mathematical ingredient: find generated `H,R` with
`R` root-truth-congruent and prove tag homogeneity at the absorbed diagonal
index.  The previous two-point tests refute the naive finite-observational
and stabilizer-orbit versions.  The next direct move is to lift the
stabilizer-orbit relation to the actual tree-model operator action and test
whether some stronger invariant forces homogeneity there.

## 0. New live checkpoint: inverse and quotient-diagonal tranche checked

The first two items from the absorption consensus program are now
machine-checked in `Higher_Order_Metaphysics_PP_ZF_Model`.

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Ambient_Inverse.thy` proves:

1. the exact Boolean cone decomposition
   `X_w \<cong> 2 \<times> X_{w@[False]} \<times> X_{w@[True]}`;
2. every view-respecting ambient bijection induces a bijection on every
   cone;
3. its raw inverse is again view-respecting and belongs to the intended
   unary PER domain; and
4. the closed logical term
   `\<lambda>\<psi> q. \<exists>p. (\<psi>p = q \<and> p)` is typed, logical, and
   computes the inverse pointwise.

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Quotient_Diagonal.thy` gives a parametric,
root-semantic formalization of separators, `H`-representations, a
root-truth-congruent relation `R`, the diagonal `D_R`, and tag homogeneity.
The theorem `pp_qd_absorption_forces_tag_heterogeneity` proves:

```
D_R diagonal + root-truth congruence of R + E k = D_R + separator p
  ==> the tag H p ((E k) p) is not R-homogeneous.
```

The root-truth-congruence premise is essential; Isabelle rejected the
argument without it.  The same theory checks two finite diagnostics.
Singleton finite-observational agreement (observing the tag itself) and the
stabilizer-orbit relation are truth-congruent, but both fail tag homogeneity
in an explicit two-point example with `E False = id` and
`E True = Not`.  These relations therefore do not by themselves supply the
uniform homogeneity needed for contradiction.

The next mathematical move is narrower:

1. encode `D_R` as a closed object-language builder over `E`, `H`, and `R`;
2. prove that its denotation satisfies the checked root-semantic schema and
   therefore lies in the generated central stock; and
3. lift the stabilizer-orbit diagnostic to the actual tree-model action,
   looking either for an extra invariant that forces homogeneity or for a
   systematic heterogeneous representation.

The direct consistency question remains open.

## 0. New live checkpoint: consensus sharpens the absorption frontier

An eight-round, sixteen-turn Claude--Codex debate has finished.  It reached
consensus on the exact frontier and next program, while leaving the
mathematical existence question open.  Do not report either a construction
or a refutation.

The strongest new results are currently metatheoretic:

1. cone-natural unary operators have a germ normal form, with one arbitrary
   Boolean predicate on proposition views;
2. two infinite-fiber enumerations of the same unary range generate the same
   unary basis, so the canonical regime admits an inflationary set operator
   `C(S)`;
3. full-domain meets and joins guarded only by nonmembership in a countable
   range collapse to bottom and top by cardinal slack;
4. the generated quotient-guarded diagonal `D_R` proves that absorption
   forces every diagonal tag to have representations in at least two
   `R`-classes, for every generated root-truth-congruent relation `R`;
5. generated bijections act on separator-tag representations by
   `(p,F) . psi = (psi^-1 p, F o psi)`; group orbits supply systematic
   colliders but are not known to exhaust representations; and
6. the logical inverse-builder denotes the raw inverse of every respecting
   raw bijection in the full unary domain, not only the cone-natural ones.

The next move is not more generic scaffolding.  Formalize the ambient inverse
theorem and `D_R` schema first.  Then attack one concrete `(H,R,p*)`, using
finite observational relations and the stabilizer-orbit relation before
literal equality.  In parallel, formulate promise-bearing stable fusion able
to preserve range membership for every scheduled expression; quotient- and
uniqueness-guarded terms are the decisive stress tests.

The full record is
`reports/CONSENSUS_ABSORPTION_FIXED_POINT_2026-07-26.md`, with checkpoints in
`reports/CONSENSUS_ABSORPTION_FIXED_POINT_PROGRESS_2026-07-26.md`.

## 0. New live checkpoint: the enumerator problem is one absorption fixed point

Two further theories are now included in
`Higher_Order_Metaphysics_PP_ZF_Model`:

- `theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Range_Diagonal.thy`; and
- `theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Range_Term_Basis.thy`.

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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Seeded_Stock.thy` defines the locale
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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Range_Classifier.thy` defines the closed logical
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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Basis_Stock.thy` is now the live frontier and is
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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Generic_Seed.thy` remains the live frontier.

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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Generic_Seed.thy` is now the live frontier.

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

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Logical_Stock.thy` is now the live frontier.

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

- `theories/goodman/models/hol_zf/Bacon_PP_ZF_Tree_Frame.thy` is now the live positive frontier.
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
- Therefore `theories/goodman/models/hol_zf/Bacon_PP_ZF_Hyper_Frame.thy` is now a checked negative
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
- `theories/goodman/models/hol_zf/Bacon_PP_ZF_Hyper_Frame.thy` remains the reusable evaluator and
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
- `theories/goodman/models/hol_zf/Bacon_PP_ZF_Full_Frame.thy` is retained as the extensional
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
- `theories/goodman/notes/Bacon_PP_Central_Model_Obligations.thy` is the live model theory.
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

- `theories/goodman/notes/Bacon_PP_QSS_Recombination_Bridge.thy` proves the precise
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
- `theories/goodman/notes/Bacon_PP_Modalized_Functionality_Derived.thy` proves, in bare CEV,
  `[] ⊢CEV pp_modalized_functionality σ Prop`. Claude Opus 5 adversarially
  audited every rule and the de Bruijn closing step: correct and non-circular.
  This is the proposition-valued unary member only, not the full `σ,τ` schema.
- `theories/goodman/notes/Bacon_PP_T6_Encoding.thy` faithfully encodes `fun′`, composition,
  reversible operators, `G`, `≈`, weak L2, Inv, and Goodman's liar `D`.
- The T6-Inv axiom set is now exact and QLN-free: purity schema, application
  closure, PP at `t→t`, `∃fun′`, weak L2, and Inv. It contains no
  Recombination, Exhaustion, fundamentality assumptions, Persistence, or
  Purity of Fun.
- The same theory machine-proves `Pure(D)` using an explicit constant-free
  abstraction over `Pure_{t→t}`.
- `theories/goodman/notes/Bacon_PP_Goodman_T6_Inv.thy` proves
  `[] ; pp_T6_Inv_axioms ⊢CEV+ ⊥`.  The axiom stock is exact: purity schema,
  application closure, PP at `t→t`, `∃fun′`, weak L2, and Inv.  Both the
  same-kind witness and the `fun′` witness are eliminated in the
  object-language calculus.  No QLN, Recombination, Exhaustion,
  fundamentality, Persistence, Purity of Fun, WI, TU, RS, or strong-L2 enters.
- `theories/goodman/notes/Bacon_PP_Goodman_T6_TU.thy` proves
  `[] ; pp_T6_TU_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and TU.  The truth-flipping case eliminates the inverse existential and
  uses the conjugate `Z∘D∘Z⁻¹`; it imports no Inv, WI, strong-L2, RS, QLN,
  fundamentality, Persistence, or Purity of Fun.
- `theories/goodman/notes/Bacon_PP_Goodman_T6_WI.thy` proves
  `[] ; pp_T6_WI_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and WI.  The key theorem `CEV_axiom_WI_implies_TU` derives TU directly:
  every WI witness has the form `λp.(p↔A)`, hence is truth-preserving if `A`
  and truth-flipping if `¬A`.  This uses neither the stronger T1 stock nor
  Exhaustion.  An explicit axiom translation then reuses the verified TU
  contradiction.  No Inv, strong-L2, RS, QLN, Recombination, fundamentality,
  Persistence, or Purity of Fun enters.
- `theories/goodman/notes/Bacon_PP_Goodman_T6_WI_Master.thy` formalizes Goodman's advertised
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
- `theories/goodman/notes/Bacon_PP_Goodman_Composition.thy` now machine-proves the
  composition beta law, left and right identity, associativity, and purity of
  composition from the exact T6 core. It also provides versions of application
  closure and equality reasoning that are sound under temporary local
  assumptions.
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Closure.thy` proves Goodman T2a:
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
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Nontriviality.thy` proves Goodman T2b:
  `¬fun′(⊤)`, `¬fun′(⊥)`, and
  `fun′(p) → (p ≠ ⊤ ∧ p ≠ ⊥ ∧ p ≠ ¬p)` for every typed proposition `p`.
  The last inequality is proved already in bare CEV.
- Claude Opus 5 adversarially audited T2b and returned PASS.  Its independent
  audit theory proved the sharper dependency claim: the two refutations use
  only `Pure(id)`, `Pure(K⊤)`, and `Pure(K⊥)`; PP and application closure are
  not used.  It also generalized the argument to every closed constant-free
  proposition `M`, for which `¬fun′(M)` follows.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2B_2026-07-25.md`.
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Attainment.thy` proves Goodman T2c in
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
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Possibly_Pure.thy` proves T2d,
  `fun′(r) → ◇Pure(r)`, from T2c at `⊤`, identity transport for purity, and
  derived possibility monotonicity.  Neither PP nor Persistence is needed:
  the required `Pure(⊤)` instance is a purity-schema axiom and is therefore
  necessitable in CEV's axiom-extension calculus.
- Claude Opus 5 adversarially audited T2d and returned PASS.  It independently
  re-proved the modal and identity-transport lemmas, machine-reproved the
  PP-free strengthening, and also machine-checked Goodman's original
  arbitrary-pure-`p` derivation using Persistence.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2D_2026-07-25.md`.
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Noncontingency.thy` machine-proves
  T2e using the literal modal rendering `□r ∨ □¬r`.
  `theories/goodman/notes/Bacon_PP_Goodman_T2f_Verified.thy` machine-proves T2f as one
  conditional object-language theorem containing all fifteen pairwise
  inequalities among `⊤`, `⊥`, `r`, `¬r`, `(r=⊤)`, and `(r=⊥)`.
  Claude Opus 5 independently rebuilt these results and replayed the entire
  T2a--T2f chain over the PP-free core consisting only of the purity schema
  and application closure.  PP and Persistence are unused; application
  closure is genuinely needed.
- `theories/goodman/notes/Bacon_PP_Goodman_Pure_Proposition_Triviality.thy`,
  `theories/goodman/notes/Bacon_PP_Goodman_Biconditional_Classification.thy`, and
  `theories/goodman/notes/Bacon_PP_Goodman_WI_Collapse.thy` machine-prove all three stages
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
- `theories/goodman/notes/Bacon_PP_Goodman_Higher_Type_Diagonal.thy` machine-proves T4 in
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
- `theories/goodman/notes/Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse.thy` records a crucial
  consistency qualification found by Claude: if `fun′(r)` is inserted into
  the theorem-level axiom stock rather than retained as an antecedent, Rule
  of Equivalence collapses `(r=⊤)` and `(r=⊥)` to `⊥`; T2f fails and the
  resulting theory proves `⊥`.
- `theories/goodman/notes/Bacon_PP_Goodman_Proliferation.thy` machine-proves T5:
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
- `theories/goodman/notes/Bacon_PP_Goodman_T6_RS_Encoding.thy` and
  `theories/goodman/notes/Bacon_PP_Goodman_T6_RS.thy` machine-prove the remaining T6 route.
  `CEV_Goodman_T6_RS` establishes `T₀ + PP + strong-L2 + RS ⊢ ⊥` from the
  exact stock. RS itself supplies a nonempty `fun′`-only specification, so no
  separate `∃fun′` axiom is present. The proof derives collision injectivity,
  proves the existential diagonal pure, verifies both directions of its liar
  law, and eliminates both existential witnesses object-linguistically.
- T7a is now machine-proved in
  `theories/goodman/notes/Bacon_PP_Goodman_T7_Absorption.thy`.
  `CEV_Goodman_T7a` establishes the exact closed absorption result from
  `T₀ + PP + ∃fun′ + L2`, with no Inv/WI/TU/RS classification axiom.
  The object-language proof extracts the liar counterexample witnesses,
  obtains same-kind via weak L2, transports truth to `D(Zd)`, and eliminates
  all witnesses.
- T8 now has an exact 31-object encoding in
  `theories/goodman/notes/Bacon_PP_Goodman_T8_Encoding.thy`: the five advertised base
  operators, their 31 nonempty subsets, the corresponding kind properties,
  and literal pairwise-distinctness formulas for both operators and values.
  The file proves both lists have length 31 and type-checks the full target.
- T8b is machine-proved by `CEV_Goodman_T8_kind_uniqueness` in
  `theories/goodman/notes/Bacon_PP_Goodman_T8_Kind_Uniqueness.thy`.
- T8a is machine-proved by `CEV_Goodman_T8a` in
  `theories/goodman/notes/Bacon_PP_Goodman_T8_Base_Kinds.thy`.  The theorem packages all
  ten base-pair separations and uses no L2 or group-classification principle.
  The nonconstant cases use `fun′` closure under arbitrary group members;
  the constant cases use the checked left-absorption equations for `K⊤` and
  `K⊥`.
- T8c is machine-proved in
  `theories/goodman/notes/Bacon_PP_Goodman_T8_Growth.thy`.
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
  `CEV_proves_zeroary_recombination` in `theories/goodman/notes/Bacon_PP_Minimal_Axioms.thy`.
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

Fix 2 is in `theories/goodman/notes/Bacon_PP_Definable_Purity.thy`: `pp_definable_purity L F =
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
4. **Do not use `ContextVectorEquivalence`.** It is not part of this problem.
5. Sessions are split (`Higher_Order_Metaphysics`, `..._PP` in `theories/goodman/core/`,
   `..._PP_Frontier` in `theories/goodman/notes/`) specifically to keep iteration short. New
   work goes in `theories/goodman/notes/`; avoid editing the base session, which forces a
   full rebuild.
6. **Beware bare `auto`.** The `H_proves`/`C_proves`/`CE_proves`/`CEV_proves`/
   `compatible_step` constructors are all `[intro]`, so `auto` on goals in this
   development can search enormously. Prefer explicit `rule`/`intro`.

---

## 5. First Codex checkpoint: Unary Intensionality is complete

**Unary Intensionality in repo-CEV**, `theories/goodman/notes/Bacon_PP_Intensionality.thy`.
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

---

## 9. Current checkpoint: Goodman M1--M7 complete (2026-07-27)

The determinate model-theoretic suite is now formalized and green:

- M1 exact footnote-59 syntax, beta conversion, purity derivation, and the
  QSS/unique-`Fun` diagonal:
  `theories/goodman/notes/Bacon_PP_Goodman_M1_Complete.thy`.
- M2 definability-vs-invariance correction:
  `theories/goodman/notes/Bacon_PP_Goodman_M2.thy`.
- M3 countable gluing/free generator and explicit product-meagerness theorem:
  `theories/goodman/notes/Bacon_PP_Goodman_M3_Complete.thy`.
- M4 heredity calibration:
  `theories/goodman/notes/Bacon_PP_Goodman_M4.thy` and
  `theories/goodman/core/Bacon_PP_Heredity_Semantics.thy`.
- M5 rebuilt-model theorem via the formal Theorem 10.1 interface:
  `theories/goodman/models/hol_zf/Bacon_PP_ZF_Bacon_10_1.thy` and
  `theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_M5_Rebuild.thy`.
- M6 separation plus the strict inclusion obstruction to joint independence:
  `theories/goodman/notes/Bacon_PP_Goodman_M6.thy`.
- M7 countable-stock diagonal and failure of fundamental completeness:
  `theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_M7.thy`.

`isabelle build -D . -o timeout=60` passes. The next action is the promised
single Claude adversarial audit over the completed M-suite. After repairs, if
any, return to Goodman's consistency question with the M-results treated as
constraints on candidate stocks and rebuilt models.

For theory/dependency questions, use the project-native graph in
`isabelle-kg/graph.json`; rebuild it after theory edits with
`tools/isabelle_kg/build_graph.sh`. Graphify is no longer the project default.

---

## 10. Semantic L2 attack: exact tree model (2026-07-27)

The first recommended consistency-frontier attack is now implemented in
`theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_L2_Model.thy`.

The formal semantics uses exactly
`pp_b_closed_logical_operator_stock`: Boolean operators induced by denotations
of closed constant-free unary object-language terms. It does not silently
replace purity with the larger stock of ambient equivariant operators.

Checked results:

1. `pp_b_exact_fun_prime`, `pp_b_exact_reversible`, `pp_b_exact_G`,
   `pp_b_exact_same_kind`, `pp_b_exact_L2_pair`, and `pp_b_exact_L2` formalize
   Goodman's semantic notions.
2. `pp_b_exact_fun_prime_exists` supplies non-vacuity from the existing
   countable generic-separator theorem.
3. `pp_b_exact_stock_compose`, `pp_b_exact_G_compose`, and
   `pp_b_exact_same_kind_equivp` verify that the semantic kind action has the
   intended algebraic structure.
4. The five base operators are identified with exact closed logical
   denotations. Complement is also exact; hence so are `◇□` and `◇□¬`.
5. Exact-stock injectivity forces every `fun′` proposition to be nontrivial,
   non-fixed under `□` and `◇`, to satisfy `□p \neq \bot`, and to satisfy
   `◇p \neq \top`.
6. `pp_b_exact_base_collision_classification` proves that any equality
   `X p = Y q` on exact-stock `fun′` inputs, with `X,Y` among identity, truth,
   falsity, necessity, and possibility, forces `X=Y`.
7. `pp_b_exact_L2_on_base` therefore proves all twenty-five ordered base
   instances of semantic L2.
8. `pp_b_exact_not_L2_iff_counterexample` isolates the unresolved global
   target as a cross-input collision between exact closed logical operators
   that are not related by a closed-logical reversible.

The global L2 question remains open. The next move is no longer to retest the
five advertised base operators. Enlarge the classified stock to the modal
Boolean closure of the base operators. Seek a normal-form theorem strong
enough to classify cross-input collisions; if it fails, extract the first
explicit inequivalent pair as a semantic counterexample candidate.

---

## 11. Fresh CEV extension, rebuilt M5 model, and enlarged L2 fragment (2026-07-27)

### Fresh CEV extension

The independent `Goodman_CEVplus_Canonical` session now contains eight green
theories.  The principal results are:

1. relative Lindenbaum extension for CEV with an added stock of principles;
2. preservation of consistency while fresh Henkin witnesses are added;
3. a clean Henkin extension for every typed, consistent added stock with
   finite vocabulary;
4. a canonical-world existence theorem and
   `CEV_axiom_clean_canonical_valid_iff_proves_finite_vocabulary`;
5. proofs that the relevant Goodman stocks use only the nonlogical constants
   `Pure` and `Fun`; and
6. a term quotient with nonempty domains, constants, application, the closed
   truth lemma, Boolean and quantifier clauses, proposition-result beta
   equality, and open-substitution clauses for negation, implication, universal
   quantification, and existential quantification.

This does **not** prove the consistency of Goodman's theory plus PP.  The
construction assumes syntactic consistency and then produces its canonical
Henkin world.  The exact remaining semantic step is to turn environments of
term-equivalence classes into substitutions by representatives and prove that
evaluation is independent of those choices.  That evaluator must then be
placed in a system of worlds and substitutions on which the added principles,
including PP, are globally true.

### Rebuilt model for M5

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model.thy` now gives the full
rebuilt model requested in M5.  Its pure stock is the least stock closed under
application that contains every closed logical denotation and the repaired
exotic operator.  Isabelle verifies that this stock is countable, that the
exotic operator is pure, that one fundamental proposition supplies
Recombination and Fun-prime separation, and that the latter separation holds
at every world.  The resulting interpretation validates Bacon's
Recombination background.

The model does not yet satisfy PP.  PP remains the condition that the
classification of this very pure stock must itself occur at the next type.

### L2

The exact-stock L2 analysis now extends well beyond the original five
operators.

- `Bacon_PP_ZF_Goodman_L2_Composition_Fragment.thy` proves that every word
  formed by composing identity, negation, necessity, and possibility is
  distinction-preserving exactly when it is reversible.  Hence no
  nonreversible member of this entire composition fragment refutes L2.
- `Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers.thy` treats six closed
  logical unary operators containing quantification over proposition
  operators.  Their denotations are respectively necessity, necessity after
  negation, possibility after negation, possibility, constant falsity, and
  constant truth.  None is a nonreversible distinction-preserving operator.

Global semantic L2 for the complete stock of closed logical unary operators
remains open.  The fresh semantic attack and the L2 classification therefore
meet at the same next question: either prove a normal-form theorem for every
closed logical unary operator or find the first higher-order quantified term
whose denotation escapes the modal and constant classes.

---

## 12. Sparse model for every fragment without logical purity (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Sparse_Fragment_Model.thy` constructs an explicit
HOL-ZF tree interpretation in which:

1. PP is globally valid;
2. every application-closure instance is globally valid;
3. exactly one proposition is fundamental, and there are no fundamentals at
   any other type;
4. zeroary and unary Recombination and Exhaustion are globally valid; and
5. every instance of Modalized Functionality is globally valid, at arbitrary
   argument and result types.

The pure propositions and pure unary proposition operators are empty.  The
classifier of the empty unary stock is nevertheless pure at the next type,
which validates PP.  Thus the QLN clauses hold vacuously at arities zero and
one, while application closure remains valid at all types.

`theories/goodman/bridges/cevplus_zf/Bacon_PP_Fresh_ZF_Fragment_Bridge.thy` identifies the
fresh statement of Modalized Functionality with the established statement and
proves the exact fresh-stock result:

```isabelle
fresh_goodman_fragment_without_logical_purity_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema = {} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

The finite-fragment corollary is immediate, but the theorem is stronger: no
finiteness assumption on `U` is required.  Both builds are green:

```sh
isabelle build -v -d . -b Higher_Order_Metaphysics_PP_ZF_Model
isabelle build -v -d . -d fresh_attack -D fresh_attack_bridge
```

This is not a positive answer to Goodman.  It proves consistency of the whole
relevant stock except for logical purity.  The next construction problem is
therefore sharply localized: add the required closed-logical denotations to
the pure stocks while retaining PP and QLN.  The sparse model shows that PP,
QLN, fundamentality, application closure, and Modalized Functionality do not
by themselves generate the contradiction.

---

## 13. First logical-purity extension: proposition identity (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Identity_Fragment_Model.thy` adds the
logical-purity instance for the closed identity operator on propositions to
the sparse model.  At the level of world-relative equivalence classes, PP and
application closure give the following three-member closure:

1. truth at type `Prop`;
2. identity at type `Prop -> Prop`; and
3. the predicate that classifies the identity class at type
   `(Prop -> Prop) -> Prop`.

Isabelle proves directly that every application of a pure function in this
stock to a pure argument again lies in the stock.  It also proves global
validity of PP, unique proposition-level fundamentality, the absence of
fundamentals at every other type, zeroary Recombination and Exhaustion, unary
Recombination and Exhaustion, and Modalized Functionality at arbitrary types.
Unary Recombination is not obtained by emptying the unary pure stock: every
pure unary operator is equivalent to identity, and the unique fundamental
proposition is false at the evaluation world, so its image is not necessary.
Unary Exhaustion holds because identity is not true of every proposition.

The main model theorem is:

```isabelle
pp_identity_fragment_PP_axioms_consistent:
  CEV_axiom_consistent [] pp_identity_fragment_PP_axioms
```

`theories/goodman/bridges/cevplus_zf/Bacon_PP_Fresh_ZF_Fragment_Bridge.thy` verifies that this
axiom package is genuinely a subcollection of the independently formulated
fresh Goodman stock and proves:

```isabelle
fresh_goodman_identity_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema
    \<subseteq> {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

This strictly extends the earlier theorem for fragments containing no
logical-purity instance.  It does not settle Goodman's full question, but it
shows that the first natural logical-purity instance, together with the
application-closed enlargement it forces, does not produce an inconsistent
core.  The next controlled extension should add purity of negation and compute
the additional classes forced by application and PP.

Both relevant sessions are green:

```sh
isabelle build -d . Higher_Order_Metaphysics_PP_ZF_Model
isabelle build -d . -d fresh_attack -D fresh_attack_bridge
```

---

## 14. Second logical-purity extension: propositional negation (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Identity_Negation_Fragment_Model.thy` retains
purity of proposition identity and adds purity of propositional negation.
The application-closed pure stock consists of five world-relative
equivalence classes:

1. truth and falsity at type `Prop`;
2. identity and negation at type `Prop -> Prop`; and
3. the predicate classifying the identity-negation pair at type
   `(Prop -> Prop) -> Prop`.

The naive extension of the identity model fails.  Its unique fundamental
proposition is necessarily false.  Negation therefore sends it to necessary
truth, but negation is not true of every proposition, contradicting unary
Recombination.  Isabelle records this exact failure as
`pp_t_idneg_false_seed_does_not_recombine`.

The repaired model changes only the choice of fundamental proposition.  At
each world, the fundamental proposition is true throughout one immediate
branch and false throughout the other.  Identity and negation therefore both
send it to propositions that are not necessary.  This discharges unary
Recombination; unary Exhaustion holds because neither identity nor negation is
true of every proposition.  Zeroary Recombination and Exhaustion also hold
because both pure propositions are noncontingent.

The full model validates PP, both logical-purity instances, every
application-closure instance, unique proposition-level fundamentality, no
fundamentality at other types, all four zeroary/unary QLN clauses, and
Modalized Functionality at arbitrary types.  Its principal consistency
theorem is:

```isabelle
pp_identity_negation_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_identity_negation_fragment_PP_axioms
```

The bridge to Goodman's independently formulated stock proves:

```isabelle
fresh_goodman_identity_negation_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema \<subseteq>
    {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
     pp_pure (Prop \<rightarrow>\<^sub>o Prop)
       pp_negation_operator} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

The result is stronger than a finite-fragment theorem.  Every such
subcollection is consistent, without a finiteness assumption.  The next
controlled extension should add the closed constant-truth and constant-
falsity operators, or equivalently the closed constant-builder instances
that generate them, and recompute the QLN constraints.

---

## 15. Context-indexed size-4 finite-core search (2026-07-28)

The finite-core search now has a second engine that holds type depth at 1 and
term size at 4 while increasing proof-rule coverage. The implementation is:

- `finite_core_search/context_c_input.py`
- `finite_core_search/run_context_c_search.py`
- `finite_core_search/c_engine/finite_core_context1.c`
- `theories/goodman/cevplus/Bacon_PP_Fresh_Finite_Core_Search.thy`

The search state is keyed by `(context, formula)` for the empty context and
all six singleton contexts. The engine includes PC at the displayed formula
bound, UI, targeted EG, Ref, beta, eta, MP, Gen, Inst, zeroary and unary
Vector Equivalence, lazy Leibniz substitution, and the Boolean and Classicist
identities. Open-witness substitution is capture-avoiding.

The completed central-Recombination run used 1,432 pool axioms and reached a
fixed point with:

```text
13,094,962 derived context-indexed judgments
19,993,531 term nodes
46,891,177 cached substitutions
12.4 seconds
no derivation of ObjFalse
```

The durable result is
`finite_core_search/runs/context_c_size4/result.json` (generated runs are
ignored by Git). This is bounded non-derivability only. It does not establish
Goodman's consistency claim.

All new rule families have Isabelle replay lemmas and the
`Goodman_CEVplus_Canonical` session builds. The C engine has warning-clean builds,
static-analysis checks, sanitizer fixtures, and synthetic rule tests.

The next proof-search expansion should increase context/vector depth from 1
to 2, complete EG beyond the selected root templates, and add proof-trace
output to the context engine. A future positive hit is not an inconsistent
core until its trace replays in Isabelle.

---

## 16. Third logical-purity extension: constant truth and falsity (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Logical_Constants_Fragment_Model.thy` retains
purity of proposition identity and negation and adds purity of the closed
constant-truth and constant-falsity operators.  The application-closed pure
stock consists of seven world-relative equivalence classes:

1. truth and falsity at type `Prop`;
2. identity, negation, constant truth, and constant falsity at type
   `Prop -> Prop`; and
3. the predicate classifying those four unary operators at type
   `(Prop -> Prop) -> Prop`.

The theory proves the denotations and purity of all four unary operators, PP,
application closure at arbitrary types, unique proposition-level
fundamentality, the absence of fundamentals at every other type, both
directions of zeroary and unary QLN, and Modalized Functionality at arbitrary
types.  Unary QLN is divided into four explicit cases.  Identity and negation
use the contingent fundamental proposition from the preceding model.
Constant truth makes the relevant universal and necessary consequents true;
constant falsity makes the relevant antecedents false.

The exact HOL-ZF theorems are:

```isabelle
pp_t_logical_constants_fragment_PP_gvalid:
  ConstantsFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_logical_constants_fragment_PP_axioms

pp_logical_constants_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_logical_constants_fragment_PP_axioms

pp_logical_constants_fragment_consistent:
  U \<subseteq> pp_logical_constants_fragment_PP_axioms \<Longrightarrow>
  CEV_axiom_consistent [] U
```

`theories/goodman/bridges/cevplus_zf/Bacon_PP_Fresh_ZF_Fragment_Bridge.thy` proves:

```isabelle
pp_logical_constants_fragment_PP_axioms_subset_fresh_goodman:
  pp_logical_constants_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms

fresh_goodman_logical_constants_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema \<subseteq>
    {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
     pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_negation_operator,
     pp_pure pp_unary_ty (pp_constant_operator ObjTrue),
     pp_pure pp_unary_ty (pp_constant_operator ObjFalse)} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

The last result has no finiteness restriction.  It proves consistency only
for subcollections whose logical-purity instances are among those four.  It
does not prove consistency of Goodman's full theory.

The first two controlled extensions are now complete: the constant builder
`K` and curried conjunction are pure in successive verified models.  The
current target is a uniform closure result for curried truth-functional
operators.

The remaining obstacle is not these elementary truth functions.  It is the
full logical-purity schema for all higher-order closed logical terms,
especially the self-referential requirement imposed by Purity of Pure.

---

## 17. Fourth logical-purity extension: the constant builder \(K\) (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Constant_Builder_Fragment_Model.thy` adds purity
of the closed constant builder
\(K=\lambda p.\lambda q.p\), at type
`Prop -> (Prop -> Prop)`, to the preceding four purity instances.  Its
application to a pure true or false proposition yields the corresponding
constant-truth or constant-falsity unary operator already present in the pure
stock.  Isabelle proves that the enlarged stock remains closed under every
possible application of pure objects.

The model globally validates PP, unique proposition-level fundamentality, the
absence of fundamentals at every other type, zeroary and unary Recombination
and Exhaustion, every application-closure instance, and Modalized
Functionality at arbitrary types.  The formal background at this stage
contains only the zeroary and unary QLN clauses; no binary QLN theorem is
claimed.  The exact HOL-ZF theorems are:

```isabelle
pp_t_constant_builder_fragment_PP_gvalid:
  ConstantBuilderFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_constant_builder_fragment_PP_axioms

pp_constant_builder_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_constant_builder_fragment_PP_axioms

pp_constant_builder_fragment_consistent:
  U \<subseteq> pp_constant_builder_fragment_PP_axioms \<Longrightarrow>
  CEV_axiom_consistent [] U
```

`theories/goodman/bridges/cevplus_zf/Bacon_PP_Fresh_ZF_Fragment_Bridge.thy` proves:

```isabelle
pp_constant_builder_fragment_PP_axioms_subset_fresh_goodman:
  pp_constant_builder_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms

fresh_goodman_constant_builder_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema \<subseteq>
    {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
     pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_negation_operator,
     pp_pure pp_unary_ty (pp_constant_operator ObjTrue),
     pp_pure pp_unary_ty (pp_constant_operator ObjFalse),
     pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
       pp_constant_builder} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

This consistency theorem has no finiteness restriction.  It applies to every
subcollection of the fresh Goodman principles whose logical-purity instances
are among \(K\), identity, negation, constant truth, and constant falsity.  It
does not settle Goodman's question, since it does not cover all higher-order
closed logical terms or Purity of Pure.

The conjunction extension below supersedes this stated next step.

---

## 18. Fifth logical-purity extension: curried conjunction (2026-07-28)

`theories/goodman/models/hol_zf/Bacon_PP_ZF_Fresh_Conjunction_Fragment_Model.thy` imports the
constant-builder fragment and adds the closed logical term
\[
 \mathsf{And}=\lambda p{:}t.\lambda q{:}t.\,(p\wedge q).
\]
The semantic proof is application-closed without enlarging the proposition
or unary pure stocks.  At every world,
\(\mathsf{And}\,\top\) is equivalent to identity and
\(\mathsf{And}\,\bot\) is equivalent to constant falsity.  The only new
pure class is therefore the conjunction class at
`Prop -> (Prop -> Prop)`.

The model globally validates PP, every application-closure instance, unique
proposition-level fundamentality, no fundamentality at every other type,
zeroary and unary Recombination and Exhaustion, and Modalized Functionality.
The principal theorems are:

```isabelle
pp_t_conjunction_fragment_PP_gvalid:
  ConjunctionFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_conjunction_fragment_PP_axioms

pp_conjunction_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_conjunction_fragment_PP_axioms

pp_conjunction_fragment_consistent:
  U \<subseteq> pp_conjunction_fragment_PP_axioms \<Longrightarrow>
  CEV_axiom_consistent [] U
```

The fresh bridge proves:

```isabelle
pp_conjunction_fragment_PP_axioms_subset_fresh_goodman:
  pp_conjunction_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms

fresh_goodman_conjunction_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema \<subseteq>
    {pp_pure (Prop \<rightarrow>\<^sub>o Prop) prop_id,
     pp_pure (Prop \<rightarrow>\<^sub>o Prop) pp_negation_operator,
     pp_pure pp_unary_ty (pp_constant_operator ObjTrue),
     pp_pure pp_unary_ty (pp_constant_operator ObjFalse),
     pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
       pp_constant_builder,
     pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty)
       pp_conjunction_builder} \<Longrightarrow>
  CEV_axiom_consistent [] U
```

There is no finiteness restriction on `U`.  This is a six-purity-instance
fragment theorem, not consistency of the full logical-purity schema.  The
formal QLN stock remains zeroary and unary; no binary QLN claim is made.

This stated next step has now been completed by the uniform binary
truth-function extension below.

---

## 19. Uniform binary truth-function extension (2026-07-28)

The child session
`Higher_Order_Metaphysics_PP_ZF_Truth_Functions` contains
`theories/goodman/models/fragments/truth_functions/Bacon_PP_ZF_Fresh_Binary_Truth_Functions_Fragment_Model.thy`.
For every Boolean table \(F:\mathbf 2\times\mathbf 2\to\mathbf 2\), it defines
a closed curried object-language term
\[
  B_F=\lambda p{:}t.\lambda q{:}t.\,F(p,q)
\]
using only the existing Boolean logical vocabulary, together with its exact
HOL--ZF denotation.

The central closure theorem proves that, after fixing a pure proposition
\(p\), the unary slice \(B_Fp\) is world-relatively equivalent to one of the
four already pure unary operators:
\[
  C_{\top},\qquad I,\qquad N,\qquad C_{\bot}.
\]
Thus the extension adds the sixteen builder classes at
`Prop -> (Prop -> Prop)` but adds no proposition or unary pure class.

The model verifies:

```isabelle
pp_t_binary_truth_fragment_PP_gvalid:
  BinaryTruthFragment.MovingTreeConstants.TreeHenkin.gvalid_set
    pp_binary_truth_fragment_PP_axioms

pp_binary_truth_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_binary_truth_fragment_PP_axioms

pp_binary_truth_fragment_consistent:
  U \<subseteq> pp_binary_truth_fragment_PP_axioms \<Longrightarrow>
  CEV_axiom_consistent [] U
```

This includes all sixteen truth-function purity instances, PP, every
application-closure instance, unique proposition-level fundamentality, no
fundamentality at other types, zeroary and unary Recombination and Exhaustion,
and Modalized Functionality at arbitrary types.

The fresh bridge proves:

```isabelle
pp_binary_truth_fragment_PP_axioms_subset_fresh_goodman:
  pp_binary_truth_fragment_PP_axioms
    \<subseteq> fresh_goodman_axioms

fresh_goodman_binary_truth_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema
    \<subseteq> pp_binary_truth_allowed_purity \<Longrightarrow>
  CEV_axiom_consistent [] U
```

There is no finiteness restriction.  The allowed purity stock consists of
the six previously displayed formulas together with the uniform family
`pp_truth_function_purity_axioms`.  The formal QLN stock remains zeroary and
unary; no binary QLN theorem is asserted.

The next controlled extension is modal rather than another Boolean
truth-function.  Add
\(\lambda p.\Box p\) first and
\(\lambda p.\Diamond p\) second, in separate child theories.  For each, derive
the application-closed pure stock and test PP, both unary QLN directions,
Modalized Functionality, and fundamentality.  A failure in the present tree
model is not by itself a negative answer to Goodman: it must be classified as
either a seed/model obstruction or a model-independent derivation of
contradiction.

This stated next step has now been completed by the modal and
higher-order-quantified extension below.

---

## 20. Necessity, possibility, and six quantified operators (2026-07-28)

Three successive child sessions now extend the uniform Boolean model:

1. `Higher_Order_Metaphysics_PP_ZF_Necessity`;
2. `Higher_Order_Metaphysics_PP_ZF_Possibility`;
3. `Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified`.

The first two add the closed unary operators
\(\lambda p.\Box p\) and \(\lambda p.\Diamond p\).  Each model verifies PP,
every application-closure instance, unique proposition-level
fundamentality, no fundamentality at other types, zeroary and unary
Recombination and Exhaustion, and Modalized Functionality at arbitrary types.
The principal consistency results are:

```isabelle
pp_necessity_fragment_PP_axioms_consistent:
  CEV_axiom_consistent [] pp_necessity_fragment_PP_axioms

pp_possibility_fragment_PP_axioms_consistent:
  CEV_axiom_consistent [] pp_possibility_fragment_PP_axioms
```

The third session adds the six higher-order quantified unary operators
identified in Goodman's notes.  Isabelle proves their exact denotations:

\[
\begin{array}{rcl}
\text{Leibniz truth} &\equiv& \Box p,\\
\text{Leibniz falsity} &\equiv& \Box\neg p,\\
\text{negated Leibniz truth} &\equiv& \Diamond\neg p,\\
\text{negated Leibniz falsity} &\equiv& \Diamond p,\\
\text{universal application} &\equiv& \bot,\\
\text{existential application} &\equiv& \top.
\end{array}
\]

Necessary falsity and possible falsity are two new world-relative
equivalence classes of pure unary operators.  The theory proves Recombination
and Exhaustion for each, application closure for the full enlarged stock,
and:

```isabelle
pp_quantified_fragment_PP_axioms_consistent:
  CEV_axiom_consistent [] pp_quantified_fragment_PP_axioms
```

The bridge session `Goodman_CEVplus_Modal_Quantified_Bridge` proves:

```isabelle
fresh_goodman_modal_quantified_only_consistent:
  U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
  U \<inter> pp_purity_schema
    \<subseteq> pp_modal_quantified_allowed_purity \<Longrightarrow>
  CEV_axiom_consistent [] U
```

This covers arbitrary subcollections, not only finite fragments.  Its
logical-purity restriction includes the earlier Boolean stock, necessity,
possibility, and the six quantified formulas.  The formal QLN stock remains
zeroary and unary.

The 30-target session `Goodman_Modal_Quantified_Audit_2026_07_28` audits the
principal modal, quantified, and bridge theorem objects.  Every target has
zero oracle dependencies, zero theorem hypotheses, and zero flex-flex pairs.

This is genuine positive progress but not consistency of Goodman's complete
theory.  The next controlled construction must add higher-order closed
logical terms beyond these six while preserving the same principles.  A
complete result must cover every closed logical term at every type and the
self-referential Purity-of-Pure condition.
