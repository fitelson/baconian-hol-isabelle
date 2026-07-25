# Formalization Status

Status date: 2026-07-25.

## Current verdict on Goodman's question

Open. We have neither a contradiction nor a complete model of PP plus the
Bacon--Dorr background and a fundamental proposition, with Purity of Fun
omitted.

What has changed is that the problem is now much more sharply localized, and
one of the two previously live attacks has been closed off.

1. PP is not obstructed *semantically*. In the word-action M-set the purity
   predicate for unary propositional operators is itself invariant, hence pure,
   so the target PP instance is true there. What fails in that model is
   Recombination, because the full function domain gives an uncountable stock
   of classifier indices and no single witness escapes them all.
2. The purity operator is nevertheless not Pure-free definable. Adding it to
   the language is therefore a genuine enlargement of the Henkin domains, and
   the enlarged domains change which classifier indices the Recombination
   witness must escape.

The residual obstruction is exactly that circularity: a simultaneous choice of
a countable stock and of a witness generic for the stock that choice produces.

## Verified background

The active background session contains only H, C, CE, genuine theorem-level
CEV, and their semantic infrastructure. It proves clean Henkin completeness:

```isabelle
H_clean_Henkin_valid_iff_proves
C_clean_Henkin_valid_iff_proves
CE_clean_Henkin_valid_iff_proves
CEV_clean_Henkin_valid_iff_proves
```

It also proves consistency of the CEV identity-separator diagram and obtains
diagram-preserving quotient arrows:

```isabelle
CEV_identity_separator_consistent
CEV_identity_modal_successor
CEV_identity_arrow_separates_unequal_classes
```

The quotient/category semantics still needs a uniform fresh-name construction,
quotient-valued term evaluation, the quantifier clauses, and the full truth
lemma.

## Verified PP semantic machinery

### Generic witness and Bacon function spaces

`Bacon_PP_Generic_Witness.thy` proves a QLN witness theorem for every countable
stock of classifier indices.

`Bacon_PP_MSet.thy` formalizes Bacon's local unary function space and proves:

```isabelle
pp_fun_invariant_iff_equivariant
pp_equivariant_operator_is_classifier
pp_fun_invariant_is_classifier
pp_countable_invariant_function_stock_has_QLN_witness
```

Thus the classifier/generic-witness semantics is not an ad hoc replacement for
Bacon's function domain.

### PP holds in the word-action M-set; Recombination is what fails

`Bacon_PP_Purity_Operator.thy` gives the purity predicate at type
`(t -> t) -> t` its natural value and shows that value is invariant:

```isabelle
pp_purity_operator_root
pp_purity_operator_equivariant
pp_purity_operator_necessitated
pp_purity_operator_second_order_equivariant
pp_purity_of_pure_holds_in_word_action
```

So `Pure` for unary propositional operators is itself pure, and purity is
necessitated when true. With the full function domain, however:

```isabelle
pp_full_stock_has_no_recombination_witness
```

No proposition has an orbit escaping every proper classifier index, because the
orbit is indexed by words while the indices exhaust the powerset. The
consistency question is therefore a size question about the Henkin domains, not
a question about whether invariance is preserved.

### FIN-base is false

`Bacon_PP_LevelClasses.thy` constructs cyclic length-modulo partitions and one
Pure-free family realizing infinitely many pairwise distinct invariant unary
operators:

```isabelle
pp_cyclic_level_partition_iff
pp_cyc_family_values_pairwise_distinct
pp_cyc_family_realises_infinitely_many_invariant_values
```

The semantic combinatorics is machine-checked. The displayed Pure-free terms
for the construction have not yet been connected to a full deep-embedded
M-set term semantics.

### The naive uniform-index repair is false

`Bacon_PP_Uniform_Index.thy` proves:

```isabelle
pp_naive_IDX_base_counterexample
```

Equality to a value in the range of a Pure-free family does not imply that the
value is invariant. The same theory corrects the cyclic-family analysis:

```isabelle
pp_cyc_family_lifted_universal_not_invariant
pp_cyc_family_invariant_iff
```

The invariant base of the cyclic family is exactly:

```text
CycCarrier(b) or box (not CycCarrier(b)).
```

Hence this family refutes FIN-base but satisfies the desired Pure-free
base-definability condition.

### Exact general reduction

`Bacon_PP_Orbit_Stability.thy` proves for every equivariant binary family:

```isabelle
pp_binary_family_invariant_iff_parameter_orbit_stable
pp_parameter_orbit_stable_iff_root_fibre_stable
pp_binary_family_invariant_iff_root_fibre_stable
```

The open problem is therefore a parameter-freezing problem. Ordinary modal
evaluation moves every free parameter together, whereas invariance compares
the current root fibre with the fibre obtained after moving only the indexed
parameter.

## The tree-conjugation coherence diagram is complete

`Bacon_PP_TreeAut.thy` gives an explicit accessibility automorphism preserving
the propositional Boolean/modal fragment but carrying an invariant unary
operator, under conjugation, to a non-invariant one.
`Bacon_PP_TreeAut_Functions.thy` proves the domain and application obligations
at the single type `t -> t`.

`Bacon_PP_TypeCoherence.thy` now closes the remaining obligations at every
Bacon type. The recursion over types is carried by an Isabelle type class
`pp_dom` with three parameters: a carrier, the family of local equivalences the
monoid action induces, and the conjugation. The class deliberately omits the
action itself, since tree conjugation does not commute with it; what
conjugation does preserve is the induced local equivalences, and those suffice
to define higher-type identity, the local function domains, and the quantifier
domains. The single class axiom that drives everything is

```text
eqv i (conj x) (conj y)  =  eqv (tw i) x y
```

whose base instance is exactly `pp_img_cone_equal_iff`.

Nothing has been quietly replaced by a convenient substitute. At the concrete
type `t -> t` the class notions are proved to coincide with Bacon's own:

```isabelle
pp_carrier_fun_base_iff        (* the carrier IS pp_function_space_member *)
pp_eqv_fun_base_iff_fun_view   (* the equivalence IS equality of pp_fun_view *)
pp_fixed_fun_base_iff          (* the conjugation IS pp_tree_conjugate *)
```

Obligations now discharged at every Bacon type:

```isabelle
pb_id_conjugate   pb_id_carrier   pb_id_fixed     (* higher-type equality *)
pb_all_carrier    pb_all_fixed                    (* universal quantification *)
pb_ex_carrier     pb_ex_fixed                     (* existential quantification *)
pb_neg_fixed      pb_and_fixed    pb_box_fixed    (* Boolean and modal *)
pp_fixed_app      pb_K_fixed      pb_S_fixed      (* application, combinators *)
```

The last line is the induction on object-language terms: conjugation-fixedness
is closed under application, and `S` and `K` are fixed outright, so by
combinatory completeness every closed term built from fixed constants denotes a
fixed carrier element.

### The resulting non-definability theorem

```isabelle
pp_purity_not_conjugation_fixed
```

There is no conjugation-fixed carrier member at type `(t -> t) -> t` whose root
truth tracks invariance. Hence invariance is not definable from
conjugation-fixed constants.

### The signature side condition is discharged

The Pure-free language contains `Fun` as well as the logical constants, and in
the intended model `Fun` is the local identity predicate for the fundamental
proposition. So `Fun` is conjugation-fixed exactly when that witness is.
`Bacon_PP_Symmetric_Witness.thy` shows the witness can always be so chosen.
Local symmetrization fails --- gluing symmetric views cone by cone runs into the
proper index `{P. pp_swap_all P = P}` (`pp_symmetric_propositions_proper`).
Global symmetrization across the cone pair `[0, n]`, `[1, n]`, which `pp_tw`
exchanges, works:

```isabelle
pp_paired_witness_symmetric
pp_view_paired_witness
pp_symmetric_generic_witness_for_countable_proper_stock
pp_countable_stock_has_symmetric_generic_QLN_witness
pp_countable_function_stock_has_symmetric_QLN_witness
```

For every countable stock there is a QLN witness `R` with `pp_img R = R`.

## Correction: tree conjugation cannot refute base definability

This supersedes the earlier handoff's "recommended first attack". The
coherence diagram completes, and the non-definability theorem is real, but it
does **not** touch the base-definability condition. Machine-checked:

```isabelle
pp_stock_locus_conjugation_stable
```

The base-definability condition quantifies over the loci
`{b. Y b is an invariant member of L}`, where `L` is the stock of denotations of
closed Pure-free terms of type `t -> t`. Every member of `L` is
conjugation-fixed, so `L` is conjugation-stable and pointwise fixed, and for a
Pure-free family `Y` we have `Y (pp_img b) = pp_tree_conjugate (Y b)`. Then:

- if `Y b` is in `L`, then `pp_tree_conjugate (Y b) = Y b`, so the invariance
  claims at `b` and at `pp_img b` are literally the same claim;
- if `Y b` is not in `L`, the membership conjunct fails at both parameters.

Either way the locus is `pp_img`-stable. This is the cancellation the earlier
handoff warned about, and the argument uses nothing special about `pp_tw`: it
applies to every automorphism fixing the signature. The parity family is not a
counterexample either --- what its non-stability shows is that its values are
not in `L`, not that the locus moves.

**Tree conjugation is therefore removed from the list of live attacks on base
definability.** It refutes only the stronger claim that invariance is definable
as a predicate over the whole function domain at `t -> t`.

## Exact remaining consistency frontier

Two attacks remain, and they are no longer symmetric in promise.

1. Base definability, now known to be immune to automorphism arguments. Any
   refutation must come from a diagonal or counting argument that constructs a
   Pure-free family defeating an enumeration of candidate Pure-free
   definitions. Plain cardinality does not suffice: there are countably many
   Pure-free families and countably many Pure-free formulas, and one definable
   set may contain continuum-many propositions.
2. The alternative model route: construct a countable, orbit-generic,
   self-classifying Henkin stock. The generic-witness theorem already supplies
   QLN for *any* countable stock, so the whole difficulty is
   self-classification. Correctly typed, the condition is that the domain at
   `sigma -> Prop` contain the classifier of the pure elements of `sigma`; it is
   not a set membering itself, and simple typing blocks the Russell
   self-application, so there is no Cantor-style no-go in sight.

   Note where the cost is and is not. Reading `pp_unary_recombination` and
   `pp_unary_exhaustion` in `Bacon_PP_Question.thy`, the only nonzero-arity QLN
   instance required is the unary one, quantifying over the *pure* elements of
   the domain at `Prop -> Prop` together with the fundamental proposition. So
   the escapability burden falls only on the invariant part of that one domain.
   The domain at `(Prop -> Prop) -> Prop` may be as large as one likes, which is
   why housing the purity operator costs nothing by itself, and why the zeroary
   instances are free (pure propositions are `{}` or `UNIV`, and `pp_sem_box`
   fixes both). The entire difficulty is that the stock of pure elements at
   `Prop -> Prop` grows when the language is enlarged by `Pure` and by a name
   for the witness.

## The self-classifying stock: the priority problem largely collapses

`frontier/Bacon_PP_Stock_Requirements.thy` (see the session layout note below)
begins route 2, and the first finding is that most of the anticipated
priority/forcing machinery is not needed.

Every element of the term-generated domain at `t -> t` over the seed `r` is
`Y r` for an equivariant binary family `Y` in which the seed occurs only as the
argument: abstracting the seed turns `Fun` into `\x. \P. Id(P, x)`, and `Pure`
is `pp_purity_operator`, which is parameter-free and equivariant. And
`Bacon_PP_Orbit_Stability.thy` already proves that `Y r` is invariant exactly
when `Y` is constant on the orbit of `r`.

So build the witness to defeat orbit-constancy. For each *non-constant* family,
place two propositions separating it into the orbit; for each *constant*
family, place one proposition escaping the index of its constant value. Both
kinds of requirement are met by prescribing values at reserved cones, the
paired cones are independent and inexhaustible, and hence the requirements do
not interact: no priority ordering, no injury.

```isabelle
pp_prescribed_orbit_witness
pp_two_orbit_values_defeat_stability
pp_nonconstant_family_not_invariant
pp_countable_family_stock_has_generic_witness
```

The last is the main theorem: for every countable set of equivariant families
there is a tree-symmetric `r` such that every *invariant* value of the stock
comes from a globally constant family --- so it is parameter-free --- and
satisfies unary QLN. The pure part of the stock is thereby made independent of
the witness, which is what removes the circularity.

Sanity check, also proved: at such a witness `Fun` is *not* pure
(`pp_fundamentality_not_pure_when_required`), since it is the value of the
non-constant family `pp_operator_equal`. That is as it should be --- Purity of
Fun is exactly what this question does not assume, and a construction that made
it true for free would be answering a different question.

### What the collapse does not cover

The dependence of the family set on the seed is not fully removed, and the
residue is now identified exactly: it is the object-language *quantifier
domains*, and nothing else. `Fun` is handled by abstraction and `Pure` is
parameter-free, but a quantified term is interpreted over the Henkin domains,
which are generated from the seed.

This residue is not repaired by the separation requirements, and the reason is
worth recording. Consider a family of the shape

```text
Y b P  =  forall X in D. Psi X P
```

in which the parameter `b` does not occur. It is constant, so the separation
requirements never touch it, yet its index `{P. forall X in D. Psi X P}` moves
when `D` moves. So `pp_family_constant_index` gives
`index (Y_r r) = index (Y_r {})` but not `index (Y_r {}) = index (Y_s {})`, and
the escape requirement can no longer be posed independently of the seed. Nor
does a monotone union of domains repair it: enlarging a domain changes the
denotation of quantified terms already present, so it is not merely that new
families arrive. A stage-wise construction would additionally need a
persistence theorem, to the effect that each term's denotation is eventually
constant along the chain of domains.

What can be stated exactly is the hypothesis under which the construction goes
through unchanged, and it is now a theorem:

```isabelle
pp_seed_dependent_stock_has_generic_witness
pp_uniform_envelope_gives_generic_witness
```

If one countable set of propositions covers the requirements of every family
that any seed can produce --- for instance because a single countable envelope
`Fam0` contains `Fam s` for every seed `s` --- then the witness exists outright,
with no priority ordering and no injury. **The remaining obligation on route 2
is therefore that one uniformity condition on the object language, not a
forcing construction.**

Two scope notes on this part. The conclusion is root-level QLN; validating PP
at every world with `Fun_r = pp_operator_equal r` needs the corresponding
tail-orbit requirements as well, and the all-worlds guarded theorem in
`Bacon_PP_Generic_Witness.thy` uses a different, shifting-fundamental
presentation that cannot simply be substituted. And none of this yet shows the
resulting structure models H, Classicism, CE and CEV.

## Attacking the uniformity condition

Two results, both machine-checked. Neither proves the condition; together they
shrink it and close off the obvious way of achieving it.

### The requirement reduces to a diagonal set

`frontier/Bacon_PP_Diagonal_Reduction.thy`. For an equivariant binary family
`Y` put `D_Y = {b. Y b b is true at the root}`. Then:

```isabelle
pp_equivariant_diagonal_is_classifier   (* Y b b = pp_classifier D_Y b *)
pp_orbit_index_iff_diagonal             (* the reduction *)
```

The second says that when `Y r` is pure --- equivalently, when `Y` is constant
along the orbit of `r` --- the orbit sits inside `pp_operator_index (Y r)`
exactly when it sits inside `D_Y`. Note it needs only orbit-stability, not
equivariance.

This matters because `pp_operator_index (Y r)` is the quantity whose
seed-independence was in doubt, and `D_Y` is a function of the family alone: it
does not mention the seed and is obtained by a single root-truth test rather
than by evaluating `Y` at the seed. The construction also shrinks to one
required proposition per family instead of three, with separators needed only in
the degenerate case where the diagonal is universal and the family is
non-constant --- a constant family with universal diagonal has a universal index
outright (`pp_constant_family_diagonal`):

```isabelle
pp_diagonal_stock_witness
pp_diagonal_envelope_witness
```

### The domains cannot be frozen by choosing the seed inside them

`frontier/Bacon_PP_Seed_Nontriviality.thy`. The cheapest route to
seed-independence would be to take the seed from a domain that was already
closed before the seed was introduced --- the term model over the seed-free
language. Adjoining it would then enlarge nothing, the domains would stay
fixed, and the envelope hypothesis would hold outright.

That route is now closed. A closed seed-free term has no free parameter, so its
denotation is invariant, and the only invariant propositions are `{}` and
`UNIV`. An invariant proposition has a one-point orbit, and a one-point orbit is
trapped inside a proper classifier index:

```isabelle
pp_invariant_orbit_singleton
pp_invariant_seed_fails_recombination
pp_no_seed_inside_an_invariant_domain
```

The trap is not exotic. The two relevant classifiers are exactly the modal
operators,

```isabelle
pp_box_is_classifier_UNIV        (* pp_sem_box     = pp_classifier {UNIV} *)
pp_box_neg_is_classifier_empty   (* pp_sem_box o - = pp_classifier {{}}   *)
```

so they are Pure-free definable and belong to any stock closed under the
logical constants. The failure cannot be dodged by trimming the stock:

```isabelle
pp_extreme_seed_fails_definable_recombination
pp_seed_must_be_contingent
pp_seed_not_extreme
```

**The fundamental proposition must therefore be genuinely contingent, and must
lie outside every seed-free domain.**

### Requirements only where they are needed

`frontier/Bacon_PP_Seed_Aware_Requirements.thy`. The requirement sets above are
imposed on every family whether or not it causes trouble at its own seed, and
that waste is not harmless: it can demand escapes that are impossible to
supply. The guarded version imposes a requirement only when the value at the
seed is pure and its index is proper:

```isabelle
pp_seed_aware_diagonal_stock_witness
pp_seed_aware_below_diagonal          (* the guarded cover is the weakest *)
```

The sharpest instance is the membership test `T = \b. \c. exists X:Prop. Id(X,b)`
below: its diagonal is the whole proposition domain, so the unguarded
requirement demands a proposition escaping the domain, yet its value at its own
seed has universal index and satisfies QLN outright. The guarded cover drops it.

### Verdict: the envelope condition is false

Not merely unproved. The argument, which is meta-level because it turns on the
term semantics:

1. A seed belongs to its own domain, so each fibre of `s |-> D_Prop(s)` is
   countable; continuum-many seeds therefore give continuum-many distinct
   proposition domains.
2. The membership test `T = \b. \c. exists X:Prop. Id(X,b)` has diagonal set
   exactly `D_Prop(s)`, since root-level identity is genuine equality. So `T`
   turns distinct domains into distinct families.
3. Hence the union of the family sets over all seeds has the cardinality of the
   continuum, and no countable `Fam0` contains every `Fam s`.

One correction to an earlier draft of this note. The obvious candidate
`\b. \c. forall X. (X --> c)` does **not** witness seed-dependence: whenever the
domain contains `UNIV`, as any logical domain must, that term has value `c` and
its diagonal is seed-independent. The membership test is what does the work.

### Verdict: no generic fixed-point theorem is available either

The seed space is Cantor space, which is compact Polish, but that alone gives
no fixed point --- continuous self-maps of Cantor space can be fixed-point-free.
Nor is there monotonicity to exploit: `exists X. Id(X,b)` makes the diagonal
`D_Prop(s)` while `forall X. not Id(X,b)` makes it the complement, so existential
and universal occurrences have opposite variance and quantifier alternation
destroys any uniform order behaviour. `pp_escape` is defined by `SOME` and has
no reason to be continuous or monotone. So Banach needs a guardedness theorem
that is not available, Knaster--Tarski needs monotonicity that fails, and Baire
category yields no fixed point.

### Where that leaves the route

The shape of the problem has changed even though it is not solved. What must be
uniform is now the family of diagonal sets rather than indices of seed-evaluated
operators; the requirement set has been cut to those families that actually
cause trouble; the natural way of freezing the domains is refuted; the envelope
form of the hypothesis is false; and the off-the-shelf fixed-point theorems are
ruled out.

## The persistence theorem: false in general, with two usable substitutes

`frontier/Bacon_PP_Domain_Persistence.thy`. The stage-wise construction would
need each term's denotation to settle down along an increasing chain of domains.
It does not.

### It fails

```isabelle
pp_universal_denotation_does_not_persist
```

Along an increasing chain whose stages are even *finite*, the denotation of the
single term `forall X : Prop. X` --- read semantically as
`pp_forall_over D id` --- differs from its limit value at **every** finite stage.
The chain is `D n = {- {0^k} | k < n}`, so the stage values are
`- {0^k | k < n}`, strictly decreasing forever. A stage-wise construction
therefore cannot assume persistence; it has to earn it.

### Substitute one: the limit is always recoverable from the stages

```isabelle
pp_forall_over_Union    (* limit = intersection of the stage values *)
pp_exists_over_Union    (* limit = union of the stage values        *)
```

Neither needs the chain to be increasing. The limit denotation need not equal
any stage denotation, but it is always determined by the sequence of them. For a
fusion construction this is the correct replacement for persistence.

### Substitute two: persistence under a finite-image bound

```isabelle
pp_finite_image_persistence
```

If the quantified body takes only finitely many values over the limit domain,
the denotation does stabilize. This is exactly what the counterexample violates
--- there the body is the identity and takes infinitely many values. Note this
is a condition on the term and the limit domain together, not on the chain.

### Persistence is exactly finite attainment

```isabelle
pp_persistence_iff_attained
```

For an increasing chain the stage values decrease, so eventual stabilization is
equivalent to the limit value being reached at one single finite stage. That
converts persistence from a statement about tails into a concrete attainment
question.

### Variance, and why Knaster--Tarski is unavailable

```isabelle
pp_forall_over_antitone
pp_exists_over_monotone
```

Universal quantification is antitone in the domain and existential quantification
is monotone. Both variances are realized, so a term with alternating quantifiers
has no uniform variance in the domain. This is the checked form of the
obstruction noted earlier.

## Do Henkin closure chains admit finite-image bounds? No --- but that was the
## wrong condition, and the right one holds

`frontier/Bacon_PP_Attainment.thy`. This answers the question left open above,
and in doing so it defuses the counterexample.

### Finite image is unusable here

The simplest quantified term of all, `forall X : Prop. X`, has the identity as
its body, so its image over the limit domain *is* the limit domain, which is
infinite in any nondegenerate model:

```isabelle
pp_identity_image_is_the_domain
pp_identity_body_has_no_finite_image_bound
```

So no Henkin chain satisfies the finite-image hypothesis for that term.

### Attainment is the right condition, and it is weaker

What the proof of `pp_finite_image_persistence` actually uses is only that some
*finite* part of the domain already cuts the intersection down to its limit
value:

```isabelle
pp_finitely_attained            (* the definition *)
pp_finitely_attained_persistence
pp_finite_image_gives_attainment   (* finite image is a special case *)
```

### Closure supplies attainment exactly where finite image fails

Comprehension puts the value of `forall X. X` into the domain at the quantified
type. That single element attains the intersection, so persistence holds for the
identity body however large the domain is:

```isabelle
pp_closed_domain_attains_identity
pp_closed_domain_identity_persistence
```

More generally a monotone body attains at the least proposition and an antitone
body at the greatest, and any domain closed under the Boolean connectives
contains both `{}` and `UNIV`:

```isabelle
pp_monotone_body_attains
pp_antitone_body_attains
```

### The counterexample is not a Henkin chain

```isabelle
pp_counterexample_domain_not_closed
```

The chain that refutes persistence has a limit domain that provably does *not*
contain the value of `forall X. X` over it. So it is not closed under
comprehension, and the refutation does not transfer to the chains we care
about. The earlier negative result stands as stated --- persistence is not a
general fact about increasing chains --- but it does not obstruct the
construction.

### The remaining gap is real: non-contingency defeats attainment

`frontier/Bacon_PP_Attainment_Failure.thy`. The gap left above --- bodies at
quantified type `Prop` that are neither monotone nor antitone --- is not
hypothetical, and the counterexample is about as innocent as it could be.

The body is **non-contingency**, `f X = box X or box (not X)`. It is Pure-free,
parameter-free, and of modal depth one, and it is mixed in variance exactly as
predicted:

```isabelle
pp_decided_not_monotone     (* {} is decided everywhere, its supersets need not be *)
pp_decided_not_antitone     (* UNIV likewise *)
```

The domain is generated by `C_n = {w. length w <= n}`. A world `i` decides `C_n`
exactly when `n < length i`:

```isabelle
pp_decided_shortprop
```

Deep enough into the tree the cone holds only long words and `C_n` is uniformly
false there; at shallower worlds the cone holds both short and long words. So the
sets of deciding worlds shrink to nothing, while every *finite* family of
generators is still decided somewhere. Hence:

```isabelle
pp_decided_defeats_attainment
pp_decided_denotation_does_not_persist
```

Crucially this is not an artefact of taking too small a domain. Decidedness is
inherited by complements, intersections and boxes:

```isabelle
pp_decided_Compl   pp_decided_Int   pp_decided_box
```

so generating a Boolean and modal algebra from the `C_n` leaves the deciding
worlds exactly where they were. The positive results really do stop at the
monotone and antitone cases.

### Caveat, and what is now open

What has been exhibited is a legitimate domain of propositions closed under the
connectives and the modality --- the form in which the question was posed. It is
*not* a domain shown to arise as the Henkin closure of a language over a seed.
To promote this into an obstruction for the consistency construction one would
still have to realize the `C_n`, or something with the same decidedness
behaviour, as denotations of terms over a seed. That looks plausible, since
`C_n` is a depth predicate and the seed is contingent by `pp_seed_not_extreme`,
but it is not proved and should not be assumed.

So the position is symmetric and sharp. Persistence holds for monotone and
antitone bodies by closure; it fails for a simple mixed body over a
Boolean-and-box-closed domain; and the single remaining question is whether that
failure can be realized inside a seed-generated domain.

## Can it be realized over a seed? Almost certainly not

`frontier/Bacon_PP_Decided_Realization.thy` takes up that question, and the
answer is negative for the closure that a single seed actually generates.

### Deciding worlds form an up-set

```isabelle
pp_decided_deeper
pp_decided_accessible
```

If `X` is decided at `i` it is decided at every deeper world, so each set of
deciding worlds is an up-set and the counterexample needs a strictly decreasing
sequence of up-sets with empty intersection.

### A refutation test: one nowhere-decided proposition kills it

```isabelle
pp_nowhere_decided_gives_attainment
pp_parity_nowhere_decided
pp_domain_with_parity_attains
```

If the domain contains even one proposition decided *nowhere*, the intersection
is already empty at that single element and attainment holds. Such propositions
exist in abundance in the ambient model --- every parity proposition is one.

This should not be oversold, and Codex was right to push back on an earlier
draft that did. Genericity does **not** force a nowhere-decided Boolean or modal
combination of the seed; quite the reverse, at a world where `pp_view i r` is
extreme that same world decides every Boolean and modal term in `r`. So this is
a way of killing a proposed realization when it happens to apply, not an
obstruction guaranteed to fire.

### The obstruction that does fire: finitely generated domains always attain

Decidedness passes through the Boolean connectives, the modality, and --- as
Codex pointed out --- propositional identity as well, since local identity just
*is* a boxed biconditional here:

```isabelle
pp_operator_equal_is_boxed_biconditional
pp_bmclosure_operator_equal
```

So a world deciding a generating family decides everything the family generates:

```isabelle
pp_bmclosure                (* Boolean-and-modal closure, inductively *)
pp_decided_bmclosure
pp_bmclosure_attains
pp_single_seed_closure_attains
```

Hence a domain generated by **finitely many** propositions always attains, at
its generators. In particular the closure of a single seed under Booleans, box
and identity always attains, and **the attaining element is the seed itself** ---
whether or not any nowhere-decided proposition is around.

A related check, agreed with Codex: a *length-only* seed cannot define the `C_n`
at all. If `r = {w. length w in E}`, the generated submodel is the linear
reflexive frame with valuation `E`; if `E` is not eventually constant then
`box E = box (-E) = {}` and the algebra is inside `{{}, UNIV, E, -E}`, while if
`E` is eventually constant every generated set is too. Either way the
one-generated Boolean-modal algebra is *finite*, so it cannot contain infinitely
many distinct `C_n`.

### Verdict

The counterexample **cannot** be realized from the closure of a seed under the
Boolean connectives, the modality and propositional identity. Any realization
must get its non-attainment from the quantifiers, from higher-type
constructions, or from `Pure`, and there it would have to manufacture infinitely
many propositions with the finite intersection property on deciding worlds and
empty total intersection, while producing neither a nowhere-decided proposition
nor any finite attaining family.

Realization in the *full* Henkin closure is therefore still open, and neither of
us can construct it or rule it out. Both Claude and Codex judge it unlikely, but
that is a judgement and not a proof. The counterexample of
`Bacon_PP_Attainment_Failure.thy` accordingly stays a statement about
Boolean-and-box-closed domains, exactly as stated there.

## The finite decision basis is proved, and the quantifiers do not break it

`frontier/Bacon_PP_Decision_Basis.thy`. The target above is now a theorem, and
in the strong form that was expected to fail.

The suspicion was that quantification breaks the induction, because a bound
variable ranges over propositions that need not be decided wherever the seed is.
That is unfounded. A universally quantified denotation is just an intersection,
`pp_forall_over D f = Inter (f ` D)`, and what has to be decided is not the bound
variable but the *body's value*, which is itself a domain element. And
decidedness is preserved by arbitrary intersections, since an intersection of
sets each `{}` or `UNIV` is again `{}` or `UNIV`:

```isabelle
pp_view_Inter
pp_decided_Inter
```

Existential quantification follows, being a complement of an intersection of
complements. So decidedness at a world is preserved by complement, the modality,
and arbitrary intersection --- which between them cover the Boolean connectives,
propositional identity, and quantification **at every type**:

```isabelle
pp_qclosure                    (* the logical closure, inductively *)
pp_decided_qclosure
pp_qclosure_operator_equal
pp_qclosure_forall
pp_qclosure_exists
```

Hence the target theorem, and its strong single-seed form:

```isabelle
pp_qclosure_finite_decision_basis
pp_seed_decision_basis          (* ALL X : D. pp_decided r <= pp_decided X *)
pp_seed_domain_attains_decided
pp_counterexample_not_realizable_over_seed
```

**The non-contingency counterexample cannot be realized inside the Pure-free
logical closure of a seed, at any type.** The seed alone is a decision basis.

The contrapositive is the tool to reach for when testing any future proposed
realization:

```isabelle
pp_non_attaining_domain_not_finitely_generated
```

a domain that fails to attain is not contained in the logical closure of any
finite set of its members.

### Scope: `Pure` is not covered, and why

The closure covers the Boolean connectives, the modality, propositional identity
and quantification at every type. It does not cover `Pure`, and that is not an
oversight. A purity value is necessitated, so its views are upward closed --- but
upward closed is not the same as `{}` or `UNIV`. A local function whose views are
invariant at every world of positive depth but not at the root has a purity value
undecided at the root, however the seed behaves there. So decidedness is not
preserved by `Pure` and the induction has no case for it.

That leaves a clean division. Inside the Pure-free logical fragment generated by
a seed the counterexample is dead. Any realization must run through `Pure`
itself --- which puts the burden back on the very predicate whose consistency is
at issue.

## Session layout and build times

The project is split so that work in progress verifies quickly.

- `Higher_Order_Metaphysics` --- the background session.
- `Higher_Order_Metaphysics_PP` in `pp/` --- settled PP results. Stable base.
- `Higher_Order_Metaphysics_PP_Frontier` in `frontier/` --- work in progress, a
  leaf session over the stored heap of the PP session, with
  `options [timeout = 60]`.

Editing a frontier theory rebuilds only that theory, in about five seconds; the
whole project rebuilds in a few seconds when cached. The timeout makes a
runaway proof fail fast with a line number instead of hanging the build. Move
theories down from `frontier/` into `pp/` once they are settled.

## Scope notes

- `pp_purity_not_conjugation_fixed` is an internal theorem about
  conjugation-fixed carrier members. The step from it to "Purity is not
  Pure-free definable" uses combinatory completeness at the meta level, each of
  whose steps is one of the checked closure theorems above, together with
  fixedness of the non-logical constants, which
  `Bacon_PP_Symmetric_Witness.thy` supplies for `Fun`.
- `Bacon_PP_TypeCoherence.thy` establishes the recursive carriers,
  conjugations, higher-type identity, and quantifier coherence. It does not
  contain a deep-embedded object-language term-denotation induction, and does
  not by itself establish that the construction models H, Classicism, CE, and
  CEV at every recursively generated type. Those remain open.
- At a function type, `pp_eqv []` is extensional equality on the carrier, not
  HOL equality on arbitrary representatives. Statements about `L` should be
  read modulo that equality. At `t -> t` the source carrier is everything, so
  there the two coincide.

## Hygiene

- No active theory imports Caie material.
- `ContextVectorEquivalence` is absent from the active logic.
- No active theory contains `sorry`, `oops`, `admit`, or
  `quick_and_dirty`.
- The complete active project builds with Isabelle2025-2.

Earlier Caie and contextual-rule material is preserved under
`quarantine/2026-07-24_pre_core_cleanup/`.
