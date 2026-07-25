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

The residual quantifier difficulty on route 2 is a dependency, not a
cardinality obstruction. The generic-witness theorem has the form

```text
for every Stock, there is an r with QLN(Stock, r)
```

whereas what is needed is

```text
there is an r with QLN(Stock(r), r)
```

because the stock of Pure-free denotations depends on `r` through `Fun`. The
paired-cone witness of `Bacon_PP_Symmetric_Witness.thy` is the natural raw
material for a priority or forcing construction that closes that gap, since it
leaves continuum-many cone pairs free after any countable list of requirements.

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
