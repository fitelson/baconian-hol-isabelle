# Formalization Status

Status date: 2026-07-25.

## Current verdict on Goodman's question

Open. We have neither a contradiction nor a complete model of PP plus the
Bacon--Dorr background and a fundamental proposition, with Purity of Fun
omitted.

The evidence now separates the problem into two parts.

1. The fundamental-proposition and QLN side is modeled by the generic-witness
   construction for any countable stock of invariant unary operators.
2. PP requires that the chosen pure stock classify itself. A large
   self-classifying stock can be obtained by an inflationary fixed-point
   construction, but no QLN witness is known for it. The Pure-free stock is
   countable and therefore has a QLN witness, but its self-classification is
   the remaining open condition.

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

### Tree-automorphism route

`Bacon_PP_TreeAut.thy` gives an explicit accessibility automorphism that
preserves the propositional Boolean/modal fragment but carries an invariant
unary operator, under conjugation, to a non-invariant one.

`Bacon_PP_TreeAut_Functions.thy` proves that the conjugation nevertheless
bijects Bacon's local unary function domain and preserves application:

```isabelle
pp_img_cone_equal_iff
pp_tree_conjugate_member_iff
pp_tree_conjugate_bijects_function_space
pp_tree_conjugate_can_destroy_invariance_inside_domain
```

This is evidence for a non-definability theorem, not yet that theorem.
Higher-type equality and the recursively induced conjugations at every type
must still be shown coherent before Pure-free definability can be inferred to
be tree-stable.

## Exact remaining consistency frontier

Let `L` be the stock of denotations of closed Pure-free terms. The current
model strategy succeeds if, for every Pure-free family
`Y : t -> (t -> t)`, the set

```text
{b : Y b is an invariant member of L}
```

is itself Pure-free definable. This is the remaining base-definability
condition.

There are now two live attacks:

1. complete the tree-conjugation coherence theorem and determine whether it
   yields a genuine counterexample to base definability;
2. bypass Pure-free base definability by constructing a countable or
   orbit-generic Henkin fixed point satisfying PP and QLN simultaneously.

Failure of the first route would not prove inconsistency. Success on the
second route would give an affirmative answer to Goodman.

## Hygiene

- No active theory imports Caie material.
- `ContextVectorEquivalence` is absent from the active logic.
- No active theory contains `sorry`, `oops`, `admit`, or
  `quick_and_dirty`.
- The complete active project builds with Isabelle2025-2.

Earlier Caie and contextual-rule material is preserved under
`quarantine/2026-07-24_pre_core_cleanup/`.
