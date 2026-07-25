# Higher-Order Metaphysics in Isabelle/HOL

This repository contains a deep embedding of the Bacon--Dorr higher-order
background logic and a separate Isabelle session for Jeremy Goodman's
Purity-of-Pure consistency question.

The active development contains no Caie-specific axiom or theorem.
`CEV_proves` has the theorem-level vector Equivalence rule only; the former
`ContextVectorEquivalence` rule is not part of the theory.

## Sessions

### `Higher_Order_Metaphysics`

The background session develops:

1. typed higher-order syntax, substitution, beta and eta conversion;
2. Bacon's deductive system H;
3. Classicism C;
4. propositional Equivalence CE;
5. vector or zeta Equivalence CEV;
6. clean Henkin completeness through CEV;
7. local intensional quotients and diagram-preserving arrows.

In particular, Isabelle proves:

```isabelle
H_clean_Henkin_valid_iff_proves
C_clean_Henkin_valid_iff_proves
CE_clean_Henkin_valid_iff_proves
CEV_clean_Henkin_valid_iff_proves

CEV_identity_separator_consistent
CEV_identity_modal_successor
CEV_identity_arrow_separates_unequal_classes
```

The full category-level truth lemma still requires the uniform Henkin-name
reserve and the quotient-valued evaluation construction described in
[`STATUS.md`](STATUS.md).

### `Higher_Order_Metaphysics_PP`

The `pp/` session studies whether PP is consistent with the Bacon--Dorr
background and the existence of a fundamental proposition, without assuming
Purity of Fun.

The current machine-checked results include:

- the finite-word right-division action and a generic QLN witness for every
  countable stock of invariant unary operators;
- Bacon's local unary function space and its action;
- the representation of every invariant unary function-space element as a
  classifier;
- an explicit Pure-free cyclic family with infinitely many distinct invariant
  values, refuting the proposed FIN-base route;
- a counterexample to the proposed uniform-index replacement;
- the exact invariant base of the cyclic family:

  ```isabelle
  pp_cyc_family_invariant_iff
  ```

  Its right-hand side is the semantic reading of the Pure-free condition
  `CycCarrier(b) or box (not CycCarrier(b))`.

- the general orbit-stability reduction:

  ```isabelle
  pp_binary_family_invariant_iff_parameter_orbit_stable
  pp_binary_family_invariant_iff_root_fibre_stable
  ```

- a tree automorphism preserving the propositional Boolean/modal fragment but
  not invariance of unary operators;
- preservation of Bacon's unary function domain and application under the
  induced tree conjugation;
- the completed all-type coherence diagram for that conjugation, carried by a
  type class whose instances are generated from a propositional base type by a
  function-space instance, including higher-type identity, the quantifier
  domains, application, and the `S`/`K` combinators;
- the resulting non-definability theorem

  ```isabelle
  pp_purity_not_conjugation_fixed
  ```

- that PP itself is *true* in the full word-action M-set, since the purity
  operator is invariant, while Recombination is what fails there:

  ```isabelle
  pp_purity_of_pure_holds_in_word_action
  pp_full_stock_has_no_recombination_witness
  ```

- a tree-symmetric generic QLN witness for every countable stock, built by
  pairing the cones `[0, n]` and `[1, n]`:

  ```isabelle
  pp_countable_stock_has_symmetric_generic_QLN_witness
  ```

Goodman's consistency question is not yet settled. The exact remaining model
obligation is a countable or orbit-generic self-classifying pure stock.

One correction to the earlier reading of the tree-automorphism route: it
refutes definability of invariance over the whole function domain, but it
cannot refute the base-definability condition, because every stock locus is
automatically stable under any signature-fixing automorphism
(`pp_stock_locus_conjugation_stable`). See [`STATUS.md`](STATUS.md).

## Verification

The project requires Isabelle2025-2 and no AFP or third-party theory.

```sh
isabelle build -D .
```

or:

```sh
./check_isabelle.sh
```

No active theory contains `sorry`, `oops`, `admit`, or `quick_and_dirty`.

## Quarantine

The previous Caie development, the contextual strengthening of CEV, and model
experiments depending on them are preserved under
`quarantine/2026-07-24_pre_core_cleanup/`. Nothing there is imported by either
active session.
