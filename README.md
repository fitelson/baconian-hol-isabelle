# Higher-Order Metaphysics in Isabelle/HOL

This repository contains a deep embedding of the Bacon--Dorr higher-order
background logic and a separate Isabelle session for Jeremy Goodman's
Purity-of-Pure consistency question.

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

The `pp/` session formalizes Goodman's question:

> Is \(T_0\), together with QLN, exactly one fundamental proposition, no
> fundamental entities at other types, and Purity of Pure, consistent without
> assuming Purity of Fun?

Here QLN is divided into Recombination and Exhaustion so that the contribution
of each direction remains explicit.  The additional principles are treated as
axioms of CEV: Generalization, Instantiation, and vector Equivalence may still
be applied to conclusions obtained from them.

Goodman's question remains open.  The development verifies the determinate
T1--T9 and M1--M7 claims in the July 2026 notes, with the corrections and
qualifications stated in:

- [`reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf`](reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf);
- [`reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md`](reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md).

The dedicated audit checks the original 96 principal theorem objects plus five
new \(K\)-fragment and bridge results.  In particular, it
records the modal gap in T3, repairs the countability argument in M5, proves
the T6 contradictions and T9 counting result at their stated levels, and
separates what is proved in Bacon's appendix model from what remains
conditional.

### `Higher_Order_Metaphysics_PP_Frontier`

The `frontier/` session contains current proofs concerning Goodman's
object-language theorems, Bacon's appendix model, and the remaining consistency
question.  It is a leaf session over the stored heap of the PP session, so an
individual theory can be checked without rebuilding the stable base.

The present affirmative route asks for an enumerator \(E\) of unary operators
that respects Bacon's substitution action and satisfies
\[
  \mathcal C_E=\{E(n):n\in\mathbb N\},
\]
where \(\mathcal C_E\) is the class of unary operators denoted by closed
expressions built from the logical vocabulary, the natural-number indices,
\(E\), and application.  This equation is a sufficient condition for a model
of the relevant principles including PP.  No such enumerator, and no proof
that none exists, is currently known.

### `Goodman_Fresh_Attack`

The independent session in `fresh_attack/` imports only the foundational CEV
axiom-extension theory.  It proves that the full consistency question is
equivalent to consistency of every finite set of Goodman's additional
principles.  Equivalently, a negative answer requires one finite set from
which CEV derives falsity while retaining Generalization, Instantiation, and
vector Equivalence above the added principles.

```sh
isabelle build -v -d . -d fresh_attack -b Goodman_Fresh_Attack
```

That Henkin step is now complete.  For every typed, consistent stock of added
principles using only finitely many constants, the session constructs a clean
Henkin extension and proves canonical validity exactly when the formula is
derivable in CEV with those added principles.  Goodman's principal stocks meet
the finite-vocabulary condition: their only nonlogical constants are `Pure`
and `Fun`.

The associated term quotient now has nonempty domains, constants, application,
the closed truth lemma, the Boolean and quantifier clauses, and the
corresponding open-substitution clauses.  This remains a conditional
completeness result, not a proof that Goodman's theory plus PP is consistent.
The next step is to prove that evaluation is independent of the representatives
chosen for quotient classes, package the resulting denotable Henkin evaluator,
and supply the worlds and substitutions required for global validity.

The HOL-ZF bridge now gives an unconditional consistency result for the
largest presently constructed subtheory.  There is a tree model of PP,
application closure, unique proposition-level fundamentality, the absence of
fundamentals at every other type, zeroary and unary Recombination and
Exhaustion, and Modalized Functionality at arbitrary types.  The model omits
the logical-purity schema: it has no pure propositions or pure unary
proposition operators, while the predicate that classifies pure unary
operators is itself pure at the next type.  Consequently Isabelle proves that
every subset of the fresh Goodman stock containing no logical-purity instance
is CEV-axiom-consistent, and hence so is every finite such fragment.  Build the
bridge with:

```sh
isabelle build -v -d . -d fresh_attack -D fresh_attack_bridge
```

This does not settle Goodman's question, because the intended background
contains the logical-purity schema.  It identifies that schema, rather than
PP, QLN, fundamentality, application closure, or Modalized Functionality, as
the first family that the model construction must add.

The first such extension is now checked.  Add the logical-purity instance for
the closed identity operator on propositions.  PP and application closure then
require the pure truth proposition and the predicate that classifies the
identity class; those three equivalence classes are application-closed.  In
this enlarged HOL-ZF interpretation, PP, both zeroary and unary directions of
QLN, fundamentality, all application-closure instances, and Modalized
Functionality remain globally valid.  Isabelle consequently proves that every
subcollection of the fresh Goodman stock whose only logical-purity instance is
purity of the proposition identity operator is CEV-axiom-consistent.  This
result has no finiteness restriction.

Purity of propositional negation can also be added.  The resulting pure stock
contains truth and falsity, identity and negation, and the predicate
classifying the identity-negation pair.  Unary Recombination requires one
change to the preceding model: the unique fundamental proposition must be
contingent rather than necessarily false.  On the Boolean tree it is chosen
true on one immediate branch and false on the other.  Isabelle verifies that
PP, both zeroary and unary directions of QLN, fundamentality, application
closure, and Modalized Functionality all survive.  Every subcollection of the
fresh Goodman stock whose only logical-purity instances are identity and
negation purity is therefore CEV-axiom-consistent.

The next extension is also checked.  In addition to identity and negation, it
makes the closed constant-truth and constant-falsity operators pure.  The
application-closed stock has seven world-relative equivalence classes: truth
and falsity; identity, negation, constant truth, and constant falsity; and the
predicate classifying those four unary operators.  Isabelle proves global
validity of PP, all four displayed logical-purity instances, every
application-closure instance, unique proposition-level fundamentality, no
fundamentality at other types, zeroary and unary Recombination and Exhaustion,
and Modalized Functionality at arbitrary types.  The principal HOL-ZF theorem
is:

```isabelle
pp_logical_constants_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_logical_constants_fragment_PP_axioms
```

The bridge theorem
`fresh_goodman_logical_constants_only_consistent` applies this result to every
subcollection of the fresh Goodman principles whose logical-purity instances
are restricted to identity, negation, constant truth, and constant falsity.
This has no finiteness restriction.  It is not a proof of consistency for
Goodman's full theory, whose logical-purity schema includes all closed terms
formed from the logical vocabulary.

The constant builder \(K=\lambda p.\lambda q.p\) has now also been added.
The enlarged interpretation makes \(K\), identity, negation, constant truth,
and constant falsity pure.  Isabelle verifies PP, every application-closure
instance, unique proposition-level fundamentality, no fundamentality at other
types, zeroary and unary Recombination and Exhaustion, and Modalized
Functionality at arbitrary types.  Its principal theorem is:

```isabelle
pp_constant_builder_fragment_PP_axioms_consistent:
  CEV_axiom_consistent []
    pp_constant_builder_fragment_PP_axioms
```

The unrestricted bridge theorem
`fresh_goodman_constant_builder_only_consistent` covers every subcollection
of the fresh Goodman principles whose logical-purity instances are restricted
to \(K\) and the preceding four unary operators.  This is not a proof of
consistency for Goodman's full theory.  The next construction is curried
conjunction, followed by a uniform treatment of the curried truth-functional
operators.  The remaining obstacle is the full class of higher-order closed
logical terms, including the self-referential condition imposed by Purity of
Pure.

## Finite-core search

`finite_core_search/` contains the bounded search for a finite derivation of
falsity. The strongest completed tranche holds structural type depth at 1 and
logical term size at 4, but includes the empty context and every singleton
context together with PC, UI, targeted EG, Ref, beta/eta conversion, Leibniz
substitution, MP, Gen, Inst, and zeroary/unary Vector Equivalence.

That search reached a fixed point after 13,094,962 context-indexed judgments
without deriving `ObjFalse`. This is bounded non-derivability, not a
consistency proof. See
[`finite_core_search/README.md`](finite_core_search/README.md) for the exact
command, bounds, and certification boundary.

## Documentation terminology

Reader-facing documentation and Isabelle `text` blocks use the vocabulary of
Bacon, Dorr, and Goodman.  Stable Isabelle identifiers are not renamed.
[`docs/ISABELLE_TERMINOLOGY.md`](docs/ISABELLE_TERMINOLOGY.md) records the
translation between source terminology and implementation names.

## Verification

The project requires Isabelle2025-2 and no AFP or third-party theory.

```sh
isabelle build -D .
```

or:

```sh
./check_isabelle.sh
```

To iterate on the frontier only:

```sh
isabelle build -d . Higher_Order_Metaphysics_PP_Frontier
```

No active theory contains `sorry`, `oops`, `admit`, or `quick_and_dirty`.

Reader-facing terminology can be checked with:

```sh
./tools/check_goodman_documentation_vocabulary.sh
```
