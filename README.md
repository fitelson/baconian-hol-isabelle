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

The dedicated audit checks 96 principal theorem objects.  In particular, it
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

The next step is a Henkin extension theorem for this axiom-extension
consequence relation.

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

## Quarantine

The previous Caie development, the contextual strengthening of CEV, and model
experiments depending on them are preserved under
`quarantine/2026-07-24_pre_core_cleanup/`. Nothing there is imported by either
active session.
