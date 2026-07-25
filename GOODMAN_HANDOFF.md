# Goodman PP Consistency: Handoff to Claude

## Objective

Settle Jeremy Goodman's question:

> Is PP consistent with the Bacon--Dorr background theory plus the existence
> of a fundamental proposition, when Purity of Fun is not assumed?

Work only with the Bacon--Dorr background, Classicism, theorem-level CE/CEV,
and the PP/QLN package. Caie and `ContextVectorEquivalence` are not part of
this problem.

## Start here

Read, in order:

1. `STATUS.md`
2. `README.md`
3. `pp/Bacon_PP_MSet.thy`
4. `pp/Bacon_PP_Uniform_Index.thy`
5. `pp/Bacon_PP_Orbit_Stability.thy`
6. `pp/Bacon_PP_TreeAut.thy`
7. `pp/Bacon_PP_TreeAut_Functions.thy`

Then run:

```sh
isabelle build -D .
```

The repository should be green before any new work.

## Verified frontier

- The background H/C/CE/CEV completeness reconstruction is green and uses only
  genuine theorem-level CEV.
- For every countable stock of invariant unary operators, the word-action
  model has a generic fundamental witness satisfying unary QLN.
- Bacon's actual local unary function space is formalized. Its invariant
  elements are exactly classifiers.
- FIN-base is false: the cyclic family realizes infinitely many distinct
  invariant Pure-free values.
- The naive IDX/range repair is false.
- The cyclic family's actual invariant base is Pure-free definable:

  ```text
  CycCarrier(b) or box (not CycCarrier(b)).
  ```

- For an arbitrary equivariant binary family `Y`, Isabelle proves:

  ```text
  Y b invariant
    iff Y is constant on the action orbit of b
    iff the root fibre of Y is unchanged after moving only b.
  ```

This is the precise parameter-freezing obstruction.

## Do not regress these corrections

1. Equality to a ranged value does not imply invariance. Bound witnesses inside
   `box` move with the world.
2. An empty root fibre does not make a unary value the false invariant
   operator. A later fibre can become nonempty.
3. The cyclic family refutes FIN-base but does not refute the base-definability
   condition.
4. No result currently settles consistency.
5. The semantic cyclic construction is machine-checked, but the displayed
   Pure-free terms have not yet been connected to a full deep-embedded M-set
   evaluation theorem.
6. Non-definability of invariance over the whole domain does not give
   non-definability of a stock locus. The `in L` conjunct cancels the effect of
   moving the parameter. This is now the theorem
   `pp_stock_locus_conjugation_stable`; do not re-open the automorphism route
   against base definability.
7. `Bacon_PP_TypeCoherence.thy` does not contain a deep-embedded term-denotation
   induction, and does not show the construction models H, C, CE and CEV at
   every recursively generated type. Both remain open.

## Audit of the tree-automorphism route (now resolved)

`Bacon_PP_TreeAut.thy` proves a propositional/frame result: `pp_tw` preserves
the Boolean/modal fragment and can carry an invariant unary operator to a
non-invariant one under conjugation. On its own that did not license any
statement about higher-type definability; the missing obligations were a
recursively coherent action on every Bacon type preserving the local function
domains, application, higher-type equality, and all quantifier domains and
logical constants.

`Bacon_PP_TreeAut_Functions.thy` proved the first two at `t -> t`.
`Bacon_PP_TypeCoherence.thy` now proves all four at every type, and checks that
its class notions coincide with Bacon's own at `t -> t`
(`pp_carrier_fun_base_iff`, `pp_eqv_fun_base_iff_fun_view`,
`pp_fixed_fun_base_iff`), so no substitution has been smuggled in.

The conclusion licensed is `pp_purity_not_conjugation_fixed`, and nothing
stronger. See item 6 above.

## Status of the recommended first attack: done, with a limitative verdict

Steps 1--3 below are now complete and machine-checked in
`pp/Bacon_PP_TypeCoherence.thy`; step 4 has been carried out and its answer is
negative for the base-definability condition.

1. Higher-type equality is preserved --- `pb_id_conjugate`, `pb_id_fixed`. Done.
2. The conjugation is generalized recursively to every Bacon type and bijects
   each quantified domain --- the `pp_dom` class, `pb_all_fixed`,
   `pb_ex_fixed`. Done.
3. Application, equality and quantifier coherence hold at every type;
   `pp_fixed_app`, `pb_S_fixed`, `pb_K_fixed` give the term induction via
   combinatory completeness. Done.
4. What follows is `pp_purity_not_conjugation_fixed`: invariance is not
   definable as a predicate over the whole domain at `t -> t`. What does **not**
   follow is any failure of base definability. The cancellation this document
   warned about is real and is now itself a theorem,
   `pp_stock_locus_conjugation_stable`: every stock locus is automatically
   stable under any signature-fixing automorphism, so no argument of this shape
   can refute base definability.

The `Fun` side condition is discharged: the fundamental witness can always be
chosen tree-symmetric
(`pp_countable_stock_has_symmetric_generic_QLN_witness`), so the whole Pure-free
signature, not just its logical fragment, can be taken conjugation-fixed.

A separate result relocates the difficulty: PP is *true* in the full
word-action M-set (`pp_purity_of_pure_holds_in_word_action`), and what fails
there is Recombination (`pp_full_stock_has_no_recombination_witness`).

## Recommended next attack

Symmetry arguments are exhausted, so pursue the model route: construct a
countable, orbit-generic, self-classifying Henkin stock. The generic-witness
theorem already gives QLN for *any* countable stock, so the entire difficulty
is self-classification, and the residual gap is a dependency rather than a
cardinality obstruction:

```text
have:  for every Stock, there is an r with QLN(Stock, r)
want:  there is an r with QLN(Stock(r), r)
```

since the stock of Pure-free denotations depends on `r` through `Fun`. Build
the stock and the witness simultaneously, with reserved classifiers, rather
than by repeatedly adjoining the classifier of the current approximation. The
paired-cone construction is the natural raw material, since it leaves
continuum-many cone pairs free after any countable list of requirements.

There is no Cantor-style no-go: the self-classification condition is that the
domain at `sigma -> Prop` contain the classifier of the pure elements of
`sigma`, which is not a set membering itself, and simple typing blocks the
Russell self-application.

## Working protocol

- Keep changes inside this repository.
- Use `apply_patch`-style focused edits; do not overwrite unrelated work.
- Add every active theory to `ROOT`.
- After each substantive lemma, run the PP session; before a checkpoint, run
  the full build.
- Do not add `sorry`, `oops`, `admit`, or `quick_and_dirty`.
- Keep `STATUS.md` synchronized with proved results and explicit gaps.
- Commit coherent checkpoints to `main` and push them to `origin`.

The task is to advance the proof, not merely produce another speculative
report.
