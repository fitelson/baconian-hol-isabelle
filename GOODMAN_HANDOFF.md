# Goodman PP Consistency: Handoff to Claude

## Objective

Settle Jeremy Goodman's question:

> Is PP consistent with the Bacon--Dorr background theory plus the existence
> of a fundamental proposition, when Purity of Fun is not assumed?

Work only with the Bacon--Dorr background, Classicism, theorem-level CE/CEV,
and the PP/QLN package. `ContextVectorEquivalence` is not part of this
problem.

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

- The constant-builder HOL-ZF model makes the closed constant builder
  \(K=\lambda p.\lambda q.p\) pure, together with the four preceding unary
  logical operators: identity, negation, constant truth, and constant
  falsity.  Applying \(K\) to a pure true or false proposition yields the
  corresponding constant unary operator.  The theory proves global PP,
  zeroary and unary Recombination and Exhaustion, unique proposition-level
  fundamentality, no fundamentality at other types, application closure, and
  Modalized Functionality.  The exact consistency theorem is:

  ```isabelle
  pp_constant_builder_fragment_PP_axioms_consistent:
    CEV_axiom_consistent []
      pp_constant_builder_fragment_PP_axioms
  ```

- The bridge to the fresh formulation proves:

  ```isabelle
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

  There is no finiteness restriction.  The model verifies the zeroary and
  unary QLN clauses present in this formal background; it does not establish
  a binary QLN clause.  This is not a consistency theorem for the full
  logical-purity schema.

- The conjunction model extends this result by making curried conjunction
  \(\mathsf{And}=\lambda p.\lambda q.(p\wedge q)\) pure.  Application closure
  forces no new unary class:
  \(\mathsf{And}\,\top\) is equivalent to identity and
  \(\mathsf{And}\,\bot\) is equivalent to constant falsity.  Isabelle proves:

  ```isabelle
  pp_conjunction_fragment_PP_axioms_consistent:
    CEV_axiom_consistent []
      pp_conjunction_fragment_PP_axioms

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

  Again there is no finiteness restriction, and only the zeroary and unary
  QLN clauses are claimed.

- The uniform binary truth-function model subsumes the Boolean part of the
  preceding construction.  For every
  \(F:\mathbf 2\times\mathbf 2\to\mathbf 2\), it makes the closed curried
  operator \(\lambda p.\lambda q.F(p,q)\) pure.  Every partial application to
  a pure proposition is equivalent to constant truth, identity, negation, or
  constant falsity, so no new proposition or unary pure class is forced.
  Isabelle proves:

  ```isabelle
  pp_binary_truth_fragment_PP_axioms_consistent:
    CEV_axiom_consistent []
      pp_binary_truth_fragment_PP_axioms

  fresh_goodman_binary_truth_only_consistent:
    U \<subseteq> fresh_goodman_axioms \<Longrightarrow>
    U \<inter> pp_purity_schema
      \<subseteq> pp_binary_truth_allowed_purity \<Longrightarrow>
    CEV_axiom_consistent [] U
  ```

  The allowed purity stock consists of the six previously displayed
  instances together with all sixteen members of
  `pp_truth_function_purity_axioms`.  There is no finiteness restriction.
  This remains a zeroary/unary QLN fragment theorem, not a theorem for the
  full logical-purity schema.

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

Continue the controlled logical-purity extensions in increasing type and
term complexity:

1. add the closed necessity operator \(\lambda p.\Box p\);
2. add the closed possibility operator \(\lambda p.\Diamond p\) separately;
3. if both extensions survive, absorb the six already evaluated
   higher-order quantified unary operators, whose denotations collapse to
   necessity, possibility, their negated variants, truth, or falsity;
4. continue upward through the remaining higher-order closed logical terms.

At each stage retain the same obligations: PP, both directions of the
zeroary and unary QLN clauses, application closure, unique
proposition-level fundamentality, no fundamentality at other types, and
Modalized Functionality.  If a modal extension fails, distinguish failure of
the present moving-seed interpretation from a model-independent derivation of
contradiction.  Only the latter answers Goodman's question negatively.

Even success at both stages would not answer the full question.  The
remaining obstacle is logical purity for every higher-order closed logical
term, including quantified operators, together with the self-referential
condition imposed by Purity of Pure.

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
