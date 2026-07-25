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

## Important audit of the tree-automorphism route

`Bacon_PP_TreeAut.thy` proves a propositional/frame result: `pp_tw` preserves
the Boolean/modal fragment and can carry an invariant unary operator to a
non-invariant one under conjugation.

Do **not** cite this alone as proving that invariance is not Pure-free
definable at higher type. That conclusion requires a recursively coherent
action on every Bacon type preserving:

- the local function domains;
- application;
- higher-type equality;
- all quantifier domains and logical constants.

`Bacon_PP_TreeAut_Functions.thy` now proves the first two obligations at
`t -> t`: tree conjugation bijects Bacon's local unary function domain and
preserves application. Equality and the recursive all-type diagram remain
open.

The earlier Claude correction report overstates this point. The source and
project status files contain the corrected, conservative claim.

## Recommended first attack

Complete or refute the tree-conjugation coherence diagram.

1. Use the proved cone characterization and domain bijection to formalize and
   prove preservation of the object-language equality proposition at type
   `t -> t`.
2. Generalize the conjugation recursively to Bacon's exponential types and
   prove that it bijects each quantified domain.
3. Prove application, equality, and quantifier coherence simultaneously by
   induction on object-language types and terms.
4. Only after those steps decide what non-definability follows. Invariance
   itself may be undefinable while the stock locus `S_Y` remains definable by
   cancellation, as the parity and cyclic examples warn.

In parallel, keep the alternative model route in view: construct a countable
or otherwise orbit-generic self-classifying Henkin stock. A large
self-classifying fixed point exists, but QLN for it is open; the countable
Pure-free stock has QLN, but self-classification is open.

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
