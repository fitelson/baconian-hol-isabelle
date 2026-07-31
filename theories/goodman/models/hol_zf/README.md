# HOL-ZF model developments

This development has three deliberately separate directories and two
deliberately separate Isabelle sessions.

- [`canonical/`](canonical/README.md) is the official formalization of Bacon's
  appendix construction.  It uses his recursively restricted function-space
  carriers and division action, and contains Bacon's arbitrary-signature
  Theorem 10.1 throughout the `t`-fragment,
  H/Classicist/CE/CEV soundness including the individual Existence instance
  and vector Equivalence, the enumeration/gluing construction, and
  proposition-generated completeness theorem.
- [`extensions/`](extensions/README.md) interprets Goodman's `Pure`, `Fun`,
  logical-stock, Recombination, Exhaustion, and QLN vocabulary over those exact
  carriers.  These theories extend the canonical model; they do not replace
  its carriers or action.
- [`secondary/`](secondary/README.md) contains older comparison models,
  finite-fragment experiments, and the abandoned closure-code/PER program.
  It is built only by `Higher_Order_Metaphysics_PP_ZF_Secondary`; nothing in
  the canonical Bacon chain imports this directory.

`Higher_Order_Metaphysics_PP_ZF_Model` contains exactly `canonical/` and
`extensions/`.  `Higher_Order_Metaphysics_PP_ZF_Secondary` is its child and
contains `secondary/`.

The session uses Isabelle's HOL-ZF universe.  Accordingly, its set-theoretic
results are relative to the additional assumptions of HOL-ZF.
