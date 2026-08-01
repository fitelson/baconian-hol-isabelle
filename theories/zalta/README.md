# Abstract Object Theory in Isabelle/HOL

## Place in this repository

This directory is an independent theory family within *Higher-Order
Metaphysics in Isabelle*. It does not extend, import, or provide foundations
for the Bacon--Dorr--Goodman developments elsewhere in the repository. Its
single maintained Isabelle session is `AOT`, based directly on
`HOL-Cardinals`.

Daniel Kirchner developed this Isabelle/HOL formalization and its custom AOT
theorem-proving environment. It formalizes Edward N. Zalta's theory and PLM
developments to which Kirchner and Uri Nodelman made critical theoretical
contributions. Kirchner's article, “Computer-Verified Foundations of
Metaphysics,” describes the shallow semantic embedding, its abstraction layer,
and the verification of the AOT reconstruction of Frege's theorem. The exact
article and PLM draft used for this repository are in the
[central source archive](../../sources/README.md).

The source is based on the `develop` branch of
[`ekpyron/AOT`](https://github.com/ekpyron/AOT), commit
`9a165b4d2e1dd9da7276248ebdcaf671dcdf2bdd`. Local changes include an explicit
semantic proof of `RA[3]`, further natural-number and hype-state results, and
inclusion of truthmaker semantics in the checked session. The source records
the proposed infinitude result `inf-card-exist:2` as unproved and does not
register it as a theorem.

An older extended relation-comprehension experiment depended on facts absent
from the synchronized upstream theory. It is preserved locally under the
repository's ignored `tmp/zalta-local-experiments/` directory and is not part
of the maintained `AOT` session.

Build the session serially from the repository root:

```sh
isabelle build -j 1 -D theories/zalta AOT
```

Build and query its independent knowledge graph with:

```sh
tools/isabelle_kg/build_zalta_graph.sh
tools/isabelle_kg/query_graph.py --family zalta stats
```

The maintained session builds with Isabelle2025-2. Every registered theorem
is kernel-checked, relative to the explicitly declared AOT and semantic
axioms. The repository's BSD-2-Clause license does not relicense this imported
material; retain `COPYRIGHT_Isabelle` and the upstream attribution.

The source PDFs used alongside this formalization are stored in the central
source archive, not in the Isabelle theory directory.

## Upstream description

This directory contains an embedding of [_Abstract Object Theory_](http://mally.stanford.edu/theory.html)
in [Isabelle/HOL](https://isabelle.in.tum.de).

It implements major parts of the most recent presentation of object theory given in [Edward Zalta](https://mally.stanford.edu/zalta.html)'s
[Principia Logico-Metaphysica](https://mally.stanford.edu/principia.pdf) in context of the
[Computational Metaphysics project](https://mally.stanford.edu/cm/) of the
[Metaphysics Research Lab](https://mally.stanford.edu/) at Stanford University.

A [more readable HTML presentation of the theory files](https://aot.ekpyron.org/) is
automatically generated form this repository.

An [older and now outdated version of the embedding](https://www.isa-afp.org/entries/PLM.html)
was published in the [Archive of Formal Proofs](https://www.isa-afp.org/).
