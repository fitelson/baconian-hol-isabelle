# Deep and shallow embeddings in this repository

The repository contains two independent Isabelle developments with different
embedding architectures. The Bacon--Dorr development is a deep embedding of
the object language and its proof systems. Daniel Kirchner's formalization of
Zalta's Abstract Object Theory (AOT) is a shallow semantic embedding equipped
with custom syntax and a carefully restricted proof interface.

Here, *deep* and *shallow* are technical descriptions of how the object theory
is represented in Isabelle. They do not rank the theories by rigor,
mathematical difficulty, philosophical depth, or faithfulness to their
sources.

## The Bacon--Dorr development

The Bacon development represents object-language expressions as data. The
datatype `oterm` in
[`Bacon_Syntax.thy`](../theories/base/Bacon_Syntax.thy) has separate
constructors for variables, constants, application, lambda abstraction,
identity, propositional connectives, and quantifiers. Bound variables use de
Bruijn indices. Thus Bacon's universal quantifier is the constructor `Forall`,
not Isabelle/HOL's own universal quantifier; Bacon's lambda abstraction is the
constructor `Lam`, not an Isabelle/HOL lambda.

Because the syntax is reified, the formalization must define and verify its
metatheory explicitly:

- [`Bacon_Typing.thy`](../theories/base/Bacon_Typing.thy) defines the
  inductive typing judgment and proves the type-inference results;
- [`Bacon_Substitution.thy`](../theories/base/Bacon_Substitution.thy) defines
  renaming, shifting, and capture-avoiding substitution;
- [`Bacon_Beta.thy`](../theories/base/Bacon_Beta.thy) defines beta
  contraction; and
- [`Bacon_Deduction.thy`](../theories/base/Bacon_Deduction.thy) defines the
  Hilbert-style derivability relation for (H) as an inductive predicate.

Classicism, CE, and CEV add further explicitly represented derivability
relations. Semantics is introduced only after syntax and deduction have been
defined. In [`Bacon_Semantics.thy`](../theories/classicism/Bacon_Semantics.thy),
an evaluation maps object-language terms to denotations, and soundness is
proved by induction over the independently defined derivations. The canonical
and Henkin developments then prove the corresponding completeness results.

The architecture therefore separates three levels:

```text
object-language syntax  ->  object-language derivation  ->  semantic interpretation
```

This separation permits reasoning about substitution, typing, conversion,
derivations, admissibility, proof search, soundness, and completeness as
distinct mathematical subjects.

## Kirchner's AOT development

Kirchner's AOT formalization uses a shallow semantic embedding. AOT
propositions are represented by a primitive HOL type, and
[`AOT_model.thy`](../theories/zalta/AOT_model.thy) supplies their semantic
interpretation at possible worlds. AOT connectives and binders have HOL types
such as:

```isabelle
AOT_imp    :: [o, o] => o
AOT_forall :: ('a => o) => o
AOT_lambda :: ('a => o) => <'a>
```

In particular, the argument of `AOT_forall` is a HOL function. HOL therefore
provides much of the binding and type discipline that the Bacon development
represents explicitly. There is no general AOT formula datatype corresponding
to `oterm`, and no separately reified inductive calculus corresponding to
`H_proves`.

The PLM axioms in
[`AOT_Axioms.thy`](../theories/zalta/AOT_Axioms.thy) are established as
validities in the semantic embedding. The custom `AOT_axiom`, `AOT_theorem`,
and proof commands in
[`AOT_commands.ML`](../theories/zalta/AOT_commands.ML) provide a PLM-like
proof environment over this semantic foundation.

This is nevertheless not a naive shallow embedding. Kirchner also developed:

- PLM-like inner syntax and printing;
- custom theorem, axiom, definition, and proof commands;
- modally strict and modally weak proof contexts;
- a registry of AOT theorems; and
- an abstraction layer that restricts automated proof search to AOT-approved
  results.

The abstraction layer is important. It prevents ordinary work in the AOT
environment from depending indiscriminately on implementation-level facts
about the semantic model. It thereby preserves AOT's intended inferential
practice while retaining the conveniences of a shallow embedding.

## Comparison

| Feature | Bacon--Dorr | Kirchner's AOT |
|---|---|---|
| Formulas | Reified syntax trees | HOL terms with AOT meanings |
| Binding | Explicit de Bruijn indices | HOL functions and lambda abstraction |
| Typing | Explicit inductive judgment | Principally HOL types and type classes |
| Substitution | Defined over object syntax | Substantially inherited from HOL |
| Deduction | Explicit inductive calculi | Custom proof interface over semantic validity |
| Semantics | Defined separately from syntax | Constitutive of the embedding |
| Characteristic metatheory | Soundness and completeness relating calculus and models | Semantic verification of AOT axioms and theorems |

The Bacon embedding consequently gives more direct access to proof-theoretic
questions about the represented calculi. The AOT embedding gives a more
transparent environment for proving substantive theorems of AOT, because HOL
handles much of the binding, typing, and higher-order infrastructure.

## What does not follow

The architectural difference does not imply that the Bacon development is
more rigorous. Both developments produce Isabelle kernel-checked theorems
relative to their stated definitions and axioms. Nor does it imply that the
AOT development is technically simple: its semantic model, free logic,
hyperintensional propositions, encoding predication, relation types, custom
syntax, and abstraction layer are substantial formal achievements.

The Bacon appendix model and the AOT semantic model should also not be
confused with embedding depth. A model may be mathematically intricate
without the surrounding object language being deeply embedded. The Bacon
development is deep because syntax and derivability are independently
represented before they are interpreted. The AOT development is shallow
because object-language expressions are represented directly by objects in
the semantic metalanguage, even though the resulting semantic and proof
infrastructure is elaborate.

For Kirchner's account of the method and its motivation, see the source entry
for “Computer-Verified Foundations of Metaphysics” in
[`sources/README.md`](../sources/README.md).
