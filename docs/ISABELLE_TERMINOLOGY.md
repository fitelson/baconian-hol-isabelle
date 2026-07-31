# Bacon--Dorr--Goodman terminology in the Isabelle repository

Reader-facing documentation, Isabelle section headings, `text` blocks, and
comments should state the mathematics in the terminology of Bacon, Dorr, and
Goodman.  Theory names, constants, locales, and theorem identifiers remain
stable so that dependencies and citations do not break.

## Canonical vocabulary

Prefer:

- Bacon's system \(H\), Classicism, the Rule of Equivalence, vector
  Equivalence, and Modalized Functionality;
- purity, fundamentality, Purity of Pure (PP), and Purity of Fun;
- Quantified Logical Necessity (QLN), Recombination, and Exhaustion;
- Quantified Separated Structure (QSS);
- a fundamental proposition, exactly one fundamental proposition, and no
  fundamental entities at other types;
- \(\mathrm{fun}'\), pure operator, reversible or invertible operator, and
  Goodman's \(G_T\);
- \(X\approx Y\), kind, L2, strong L2, Inv, WI, TU, RS, and PC;
- Bacon's substitution model or appendix model, substitution action, view from
  a substitution, invariant operator, and function domain;
- “denotations of closed terms containing only logical vocabulary” when
  describing Bacon's interpretation of `Pure`;
- liar, diagonal, collision, gluing, rebuilding, free generator, and
  Fundamental Completeness.

“Stock,” “generic,” “absorption,” and “fixed point” are permitted when they
carry their source meaning.  Do not use them as universal labels for unrelated
implementation constructions.

## Translation from implementation labels

| Bacon--Dorr--Goodman expression | Stable Isabelle identifier or former implementation label |
|---|---|
| Purity of Pure | `pp_target_PP` |
| Recombination | `pp_unary_recombination` |
| Exhaustion | `pp_unary_exhaustion` |
| operators denoted by closed expressions using \(E\) | `pp_t_enumerator_basis E U`, “generated unary stock” |
| \(\mathcal C_E=\{E(n):n\in\mathbb N\}\) | `pp_t_term_basis_fixed_point`, “absorption fixed point” |
| respects Bacon's substitution action | `E_cone_natural`, “cone-natural” |
| world-relative identity | `pp_e_eqv`, “local identity” |
| property of being a value of \(E\) | “range classifier” |
| candidate fundamental proposition \(r\) | “seed” or “generic seed” |
| operator applying exactly to the members of a class | “classifier” |
| an interpretation of `Pure` whose denotation lies in its own extension | “self-classifying stock” |
| state the listed premises explicitly | “central stock,” “repaired central stock,” or “semantic-stock interface” |
| all representations of \(H(q)\) are \(R\)-related | “tag homogeneity” |
| conditional theorem whose model assumptions remain open | “abstract interface” |

Implementation terminology may appear parenthetically in developer
documentation, for example: “world-relative identity (implemented by
`pp_e_eqv`).”  It should not replace the mathematical description.

## Documentation layers

1. `README.md`, Goodman-facing reports, and verification matrices use only the
   source vocabulary or define a technical expression immediately.
2. Isabelle exposition leads with the mathematical claim.  An implementation
   name may follow in parentheses when it helps readers find the formal object.
3. `STATUS.md` gives only the current mathematical status. Historical debate
   transcripts may retain implementation terminology, but they must not be
   treated as current reader-facing documentation.

Before delivering a report, also verify that every LaTeX not-equal sign is
written as `\neq`, never `\ne`.
