# Complete verification matrix for Goodman's PP notes

Source: Jeremy Goodman, *Is Purity of Pure consistent with Bacon's Logical
Combinatorialism?*, state-of-project notes dated July 2026.

This matrix distinguishes four statuses:

- **Verified**: the stated result, with the displayed qualification, has an
  Isabelle proof.
- **Verified after repair**: the prose claim is not correct as stated, but an
  exact corrected theorem has been proved.
- **Conditional theorem; model instantiation open**: the mathematical
  implication is proved from explicit premises, but the notes' intended model
  does not yet discharge those premises.
- **Open or underspecified**: there is no determinate verified theorem.

The dedicated session `Goodman_Complete_Audit_2026_07_27` audits these 96
principal theorem objects together with fifteen later \(K\)-, conjunction-,
binary-truth-function-fragment, and bridge results.  A fresh build passes.
Every
audited proof is checked
without admitted proof steps or undischarged logical assumptions beyond the
premises stated in its theorem.  The general T9 cardinal theorems retain only
their stated restriction on the types to which they apply.

## Object-language results

| Item | Status | Exact conclusion |
|---|---|---|
| T1 | **Verified** | Under zeroary Exhaustion, every pure proposition is truth or falsity; the biconditional operators are identity or negation; WI collapses to Inv. |
| T2a | **Verified** | `fun-prime` is preserved by every pure reversible operator, hence by negation. |
| T2b | **Verified** | Truth and falsity are not `fun-prime`; a `fun-prime` witness is distinct from truth, falsity, and its negation. |
| T2c | **Verified, strengthened** | Every pure proposition is possibly identical to the witness; PP is not used. |
| T2d | **Verified, strengthened** | Possible purity of the witness is derivable without Persistence. |
| T2e | **Verified** | Noncontingency of a `fun-prime` witness is false but possible. |
| T2f | **Verified conditionally** | All 15 inequalities among the six displayed propositions follow from the explicit `fun-prime` antecedent. |
| T3 | **Verified after repair** | The advertised derivation has a modal gap: it obtains possible identity, not identity. Heredity follows after zeroary Exhaustion or pure-identity rigidity. An explicit modal abstraction satisfies the advertised intermediate principles while T3 fails. |
| T4 | **Verified, strengthened** | The higher-type diagonal result holds over purity schema plus application closure; PP and the `fun-prime` premise are unused. |
| T5 | **Verified conditionally** | The displayed background principles plus `fun-prime(r)` yield a third `fun-prime` proposition. This does not establish consistency of the antecedent. |
| T6-Inv | **Verified** | The contradiction is proved, together with its translation to \(T_0\), Recombination, zeroary Exhaustion, unique proposition-level fundamentality, and PP. |
| T6-WI | **Verified** | The contradiction follows through WI implies TU. In addition, the displayed advertised master claim is derived directly from the T6-WI stock, independently of explosion. |
| T6-TU | **Verified** | The truth-uniformity contradiction, including the flipping conjugation, is proved. |
| T6-RS | **Verified** | The strong-L2 plus rigid-specification contradiction is proved. |
| T7a | **Verified** | The liar family has a false identity member and a true member indexed by some pure reversible operator. |
| T7b | **Underspecified** | The notes give no diagonal term, binder structure, or definitions of “fixed” and “shifted” point. There is no unique theorem to verify. |
| T8a | **Verified** | The five displayed base kinds are pairwise distinct. |
| T8b | **Verified** | L2 gives uniqueness of kind for represented propositions. |
| T8c | **Verified** | The displayed assumptions prove 31 pairwise-distinct pure unary operators and 31 pairwise-distinct propositions. |
| T9 | **Verified at the claimed counting level** | The displayed PC specification itself makes the PC map injective. Representation of each member of a kind by an element of `G` supplies an injective code of each kind-fibre into `G`. These facts give `|Pow K| <= |K times G|`, and classical cardinal arithmetic gives `finite K` or `|Pow K| <= |G|`. Instantiating the abstract types uniformly across Goodman's full typed object language remains separate. |

The Recombination/QSS background also required correction. Unary
Recombination gives the pointwise modal core, but not the necessitation of its
universal closure. Zeroary Exhaustion supplies the missing bridge; with unique
fundamentality it also derives existence of a `fun-prime` proposition.

## Model-theoretic results

| Item | Status | Exact conclusion |
|---|---|---|
| M1, bottom type | **Verified** | The pure propositions are exactly the two invariant propositions, and the operator applying exactly to them is the noncontingency operator; it is denoted by a closed term containing only logical vocabulary. |
| M1, first PP failure | **Verified conditionally and syntactically** | The exact footnote-59 liar is typed, beta-reduced, and proved pure from PP plus Purity of Fun. QSS then yields contradiction. Thus any Bacon model with the other premises must omit that liar from its pure unary stock. |
| M1, fn. 60 corollary | **Exact identification; exclusion conditional** | The infinitary join exists in the full unary function domain and has exactly the pure unary operators as its extension. It is the interpretation of `Pure` at the next type, and PP at that type holds exactly when this operator belongs to the next pure stock. The current Isabelle development does not prove its nonmembership directly in Bacon's exact generic model. It proves nonmembership only from the additional PP-diagonal/QSS assumptions. Thus completeness of the function domain supplies the join, but does not by itself settle its purity. |
| M2 | **Verified** | Goodman's operators \(G_T\) belong to the invariant function domain, and \(T \mapsto G_T\) is a bijection onto the invariant operators. Cantor yields the cardinal obstruction and failure of QSS under the invariance reading. |
| M3 | **Verified with stock qualification** | Relative to the chosen stock of pure operators, `fun-prime` is equivalent to freeness against nonzero pure laws; it implies extreme views, the countable Boolean stock has a free generator, and the `fun-prime` class is product-meager. |
| M4, explicit witness | **Verified conditionally; model instantiation open** | Preimage heredity and the lifted-branch witness follow from necessitated QSS at `r`, membership of every pure operator in Bacon's function domain, invariance, and the presence of identity, zero, and one. The result has not yet been instantiated for Bacon's stock of operators denoted by closed terms containing only logical vocabulary. |
| M4, wide-Fun alternatives | **Underspecified** | The multiple-fundamental conjunction/Separated-Structure discussion does not state either the selection condition on `Fun` or a precise Separated Structure formula. There is no unique theorem to encode. The single-fundamental undershoot is covered by the explicit witness. |
| M5, exotic operator | **Verified** | The displayed fixed pair gives an invariant involution violating TU, WI, and Inv. |
| M5, original orbit choice | **Refuted and repaired** | The notes' reason is false: worlds, their views, and the displayed world-indexed pairs are all countable, so countability alone does not select a pair outside the orbit. Isabelle now constructs, for every candidate `R`, a diagonal two-element pair outside every view of `R`; every proper view of either member is empty or universal. Its transposition is invariant, fixes `R`, and is nonidentity. |
| M5, pre-rebuild QSS obstruction | **Verified conditionally** | If the repaired diagonal exotic and identity are both placed in the pure stock, then `R` is not `fun-prime` for that stock. This verifies the corrected form of the notes' claim that merely adjoining the exotic operator to the old model destroys QSS. |
| M5, rebuild | **Conditional theorem; model instantiation open** | Bacon's Theorem 10.1 is proved in a set-theoretic formalization of his appendix model, together with a rebuilding theorem for a specified operator. The new diagonal exotic operator has not yet been included in a fully rebuilt model whose enlarged stock of definable operators is verified. |
| M5, collision method | **Verified for the displayed witness** | From the core theory and `fun-prime(r)`, the closed operator `λp.(p ↔ NC(p))` takes the same value at `NC(r)` and truth, although `NC(r) ≠ truth`. This proves the advertised concrete failure of injectivity. A uniform extension to merely existentially given invertibles is a further proposal, not a consequence of this calculation. |
| M6 | **Verified conditionally; model instantiation open** | Under necessitated QSS, membership of every pure operator in Bacon's function domain, and invariance, distinct substitutions are separated by a `fun-prime` proposition. With identity, zero, and one also pure, a strict-inclusion `fun-prime` pair blocks the indicated joint assignment. Single-coordinate arbitrary realization fails independently by countability. These results have not all been instantiated for Bacon's stock of operators denoted by closed terms containing only logical vocabulary. |
| M7, definable reachability | **Verified** | The Tarski diagonal lies outside every value enumerated by the closed terms under consideration, so Fundamental Completeness fails for those denotations. |
| M7, invariant reachability | **Verified equivalence; instance open** | Every proposition is reachable from `r` by an invariant operator iff the orbit map `i |-> view i r` is injective. Whether Bacon's chosen glued `r` has that property remains construction-sensitive. |
| Bacon Theorem 10.1 | **Verified, qualified** | The rebuilt-family theorem is proved. At type `Ind`, its identity quotient forces the family to be constant; it cannot deliver a family of distinct individual denotations. |

## Claims that cannot presently be “verified”

The following are not missing proof scripts for settled claims:

1. Goodman's main consistency question remains open.  In the direct
   substitution model, where `E` is typed at `Ind -> (Prop -> Prop)` and
   commutes with taking views, the positive program is reduced to the
   self-enumeration equation saying that the unary operators denoted by
   closed expressions built using `E` are exactly `{E n | n in Nat}`.
2. Global semantic L2 for Bacon's complete definable stock remains open.  L2
   is verified only for identity, necessity, possibility, constant truth, and
   constant falsity, together with a precise
   counterexample criterion for extensions.
3. T7b is not stated precisely enough to encode uniquely.
4. The full M5 rebuilt model with the exotic operator included in its pure stock is not yet
   constructed.
5. The multiple-fundamental “wide Fun” discussion in M4 does not specify
   either the selection condition on `Fun` or a precise Separated Structure
   formula.  It therefore has no unique theorem statement to verify.

Thus “everything” does not receive a blanket PASS.  Every determinate claim in
the notes has now been proved, refuted and repaired, or assigned the explicit
qualification on which it is true.  The source itself still contains one
modal gap, one false countability argument, underspecified proposals, and
genuine open problems; those are not mislabeled as verified theorems.
