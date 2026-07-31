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

The dedicated session `Goodman_Complete_Audit_2026_07_27` audits 158 theorem
objects supporting the claims and qualifications in this matrix.  The separate session
`Goodman_Modal_Quantified_Audit_2026_07_28` audits 30 necessity, possibility,
higher-order quantified, and corresponding bridge results.  Fresh builds
pass.  Every
audited proof is checked
without admitted proof steps or undischarged logical assumptions beyond the
premises stated in its theorem.  The general T9 cardinal theorems retain only
their stated restriction on the types to which they apply.

Goodman's formal question is the consistency of the CEV+ axiom extension by
the Recombination-only stock together with PP. Isabelle proves that this is
equivalent to consistency of every finite subset of the added axioms; a
negative answer is equivalent to a finite subset from which CEV+ derives
falsity. A model would be a sufficient consistency certificate, but model
existence is not the definition of this proof-theoretic question.

The appendix-model, rebuilt-M5, exact-M1, and exact-L2 results use a HOL-ZF
interpretation whose carrier satisfies axiomatized ZFC. They are relative
semantic theorems in that setting, not pure-HOL consistency certificates for
ZFC.

## Exact appendix-model metatheory

| Task | Verified result |
|---|---|
| Exact Theorem 10.1 | Isabelle proves Bacon's arbitrary-signature theorem throughout the `t`-fragment, comprising all types built from `t` alone, and supplies the branch-gluing proof Bacon omits. Signatures involving `e`-containing types remain outside scope, as Bacon explicitly defers that extension. |
| Exact soundness | Proved for H, Classicism, CE, and CEV over Bacon's recursively defined carriers, including the individual Existence instance and vector Equivalence for an arbitrary finite vector of argument types. |
| Enumeration and gluing | The countable enumeration of consistent sentences and the glued constant assignment are proved over the exact carriers. |
| Semantic representation | One glued model represents consistency and the complete frame theory for a fixed proposition-generated signature. This is semantic frame-theory representation, not proof-theoretic completeness of H. |

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
| M1, first PP failure | **Verified for arbitrary compositional CEV+ Henkin models, with a material qualification** | The exact footnote-59 liar is typed, beta-reduced, and proved pure from PP plus Purity of Fun. Its denotation, QSS, unique fundamentality, and the identity-respecting diagonal contradiction are now abstracted from Bacon's tree semantics to the denotable-function-space Henkin interface. Hence no such model validates full QLN + PP + Purity of Fun. This does not settle Goodman's question, since the central axiom sets deliberately omit Purity of Fun. |
| M1, fn. 60 corollary | **Exact identification; exclusion conditional** | The infinitary join exists in the full unary function domain and has exactly the pure unary operators as its extension. It is the interpretation of `Pure` at the next type, and PP at that type holds exactly when this operator belongs to the next pure stock. The current Isabelle development does not prove its nonmembership directly in Bacon's appendix construction. It proves nonmembership only from the additional PP-diagonal/QSS assumptions. Thus completeness of the function domain supplies the join, but does not by itself settle its purity. |
| M2 | **Verified** | Goodman's operators \(G_T\) belong to the invariant function domain, and \(T \mapsto G_T\) is a bijection onto the invariant operators. Cantor yields the cardinal obstruction and failure of QSS under the invariance reading. |
| M3 | **Verified with stock qualification** | Relative to the chosen stock of pure operators, `fun-prime` is equivalent to freeness against nonzero pure laws; it implies extreme views, the countable Boolean stock has a free generator, and the `fun-prime` class is product-meager. |
| M4, explicit witness | **Verified conditionally; model instantiation open** | Preimage heredity and the lifted-branch witness follow from necessitated QSS at `r`, membership of every pure operator in Bacon's function domain, invariance, and the presence of identity, zero, and one. The result has not yet been instantiated for Bacon's stock of operators denoted by closed terms containing only logical vocabulary. |
| M4, wide-Fun alternatives | **Underspecified** | The multiple-fundamental conjunction/Separated-Structure discussion does not state either the selection condition on `Fun` or a precise Separated Structure formula. There is no unique theorem to encode. The single-fundamental undershoot is covered by the explicit witness. |
| M5, exotic operator | **Verified** | The displayed fixed pair gives an invariant involution violating TU, WI, and Inv. |
| M5, original orbit choice | **Refuted and repaired** | The notes' reason is false: worlds, their views, and the displayed world-indexed pairs are all countable, so countability alone does not select a pair outside the orbit. Isabelle now constructs, for every candidate `R`, a diagonal two-element pair outside every view of `R`; every proper view of either member is empty or universal. Its transposition is invariant, fixes `R`, and is nonidentity. |
| M5, pre-rebuild QSS obstruction | **Verified conditionally** | If the repaired diagonal exotic and identity are both placed in the pure stock, then `R` is not `fun-prime` for that stock. This verifies the corrected form of the notes' claim that merely adjoining the exotic operator to the old model destroys QSS. |
| M5, rebuild | **Verified** | Isabelle constructs the least application-closed pure stock containing every closed logical denotation and Goodman's displayed exotic operator. The stock is countable; the exotic denotation is typed, commutes with taking views, is self-inverse, violates TU, and is not a biconditional operator. A rebuilt fundamental proposition supplies Recombination and `fun-prime` separation at every world, and the resulting interpretation validates Bacon's Recombination background. This is not a PP model: PP would further require the classifier of the enlarged pure stock itself to belong to the next pure stock. |
| M5, collision method | **Verified for the displayed witness; unrestricted existential generalization refuted** | From the core theory and `fun-prime(r)`, the closed operator `λp.(p ↔ NC(p))` takes the same value at `NC(r)` and truth, although `NC(r) ≠ truth`. Isabelle now also proves inside CEV+ that an operator with an existentially supplied two-sided inverse is injective, and therefore proves that this displayed collision operator is not reversible. In the rebuilt M5 model, the displayed exotic operator is a non-truth-uniform bijection and hence has no collision. Thus reversibility, even together with failure of truth-uniformity, cannot support a uniform collision argument. A PP-specific argument would need a further condition constraining the existential witness's action. |
| M6 | **Verified conditionally; model instantiation open** | Under necessitated QSS, membership of every pure operator in Bacon's function domain, and invariance, distinct substitutions are separated by a `fun-prime` proposition. With identity, zero, and one also pure, a strict-inclusion `fun-prime` pair blocks the indicated joint assignment. Single-coordinate arbitrary realization fails independently by countability. These results have not all been instantiated for Bacon's stock of operators denoted by closed terms containing only logical vocabulary. |
| M7, definable reachability | **Verified** | The Tarski diagonal lies outside every value enumerated by the closed terms under consideration, so Fundamental Completeness fails for those denotations. |
| M7, invariant reachability | **Verified equivalence; instance open** | Every proposition is reachable from `r` by an invariant operator iff the orbit map `i |-> view i r` is injective. Whether Bacon's chosen glued `r` has that property remains construction-sensitive. |
| Bacon Theorem 10.1 | **Verified for arbitrary signatures in the `t`-fragment** | Isabelle proves the theorem throughout the fragment of types built from `t` alone and supplies the branch-gluing proof Bacon omits. Signatures involving `e`-containing types remain outside scope, as Bacon explicitly defers that extension. The verified scope includes Goodman's language with its single propositional constant. |
| Bacon's omitted QLN verification | **Verified for Goodman's specialization** | In the completed tree interpretation with one fundamental proposition, `Pure` interpreted by the complete closed-logical stock, and `Fun` interpreted by the generic proposition, Isabelle proves global zeroary and unary QLN. Zeroary Exhaustion follows from the root truth/falsity classification of closed logical propositions; unary Exhaustion follows from cone invariance; unary Recombination is supplied by the generic proposition. These are all nonvacuous instances in Goodman's unique-fundamental-proposition setting. Bacon's broader future-work extension to arbitrary individual types or several pairwise-distinct fundamental entities is not claimed. |
| QLN granularity condition | **Exact proof-theoretic reduction verified; no derivation from PP** | Closed logical builders for the truth-functional agreement and disagreement operators are encoded in the complete object language. The logical-purity schema and application closure make their values at a pure unary operator pure; PP is not the source of these purity premises. Isabelle reconstructs the generic unary Exhaustion instance, combines it with Recombination, and proves that over the full QLN+PP stock the modal agreement disjunction is equivalent to the pointwise agreement-or-disagreement disjunction. A separate verified truth-condition theorem identifies that disjunction with truth uniformity. Thus the proposed condition is exactly TU in this setting, not a weaker intermediate principle. No PP-only derivation, underivability theorem, or PP countermodel is claimed. |
| L2 in Bacon's exact appendix model | **Refuted for the complete closed-logical stock** | On Bacon's finite-natural-word action, the closed logical operator \(\widehat Z(P)=\{w:(\exists n\,P(w^\frown\langle n\rangle))\mathbin{\&}(\exists n\,\neg P(w^\frown\langle n\rangle))\}\) records variation among all immediate successors. Isabelle verifies its exact right-division denotation, membership in the stock of unary operators denoted by closed logical terms, surjectivity, complement-invariance and hence noninjectivity, right-cancellativity within that stock, and nonreversibility. A generic-separation theorem supplies a `fun-prime` proposition relative to this stock, which \(Z\) carries to another such proposition. Identity and \(Z\) therefore refute both L2 and strong L2 for the complete closed-logical stock. This corrects the earlier two-child calculation. No theorem for arbitrary enlarged pure stocks, and no PP interpretation, is claimed. |

## Claims that cannot presently be “verified”

The following are not missing proof scripts for settled claims:

1. Goodman's main consistency question remains open.
2. T7b is not stated precisely enough to encode uniquely.
3. The multiple-fundamental “wide Fun” discussion in M4 does not specify
   either the selection condition on `Fun` or a precise Separated Structure
   formula.  It therefore has no unique theorem statement to verify.
Thus “everything” does not receive a blanket PASS.  Every determinate claim in
the notes has now been proved, refuted and repaired, or assigned the explicit
qualification on which it is true.  The source itself still contains one
modal gap, one false countability argument, underspecified proposals, and
genuine open problems; those are not mislabeled as verified theorems.
