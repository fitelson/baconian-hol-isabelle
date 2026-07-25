# Handoff: Goodman's PP consistency problem

Written 2026-07-25 at the end of a Claude session, for whoever drives next
(immediately: Codex). `STATUS.md` is the long-form record; this is the
orientation document. Read this, then `STATUS.md`, then the sources in §6.

---

## 1. The problem, stated precisely

Background logic is **CEV** = H + Classicism + propositional Equivalence +
vector (ζ) Equivalence. It is the turnstile, not part of the axiom set.
Vocabulary: constants `Pure_σ, Fun_σ : σ →ₒ Prop` at each type. Defined:
`⊤ := ∀p:Prop. p → p` and `□A := (A = ⊤)`.

**X** (the statement whose consistency is in question) —

```
X  =  Pure_{(Prop→Prop)→Prop} ( Pure_{Prop→Prop} )
```

**A** (the assumptions) —

| | |
|---|---|
| A1 Purity schema | `Pure_σ M` for every closed constant-free `M : σ` |
| A2 Application closure | `∀F:σ→τ. ∀x:σ. (Pure F ∧ Pure x) → Pure (F x)` |
| A3 Exactly one fundamental proposition | `∃x:Prop. Fun x ∧ ∀y:Prop. (Fun y → y = x)` |
| A4 No fundamentals elsewhere (σ ≠ Prop) | `∀x:σ. ¬ Fun x` |
| A5 Unary Recombination | `∀F:Prop→Prop.∀p:Prop. (Pure F ∧ Fun p) → (□(F p) → ∀q. F q)` |

**The question:** is `A ∪ {X}` consistent?

Three things about this statement that are easy to get wrong:

- **Zeroary Recombination is redundant** and is *not* in A. CEV proves modal T
  unrestrictedly, so the purity antecedent is idle. Checked:
  `CEV_proves_zeroary_recombination` in `frontier/Bacon_PP_Minimal_Axioms.thy`.
- **Purity of Fun is deliberately absent.** `pp_purity_of_fun` is defined but in
  no axiom set. That omission *is* the question.
- **CEV⁺, not CEV.** Goodman writes `T₀ + PP + ∃fun′ + L2 + Inv ⊢ ⊥`, i.e.
  added principles are *axioms*, closed under the rules. So the target is
  `CEV_axiom_consistent` (`⊬CEV⁺ ⊥`), which is strictly stronger than the
  set-derivability version the repo's `pp_recombination_consistency_question`
  uses. Say which one you mean whenever you claim consistency.

Variants: adding Exhaustion gives the full-QLN question; further adding the
persistence schema gives the third. A5-only is the philosophically central one.

---

## 2. The single most important fact about this repo

**Goodman's own notes (`../PP_project_notes copy.pdf`, July 2026) are the
specification.** They are far ahead of this repo on the refutation side. His T1–T9
(object-language) and M1–M7 (model-theoretic) results are *hand-verified within
his collaboration, not machine-checked* — "checked n×" means exactly that.
Refereeing them is what this infrastructure is actually good for.

His T6 gives **four** routes to `⊥`: `T₀ + PP + ∃fun′` plus L2 with any of Inv,
WI, TU, and `strong-L2 + RS`. The contrapositive is the live state of play: any
model of the theory + PP must contain either cross-input collisions of pure
operators on `fun′` propositions (¬L2), or pure invertible operators that are
neither uniformly truth-preserving nor truth-flipping (¬TU). **The remaining
distance to refuting PP is a classification of G**, the group of pure reversible
operators.

His open problem **#1 is explicitly flagged "well-suited to mechanization"**:
calibrate L2 in Bacon's appendix model — do two non-≈ pure operators ever agree
on `fun′` inputs there? That model *is* this repo's word action (§4). This is
probably the highest-value target available and it is not what the internal
consensus plan recommended (that plan predates the notes).

---

## 3. Audit of this repo against the notes, §2 — results

Fifteen of seventeen items matched. Both apparent divergences were resolved, one
of them *against* my own initial finding:

- **Modalized Functionality — NOT missing.** I first recorded it as absent and
  added it as an axiom. Wrong. *Classicism* footnote 18 (p. 16): "C includes
  Modalized Functionality (see §1.5)", and §1.5 (p. 17) proves **Intensionality**
  `□∀z⃗(Xz⃗ ↔ Yz⃗) → X = Y` is a theorem of C. Intensionality has the weaker
  antecedent, so it implies MF. Bridge to this repo, p. 15: any H-theory closed
  under Propositional Equivalence together with ξ or ζ is closed under Logical
  Equivalence — and the repo has both, its `zeta_body` *being* Bacon–Dorr's
  ζ-Equivalence. So repo-CEV ⊇ Classicism ⊢ MF.
- **The `C_proves` axiom stock — not extra.** *Classicism* Figures 3 and 4 match
  it exactly, are "instances of Logical Equivalence", and Appendix A proves the
  converse. Equivalent axiomatizations.
- **H matches.** Book Def 5.1 gives PC1–3, UI, β, η, MP, Gen; the Classicism
  paper adds Ref, LL, EG as H-axioms, which is the repo's `H_proves`. The book's
  Rule of Substitution for non-logical constants is `CEV_proves_subst_const`.

**Net: the repo's theory is exactly T₀.** Not weaker, not stronger. Transfer is
unobstructed in both directions.

### The one divergence that stands

**The repo used the invariance reading of purity.** `pp_purity_operator F =
{i. pp_fun_invariant (pp_fun_view i F)}`. Goodman's M2 is titled *"the invariance
reading of purity is not an option"*, and his M1 says **PP fails at t→t in this
very model**. So `pp_purity_of_pure_holds_in_word_action` — which correctly
proves `pp_second_order_invariant pp_purity_operator` — does **not** show PP holds
in the word action, and the claim attached to it is false. Withdrawn.

Fix 2 is in `frontier/Bacon_PP_Definable_Purity.thy`: `pp_definable_purity L F =
{i. pp_fun_view i F ∈ L}` with the logical stock `L` a parameter (pinning it down
needs the `oterm` denotation bridge; everything proved is uniform in `L`), plus
`pp_definable_purity_subset_invariance`, `pp_readings_differ_of_proper_stock`,
and `pp_invariant_operators_outnumber_propositions` — M2's counting argument,
machine-checked.

Reassuringly the *model* is faithful and only the reading was wrong: M1 computes
`Pure_t` at the bottom type as `λp.(□p ∨ □¬p)`, and `pp_purity_of_meet`
independently gives `pp_purity_operator (λP. b ∩ P) = pp_decided b` with
`pp_decided X = □X ∪ □(−X)` — the same operator.

---

## 4. Ground rules — please keep these

1. **`isabelle build -D .` must stay green.** Baseline ~7s.
2. **`options [timeout = 15]` in ROOT. Do not raise it.** It exists so runaway
   proofs fail fast. It had drifted to 600 during this session, which made every
   failure take minutes and cost a lot of time before it was noticed. If a build
   is slow, **bisect** — comment out from the end and re-add in blocks. Three
   builds found two bugs that an hour of guessing had not.
3. **No `sorry`, `oops`, `admit`, `quick_and_dirty`.** A claim counts as proved
   only when a checked Isabelle theorem represents it.
4. **Do not use Caie or `ContextVectorEquivalence`.** Not part of this problem.
5. Sessions are split (`Higher_Order_Metaphysics`, `..._PP` in `pp/`,
   `..._PP_Frontier` in `frontier/`) specifically to keep iteration short. New
   work goes in `frontier/`; avoid editing the base session, which forces a
   full rebuild.
6. **Beware bare `auto`.** The `H_proves`/`C_proves`/`CE_proves`/`CEV_proves`/
   `compatible_step` constructors are all `[intro]`, so `auto` on goals in this
   development can search enormously. Prefer explicit `rule`/`intro`.

---

## 5. What is in flight, and exactly where it stands

**Unary Intensionality in repo-CEV**, `frontier/Bacon_PP_Intensionality.thy`.
Currently green; Codex has been asked to finish it. Target:

```
Γ ⊢CEV Imp (□ (Forall σ (App (shift X) (Var 0) ↔ₒ App (shift Y) (Var 0))))
           (Eq (σ →ₒ Prop) X Y)
```

then MF as a corollary (`X z = Y z` gives `X z ↔ Y z` by Ref and LL).

Route (Classicism §1.5): ζ is theorem-level and so cannot be applied to the
hypothesis. Instantiate ζ at the **guarded** pair `F := λz.(Xz ∧ C)`,
`G := λz.(Yz ∧ C)` with `C := ∀z.(Xz ↔ Yz)`, whose pointwise biconditional *is*
an H-theorem (from the UI instance `C → (Xz ↔ Yz)`); then use `□C`, i.e.
`C = ⊤`, with LL to replace `C` by `⊤`; then discharge `λz.(Xz ∧ ⊤) = X`; then
assemble with `CEV_eq_trans_from`.

**Already checked, do not redo:** `subst_rename_to_rename`,
`subst_lift_shift_by_2`, `subst0_var0_shift_by_2`, `subst0_var0_lift_ren_Suc`,
`shift_ObjTrue` (de Bruijn infrastructure the repo lacked — it had only the
identity case, `subst_rename_inverse`); `intens_conj`, `intens_pred`, their
typing lemmas, `typed_shift_ctx`/`typed_var0`/`typed_shift_app`; and
`intens_pred_beta`, the one beta step.

**The open obstacle.** All four remaining steps need transitivity of the object
biconditional, and the direct route via a `prop_tautology` instance for
`(A ↔ B) → ((B ↔ C) → (A ↔ C))` blows the 15s budget. Even the semantic half
alone —

```isabelle
lemma "∀v. prop_eval v (Imp (A ↔ₒ B) (Imp (B ↔ₒ C) (A ↔ₒ C)))" by auto
```

— times out, which I do not understand and did not resolve. `prop_tautology Γ F`
unfolds to `Γ ⊢ F : Prop ∧ (∀v. prop_eval v F)`; `prop_eval` reduces on the
constructors; the residue is a three-atom propositional tautology. And
`CEV_uncurry_conj` (`Bacon_S4.thy:138`) does a three-variable `prop_tautology`
with plain `by auto` and is fine. The difference may be that `ObjIff` expands so
the term carries six `Imp` subterms. Leading hypothesis: the `[intro]` blanket
(ground rule 6) makes `auto`'s classical search explode. **Unconfirmed — I was
wrong about this twice already.** If it can't be made cheap, avoid it: route
through `CEV_zeroary_equivalence` → `CEV_eq_trans_from` → Leibniz at `prop_id`,
so no large propositional tautology is ever checked.

---

## 6. Sources, all local

| What | Where |
|---|---|
| Goodman's project notes — **the specification** | `../PP_project_notes copy.pdf` |
| Bacon & Dorr, *Classicism* | `../Bacon_Dorr_Classicism.pdf` |
| Bacon, *Logical Combinatorialism* | `../tmp/pdfs/Bacon_Logical_Combinatorialism.pdf` |
| Bacon, *A Philosophical Introduction to Higher Order Logics* | `../Bacon_A Philosophical Introduction to Higher Order Logics.pdf` |
| Consensus debate 1 | `reports/PP_consensus_stocktaking_2026-07-25.md` |
| Consensus debate 2 | `reports/PP_consensus_stocktaking_2_2026-07-25.md` |

---

## 7. Where to go next

Ranked, with the notes taken into account. The internal consensus plan in
`STATUS.md` predates the notes and its top items are stale.

1. **Finish Intensionality** (§5). Unblocks QSS → `fun′` → `Pure(fun′)` → T6.
   Without `fun′` the T6 liar `D := λp.∀X∀q(Pure(X) ∧ fun′(q) ∧ p = Xq → ¬Xp)`
   cannot even be *stated* here, which is the real reason the earlier CEV⁺
   refutation search found nothing — it searched `Prop → Prop` operators built
   from `Pure` and `K`, a far too small space.
2. **Mechanize Goodman's open problem #1** — calibrate L2 in Bacon's appendix
   model. He flags it as suited to mechanization; the model is this repo's word
   action; the machinery largely exists. Either refutes L2 (killing the main
   refutation route) or supports seeking an object-language derivation of it.
3. **Machine-referee T6's four routes.** They are hand-checked only.
4. **Replace the purity interpretation throughout** with the definability
   reading and sweep every result that leaned on invariance (§3).
5. **A model of A + ¬X.** Lower value for Goodman — M1 already settles that PP
   fails at t→t in Bacon's model, so A is consistent and X is independent, and
   the question is non-degenerate. Worth it only as infrastructure validation.

## 8. Claims withdrawn during this session — do not resurrect

- PP holds in the word action (contradicts M1; used the invariance reading).
- The repo's theory is weaker than T₀ (it is exactly T₀).
- The CEV⁺ step-2 null result is evidence for consistency (it is evidence the
  search space was too small).
- `base_sound` fails for the word action (only conditional: it fails **if** CEV
  proves 5 — and CEV almost certainly does *not*, at ~0.99; Bacon–Dorr show
  Classicism's propositional modal fragment is exactly S4, and Prop 2.2
  identifies necessity of distinctness with 5 and B and denies it is a theorem).
- The constant-substitution lemma is missing (it exists:
  `CEV_proves_subst_const`).
- All consistency credences (~0.55, ~0.40–0.45). They were computed against a
  mis-specified theory and a wrong reading of `Pure`.
