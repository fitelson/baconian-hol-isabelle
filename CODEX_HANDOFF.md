# Handoff: Goodman's PP consistency problem

## 0. Live checkpoint: Goodman T2a--T2d verified

Codex has resumed as driver.

- `frontier/Bacon_PP_Modalized_Functionality_Derived.thy` proves, in bare CEV,
  `[] ⊢CEV pp_modalized_functionality σ Prop`. Claude Opus 5 adversarially
  audited every rule and the de Bruijn closing step: correct and non-circular.
  This is the proposition-valued unary member only, not the full `σ,τ` schema.
- `frontier/Bacon_PP_T6_Encoding.thy` faithfully encodes `fun′`, composition,
  reversible operators, `G`, `≈`, weak L2, Inv, and Goodman's liar `D`.
- The T6-Inv axiom set is now exact and QLN-free: purity schema, application
  closure, PP at `t→t`, `∃fun′`, weak L2, and Inv. It contains no
  Recombination, Exhaustion, fundamentality assumptions, Persistence, or
  Purity of Fun.
- The same theory machine-proves `Pure(D)` using an explicit constant-free
  abstraction over `Pure_{t→t}`. The final T6-Inv derivation of `⊥` remains
  open.
- `frontier/Bacon_PP_Goodman_Composition.thy` now machine-proves the
  composition beta law, left and right identity, associativity, and purity of
  composition from the exact T6 core. It also provides versions of application
  closure and equality reasoning that are sound under temporary local
  assumptions.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Closure.thy` proves Goodman T2a:
  `fun′(p) ∧ G(Z) → fun′(Zp)`, `G(¬)`, and
  `fun′(p) → fun′(¬p)`, over every extension of the §4 core.
  The existential inverse in `G` is eliminated inside the object-language
  calculus.  The sharper intermediate result needs only a right inverse and
  does not use purity of the inverse or the left-inverse equation.
- Claude Opus 5 adversarially audited T2a and returned PASS.  It independently
  clean-built the frontier, found zero proof escapes, inspected the exported
  theorem objects (zero oracles or residual hypotheses), checked the crucial
  de Bruijn and local-assumption steps, and machine-checked exclusion of the
  stronger Goodman principles from the core.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2A_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Nontriviality.thy` proves Goodman T2b:
  `¬fun′(⊤)`, `¬fun′(⊥)`, and
  `fun′(p) → (p ≠ ⊤ ∧ p ≠ ⊥ ∧ p ≠ ¬p)` for every typed proposition `p`.
  The last inequality is proved already in bare CEV.
- Claude Opus 5 adversarially audited T2b and returned PASS.  Its independent
  audit theory proved the sharper dependency claim: the two refutations use
  only `Pure(id)`, `Pure(K⊤)`, and `Pure(K⊥)`; PP and application closure are
  not used.  It also generalized the argument to every closed constant-free
  proposition `M`, for which `¬fun′(M)` follows.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2B_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Attainment.thy` proves Goodman T2c in
  both parameter and exact quantified form:
  `fun′(r) → ∀p(Pure(p) → ◇(r=p))`.  Its diagonal proof identifies
  `λq.¬(q=p)` with the constant-truth operator under the supposition
  `□¬(r=p)`, then evaluates at `p` to contradict reflexivity.
- Claude Opus 5 adversarially audited T2c and returned PASS.  It independently
  clean-built the frontier, inspected the theorem objects, recomputed both
  beta reductions and the final binder shift, and machine-reproved the entire
  theorem over only `pp_purity_schema ∪ pp_application_closure_schema`.
  Thus PP itself, QSS, Recombination, Persistence, fundamentality, L2, Inv,
  and classification are all unused.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2C_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Possibly_Pure.thy` proves T2d,
  `fun′(r) → ◇Pure(r)`, from T2c at `⊤`, identity transport for purity, and
  derived possibility monotonicity.  Neither PP nor Persistence is needed:
  the required `Pure(⊤)` instance is a purity-schema axiom and is therefore
  necessitable in CEV's axiom-extension calculus.
- Claude Opus 5 adversarially audited T2d and returned PASS.  It independently
  re-proved the modal and identity-transport lemmas, machine-reproved the
  PP-free strengthening, and also machine-checked Goodman's original
  arbitrary-pure-`p` derivation using Persistence.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T2D_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Noncontingency.thy` now machine-proves
  T2e using the literal modal rendering `□r ∨ □¬r`; it awaits adversarial
  audit.  `frontier/Bacon_PP_Goodman_Pure_Proposition_Triviality.thy`
  machine-proves T1's main universal claim from zeroary Exhaustion and awaits
  audit.  `frontier/Bacon_PP_Goodman_Biconditional_Classification.thy`
  machine-proves that every pure-indexed biconditional operator is `id` or
  `¬`; exact WI-to-Inv packaging remains open.  T2f infrastructure is in
  `frontier/Bacon_PP_Goodman_Fun_Prime_Six_Distinct.thy`.
- Standing qualification: T2a--T2d are conditional derivability results in
  repository CEV.
  Non-vacuity of CEV plus the core is not yet proved.  Moreover,
  repository CEV takes ζ-Equivalence as primitive, whereas Goodman's `T₀`
  obtains it through Modalized Functionality; their identification remains a
  prose audit rather than a theorem internal to Isabelle.
- Claude's full audit is
  `reports/CLAUDE_AUDIT_MF_T6_2026-07-25.md`; the T1--T9 controlling matrix is
  `reports/GOODMAN_OBJECT_LANGUAGE_VERIFICATION_2026-07-25.md` (both local and
  gitignored by project policy).
- Next formal targets: adversarially audit T2e and the main T1 theorem, then
  settle the exact T2f pairwise-distinctness claim.

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

## 5. First Codex checkpoint: Unary Intensionality is complete

**Unary Intensionality in repo-CEV**, `frontier/Bacon_PP_Intensionality.thy`.
Codex completed it after this handoff was written. Machine-checked theorem:

```
CEV_unary_intensionality:
  Γ ⊢CEV Imp (□ (intens_condition σ X Y))
             (Eq (σ →ₒ Prop) X Y)
```

Route (Classicism §1.5): ζ is theorem-level and so cannot be applied to the
hypothesis. Instantiate ζ at the **guarded** pair `F := λz.(Xz ∧ C)`,
`G := λz.(Yz ∧ C)` with `C := ∀z.(Xz ↔ Yz)`, whose pointwise biconditional *is*
an H-theorem (from the UI instance `C → (Xz ↔ Yz)`); then use `□C`, i.e.
`C = ⊤`, with LL to replace `C` by `⊤`; then discharge `λz.(Xz ∧ ⊤) = X`; then
assemble by identity transitivity. This is now exactly what the theory proves.

**Checked infrastructure:** `subst_rename_to_rename`,
`subst_lift_shift_by_2`, `subst0_var0_shift_by_2`, `subst0_var0_lift_ren_Suc`,
`shift_ObjTrue` (de Bruijn infrastructure the repo lacked — it had only the
identity case, `subst_rename_inverse`); `intens_conj`, `intens_pred`, their
typing lemmas, `typed_shift_ctx`/`typed_var0`/`typed_shift_app`; and
`intens_pred_beta`.

The expensive biconditional tautology was avoided, not optimized. New helper
`CEV_biconditional_trans` follows the identity route:
`CEV_zeroary_equivalence` → `CEV_eq_trans_from` → Leibniz at `prop_id`.
The guarded ζ theorem is `CEV_intens_guarded_eq`; guard transport is
`CEV_intens_guarded_true_from_box`; truth discharge is
`CEV_intens_conj_true_eq`. The full project remains green under the 15-second
session timeout.

**Immediate next target:** derive unary Modalized Functionality from
`CEV_unary_intensionality`, then build QSS and `fun′`.

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

1. **Derive unary MF, then QSS and `fun′`.** Unary Intensionality is now done.
   The next proof turns pointwise proposition identity into pointwise
   biconditional, applies `CEV_unary_intensionality`, and packages the resulting
   MF instance. This unblocks QSS → `fun′` → `Pure(fun′)` → T6. Without `fun′`
   the T6 liar `D := λp.∀X∀q(Pure(X) ∧ fun′(q) ∧ p = Xq → ¬Xp)` cannot be stated
   here; the earlier CEV⁺ search considered only `Pure` and `K`.
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
