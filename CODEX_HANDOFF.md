# Handoff: Goodman's PP consistency problem

## 0. Live checkpoint: Goodman T1--T5 and three T6 routes verified or sharply resolved

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
  abstraction over `Pure_{t→t}`.
- `frontier/Bacon_PP_Goodman_T6_Inv.thy` proves
  `[] ; pp_T6_Inv_axioms ⊢CEV+ ⊥`.  The axiom stock is exact: purity schema,
  application closure, PP at `t→t`, `∃fun′`, weak L2, and Inv.  Both the
  same-kind witness and the `fun′` witness are eliminated in the
  object-language calculus.  No QLN, Recombination, Exhaustion,
  fundamentality, Persistence, Purity of Fun, WI, TU, RS, or strong-L2 enters.
- `frontier/Bacon_PP_Goodman_T6_TU.thy` proves
  `[] ; pp_T6_TU_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and TU.  The truth-flipping case eliminates the inverse existential and
  uses the conjugate `Z∘D∘Z⁻¹`; it imports no Inv, WI, strong-L2, RS, QLN,
  fundamentality, Persistence, or Purity of Fun.
- `frontier/Bacon_PP_Goodman_T6_WI.thy` proves
  `[] ; pp_T6_WI_axioms ⊢CEV+ ⊥` from the exact core plus `∃fun′`, weak L2,
  and WI.  The key theorem `CEV_axiom_WI_implies_TU` derives TU directly:
  every WI witness has the form `λp.(p↔A)`, hence is truth-preserving if `A`
  and truth-flipping if `¬A`.  This uses neither the stronger T1 stock nor
  Exhaustion.  An explicit axiom translation then reuses the verified TU
  contradiction.  No Inv, strong-L2, RS, QLN, Recombination, fundamentality,
  Persistence, or Purity of Fun enters.
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
- `frontier/Bacon_PP_Goodman_Fun_Prime_Noncontingency.thy` machine-proves
  T2e using the literal modal rendering `□r ∨ □¬r`.
  `frontier/Bacon_PP_Goodman_T2f_Verified.thy` machine-proves T2f as one
  conditional object-language theorem containing all fifteen pairwise
  inequalities among `⊤`, `⊥`, `r`, `¬r`, `(r=⊤)`, and `(r=⊥)`.
  Claude Opus 5 independently rebuilt these results and replayed the entire
  T2a--T2f chain over the PP-free core consisting only of the purity schema
  and application closure.  PP and Persistence are unused; application
  closure is genuinely needed.
- `frontier/Bacon_PP_Goodman_Pure_Proposition_Triviality.thy`,
  `frontier/Bacon_PP_Goodman_Biconditional_Classification.thy`, and
  `frontier/Bacon_PP_Goodman_WI_Collapse.thy` machine-prove all three stages
  of T1: every pure proposition is `⊤` or `⊥`, each pure-indexed
  biconditional operator is `id` or `¬`, and WI collapses to Inv.
  Claude Opus 5 independently audited both consequence derivations and
  returned PASS.
- The T3 theories now machine-prove the exact modal core and both calibrated
  repairs.  Necessitated QSS plus Persistence yields only
  `◇(Y=Z)`, not the actual `Y=Z` required by `fun′`.  Exact T3 follows from
  zeroary Exhaustion (`CEV_Goodman_T3_heredity_with_exhaustion`) or, more
  sharply, from pure-identity rigidity
  (`CEV_Goodman_T3_heredity_rigid`).  The unrestricted rigidity repair is
  refuted by `CEV_unrestricted_rigidity_refuted`.  The literal Section 4
  stock, with the globally assumed `∃fun′`, is now
  `pp_T3_advertised_axioms`, and
  `CEV_Goodman_T3_advertised_with_exhaustion` proves the repaired theorem
  over that exact stock.  The strengthened two-world theorem
  `Goodman_T3_advertised_modal_abstraction_countermodel` includes an actual
  `fun′` witness, unique fundamentality, global QSS, Persistence, Necessity
  of Identity, and Modalized Functionality while still refuting T3.  Claude's
  independent audit confirms that Goodman's advertised premise list omits
  this rigidity commitment.  Exact non-derivability from every unbounded
  member of `pp_T3_advertised_axioms` remains open pending a full model rather
  than only the strengthened modal abstraction.
- `frontier/Bacon_PP_Goodman_Higher_Type_Diagonal.thy` machine-proves T4 in
  the stronger object-language form
  `∀C(Pure(C) → ¬fun′_{t→t}(C(r)))`.  Its exact closed stock is
  `pp_T4_axioms = pp_purity_schema ∪ pp_application_closure_schema`;
  PP, `fun′(r)`, QSS, Persistence, and Exhaustion are unused.  The proof
  explicitly constructs Goodman's two distinct pure predicates that agree at
  `C(r)`. Claude Opus 5 independently clean-built and fully unfolded the
  theorem, checked the proof graph for oracles and residual hypotheses, and
  returned PASS WITH QUALIFICATIONS.  The qualifications concern semantic
  non-vacuity of the weak stock and the generic open-axiom interface, not the
  T4 derivation. Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T4_2026-07-25.md`.
- `frontier/Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse.thy` records a crucial
  consistency qualification found by Claude: if `fun′(r)` is inserted into
  the theorem-level axiom stock rather than retained as an antecedent, Rule
  of Equivalence collapses `(r=⊤)` and `(r=⊥)` to `⊥`; T2f fails and the
  resulting theory proves `⊥`.
- `frontier/Bacon_PP_Goodman_Proliferation.thy` machine-proves T5:
  `fun′(r) → ∃q(fun′(q) ∧ q ≠ r ∧ q ≠ ¬r)`.  Its exact headline stock is
  `pp_purity_schema ∪ pp_application_closure_schema ∪ {pp_target_PP}`.
  The existence of a `fun′` proposition remains an object-language
  antecedent, never a theorem-level axiom.  No L2, Inv, WI, TU, RS,
  Exhaustion, Persistence, Recombination, fundamentality, or Purity of Fun
  enters the derivation.
- Claude Opus 5 adversarially audited T5 and returned PASS WITH
  QUALIFICATIONS.  It independently reconstructed both liar refutations,
  checked every binder shift and the local-assumption boundary, clean-built
  the session, verified all ten theorem objects have no oracles or residual
  hypotheses, and machine-checked decisive controls for a missing negation,
  a reversed composition, and deletion of `fun′(r)`.  Full report:
  `reports/CLAUDE_AUDIT_GOODMAN_T5_2026-07-25.md`.
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
- `frontier/Bacon_PP_Goodman_T6_RS_Encoding.thy` and
  `frontier/Bacon_PP_Goodman_T6_RS.thy` machine-prove the remaining T6 route.
  `CEV_Goodman_T6_RS` establishes `T₀ + PP + strong-L2 + RS ⊢ ⊥` from the
  exact stock. RS itself supplies a nonempty `fun′`-only specification, so no
  separate `∃fun′` axiom is present. The proof derives collision injectivity,
  proves the existential diagonal pure, verifies both directions of its liar
  law, and eliminates both existential witnesses object-linguistically.
- T7a is now machine-proved in
  `frontier/Bacon_PP_Goodman_T7_Absorption.thy`.
  `CEV_Goodman_T7a` establishes the exact closed absorption result from
  `T₀ + PP + ∃fun′ + L2`, with no Inv/WI/TU/RS classification axiom.
  The object-language proof extracts the liar counterexample witnesses,
  obtains same-kind via weak L2, transports truth to `D(Zd)`, and eliminates
  all witnesses.
- T8 now has an exact 31-object encoding in
  `frontier/Bacon_PP_Goodman_T8_Encoding.thy`: the five advertised base
  operators, their 31 nonempty subsets, the corresponding kind properties,
  and literal pairwise-distinctness formulas for both operators and values.
  The file proves both lists have length 31 and type-checks the full target.
- T8b is machine-proved by `CEV_Goodman_T8_kind_uniqueness` in
  `frontier/Bacon_PP_Goodman_T8_Kind_Uniqueness.thy`.
- T8a is machine-proved by `CEV_Goodman_T8a` in
  `frontier/Bacon_PP_Goodman_T8_Base_Kinds.thy`.  The theorem packages all
  ten base-pair separations and uses no L2 or group-classification principle.
  The nonconstant cases use `fun′` closure under arbitrary group members;
  the constant cases use the checked left-absorption equations for `K⊤` and
  `K⊥`.
- T8c is machine-proved in
  `frontier/Bacon_PP_Goodman_T8_Growth.thy`.
  `CEV_Goodman_T8c` proves the witness-parametric 31-operator/31-value claim;
  `CEV_Goodman_T8c_closed` proves the exact closed existential from
  `pp_T8_full_axioms = {∃fun′, L2} ∪ pp_T6_core_PP_axioms`. The proof
  explicitly abstracts the `Pure` constant in every generated kind property,
  derives its purity via PP plus application closure, separates different
  subsets using a selected base-kind witness, excludes omitted kinds via T8b
  plus the ten T8a separations, and then lifts operator inequalities to
  values at a `fun′` witness.
  The consolidated audit initially found that two finite-list distinctness
  lemmas used `by eval`, giving both exported T8c theorems one
  `Code_Generator.holds_by_evaluation` oracle. They have been replaced by
  structural proofs from `distinct_set_subseqs`, injectivity of the
  generated kind atoms, and a syntactic disjunction decoder. A focused
  post-repair theorem-object audit confirms zero oracles, hypotheses, and
  flex-flex constraints for `CEV_Goodman_T8c` and
  `CEV_Goodman_T8c_closed`.
- T7b is source-underspecified rather than an outstanding determinate
  Isabelle theorem. Goodman's PDF gives only the sentence that a
  “diagonal-on-kinds likewise has no fixed point but a shifted one,” without
  defining the diagonal, fixed/shifted point, binder structure, or exact
  stock beyond PP at `(t→t)→t`. Do not invent a formula and attribute it to
  Goodman; request an exact statement if this companion result is to be
  formalized.
- T9 remains, as advertised by Goodman, a meta-level cardinal-counting
  argument rather than a single object-language derivation. The advertised
  WI master equation remains a route-specific intermediate target, although
  the exact WI contradiction is already checked via WI⇒TU.
- The single consolidated adversarial audit is complete as a preserved
  report. It returned PASS WITH QUALIFICATIONS. Its T8c evaluation-oracle
  finding was correct and has been repaired. Its purported second finding
  was not: `CEV_Goodman_T3_heredity_with_exhaustion` exists as the corollary
  over the full stock, while `CEV_Goodman_T3_heredity_min` is the sharper
  theorem over a smaller stock. All other principal theorem objects were
  clean. T7b remains
  source-underspecified, T9 remains meta-level, and the original PP
  consistency question remains open because every T6 contradiction is
  conditional on L2 plus a classification principle (or strong-L2 plus RS).
- The next major verification phase should cover Goodman's model-theoretic
  M-claims in a parallel matrix. This is likely to be the most useful source
  of constraints for the later consistency attack, especially through a
  semantic calibration of L2 and the pure reversible group `G`.

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
2. **`options [timeout = 60]` in ROOT.** The frontier outgrew the former
   15-second whole-session limit after all four T6 routes were added. A clean
   eight-thread build still takes about seven seconds. If a command is slow,
   **bisect** rather than waiting for the session limit.
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
`CEV_intens_conj_true_eq`. The full project remains green under the 60-second
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
