# Repository structure

The Isabelle development has three principal layers.  The directory structure
and session-parent relation follow the mathematical dependence:

```text
Bacon_Base
└── Bacon_Classicism
    └── Goodman_CEVplus
        ├── Higher_Order_Metaphysics_PP
        │   ├── Higher_Order_Metaphysics_PP_Frontier
        │   │   └── Higher_Order_Metaphysics_PP_ZF_Model
        │   │       └── Higher_Order_Metaphysics_PP_ZF_Secondary
        │   └── Higher_Order_Metaphysics_PP_Models
        └── Goodman_CEVplus_Canonical
```

The older HOL-ZF fragments and bridge sessions continue below
`Higher_Order_Metaphysics_PP_ZF_Secondary`; they are listed separately below.

## 1. Bacon's base theory

Session: `Bacon_Base`

Directory: `theories/base/`

Theories:

```text
Bacon_Types
Bacon_Syntax
Bacon_Typing
Bacon_Substitution
Bacon_Beta
Bacon_Deduction
```

This layer contains the typed object language, renaming and substitution,
beta conversion, and Bacon's proof theory \(H\).  It does not import
Classicism or any Goodman-specific vocabulary.

## 2. Classicism, CE, and CEV

Session: `Bacon_Classicism`

Directory: `theories/classicism/`

This layer begins with `Bacon_Abbreviations` and `Bacon_Classicism`, adds CE
and vector Equivalence through `Bacon_Modal_Derivations` and `Bacon_Zeta`,
and contains the modal, semantic, completeness, Henkin, quotient, and finite
CEV model developments.  Its terminal theory is `Bacon_Finite_CEV_Model`.

The directory `theories/classicism/prefix/` retains the optional cached-prefix
session used by older incremental workflows.  It is not needed by the normal
central build.

## 3. Goodman's CEV+

Session: `Goodman_CEVplus`

Directory: `theories/goodman/`

The two entry theories are:

```text
Bacon_PP_Question
Bacon_CEV_Axiom_Extension
```

They introduce `Pure`, `Fun`, Recombination, Exhaustion, Purity of Pure, and
the CEV+ derivability relation in which Goodman's additional principles are
available as axioms while Generalization, Instantiation, and vector
Equivalence remain applicable.

All further work on Goodman's question is organized beneath this layer.

### `core/`

Session: `Higher_Order_Metaphysics_PP`

Reusable semantic and combinatorial machinery for Bacon's substitution
structures, purity, fundamentality, tree actions, orbits, and the original PP
diagonal.

### `notes/`

Session: `Higher_Order_Metaphysics_PP_Frontier`

The formal audit of Goodman's T1--T9 and M1--M7 claims, including the T3 and
M5 repairs, the T6 derivations, the T9 counting theorem, and the
Recombination--Exhaustion bridge.  The older session name is retained so that
existing theorem-qualified imports remain stable; the directory name records
its present role more accurately.

### `cevplus/`

Session: `Goodman_CEVplus_Canonical`

Finite-fragment, relative Lindenbaum, Henkin-completion, and canonical
semantics results for CEV+.

### `models/finite/`

Session: `Higher_Order_Metaphysics_PP_Models`

Isabelle certificates for explicitly bounded models produced by external
search.  These are calibration artifacts unless a separate translation
theorem connects them to the full theory.

### `models/hol_zf/`

Canonical session: `Higher_Order_Metaphysics_PP_ZF_Model`

Secondary session: `Higher_Order_Metaphysics_PP_ZF_Secondary`

Bacon's appendix model and the related comparison work over Isabelle's HOL-ZF
universe are separated into three directories and two sessions.

#### `models/hol_zf/canonical/`

This is the official source-faithful Bacon development.  Its dependency spine
is:

```text
Bacon_PP_ZF_Word_Propositions
  -> Bacon_PP_ZF_Full_MSet
  -> Bacon_PP_ZF_Exact_Frame
  -> Bacon_PP_ZF_Exact_Substitution
  -> Bacon_PP_ZF_Exact_10_1
  -> Bacon_PP_ZF_Exact_CEV_Soundness
  -> Bacon_PP_ZF_Exact_Enumeration
  -> Bacon_PP_ZF_Exact_Completeness
```

`Bacon_PP_ZF_Full_MSet` recursively uses Bacon's restricted function spaces
from Definition 7.2 and proves the all-type action, closure, surjectivity,
preimage-independence, and substitution/application facts required by
Proposition 8.  The subsequent theories prove Bacon's arbitrary-signature
Theorem 10.1 throughout the `t`-fragment, exact
H/Classicist/CE/CEV soundness including the individual Existence instance and
vector Equivalence, and Bacon's
enumeration/gluing completeness result for a fixed signature in the
proposition-generated fragment.  Isabelle supplies the branch-gluing proof
Bacon omits.  Signatures involving `e`-containing types remain outside scope,
as Bacon explicitly defers that extension.

#### `models/hol_zf/extensions/`

These theories interpret Goodman's `Pure`, `Fun`, closed logical stock,
Recombination, Exhaustion, and QLN vocabulary over Bacon's exact carriers.
They introduce no alternative model.  Both `canonical/` and `extensions/`
belong to `Higher_Order_Metaphysics_PP_ZF_Model`.

#### `models/hol_zf/secondary/`

This directory contains the older full, hyperintensional, Boolean-tree, and
natural-word frames, the finite-fragment and stock-enlargement experiments,
and the abandoned closure-code/PER construction.  These theories remain
available for comparison and calibration, but they are not the official Bacon
model.  They belong only to `Higher_Order_Metaphysics_PP_ZF_Secondary`.  The
maintained boundary check verifies both this session separation and that
neither `canonical/` nor `extensions/` imports them.

The source-level QLN granularity test is in
`notes/Bacon_PP_Goodman_Granularity_QLN.thy`.  It encodes the truth-functional
agreement and disagreement operators, reconstructs unary Exhaustion as a
generic CEV+ instance, proves their purity by application closure, and verifies
that the proposed modal condition is equivalent to pointwise truth uniformity
under full QLN.

### `models/fragments/`

The fragment sessions localize successive additions:

| Directory | Session |
|---|---|
| `truth_functions/` | `Higher_Order_Metaphysics_PP_ZF_Truth_Functions` |
| `necessity/` | `Higher_Order_Metaphysics_PP_ZF_Necessity` |
| `possibility/` | `Higher_Order_Metaphysics_PP_ZF_Possibility` |
| `higher_order_quantified/` | `Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified` |
| `fun_prime/` | `Higher_Order_Metaphysics_PP_ZF_Fun_Prime` |
| `t6_diagonal/` | `Higher_Order_Metaphysics_PP_ZF_T6_Diagonal` |

These sessions isolate failures and preserve short rebuild times.  A fragment
is not described as a model of Goodman's full theory unless its complete
schema and closure obligations have been proved.

The retired modal-depth-two fragment had been reserved for adding the genuine
alternations \(\Box\Diamond\) and \(\Diamond\Box\), reducing the repetitions
\(\Box\Box\) and \(\Diamond\Diamond\), closing the enlarged pure stock under
application, and retesting PP, both unary directions of QLN, Modalized
Functionality, and unique fundamentality.  It stopped before any stock or
model theorem was implemented.  Its useful modal-word syntax and
normalization lemmas remain in `higher_order_quantified/`; no verified model
result was removed.

### `bridges/`

`Goodman_CEVplus_ZF_Bridge` and
`Goodman_CEVplus_Modal_Quantified_Bridge` translate between the CEV+
axiom stocks and the HOL-ZF fragment models.

The constructive finite-fragment program is separated from those
translation bridges:

| Directory | Session | Role |
|---|---|---|
| `bridges/finite_fragments/` | `Goodman_CEVplus_Finite_Fragment_Model_Program` | Extracts the exact finite data and states the tailored-model interface used with compactness. |
| `bridges/finite_cyclic_model/` | `Goodman_CEVplus_Finite_First_Cyclic_Model` | Verifies the first cyclic packages, finite successor-component assembly, and the current `fun'`/T6 collision analysis. |

The latter session name is retained for qualified-name stability, although
its contents now extend beyond the first cyclic package.  Its successor
assembly theorem applies only when a later component's stock support is
separated from the old application sources and from the unary stock and its
classifier.  Internal stabilization of the classifier-bearing component
remains a distinct obligation.

## Session declarations

All active project sessions are declared in the root `ROOT` file.  Separate
`ROOT` files remain only for dated audit sessions, generated finite-core
replays, scratch material, and the optional Classicism prefix.  Consequently
the entire maintained development, including the Goodman claim audit, is
checked with one command:

```sh
./check_isabelle.sh
```

The script selects both the root sessions and the separately rooted maintained
audit, with a single serial Isabelle build plan.

## Reader-facing status

The mathematical status is not inferred from directory names.  Use:

- `reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md` for the exact
  status of claims in Goodman's notes;
- `reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf` for the
  reader-facing account;
- `STATUS.md` for the chronological implementation record.

The consistency question remains open.  In particular, a verified finite or
fragment model is not automatically a model of Goodman's unrestricted
logical-purity schema.

## Search tools

`finite_core_search/` is the general bounded derivability search. Its typed
term enumerator, CEV+ profiles, reference saturator, support minimizer, and
Isabelle contradiction replay are also used by `pure_diagonal_search/`.

`pure_diagonal_search/` restricts attention to closed logical terms

```text
B : (((Prop -> Prop) -> Prop) -> (Prop -> Prop))
```

and searches the pure unary operators `B(Pure)` forced by logical purity, PP,
and application closure. The initial exhaustive generated tranche has one
classifier occurrence outside quantifier scope; named priority builders add
the basic negative and positive diagonals and Goodman's T6 builder. A
generated Isabelle audit checks every candidate's type, empty nonlogical
vocabulary, and purity theorem. Any contradiction hit is passed to the
existing finite-core replay and is not certified before that replay builds.
