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
        │   └── Higher_Order_Metaphysics_PP_Models
        └── Goodman_CEVplus_Canonical
```

The HOL-ZF fragment and bridge sessions continue below
`Higher_Order_Metaphysics_PP_ZF_Model`; they are listed separately below.

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

Session: `Higher_Order_Metaphysics_PP_ZF_Model`

Bacon-style substitution models over Isabelle's HOL-ZF universe.  This
directory contains the formalizations of Bacon's Theorem 10.1, Goodman's
model-theoretic claims, and the exact semantic L2 counterexample.

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
| `modal_depth_two/` | `Higher_Order_Metaphysics_PP_ZF_Modal_Depth_Two` |

These sessions isolate failures and preserve short rebuild times.  A fragment
is not described as a model of Goodman's full theory unless its complete
schema and closure obligations have been proved.

### `bridges/`

`Goodman_CEVplus_ZF_Bridge` and
`Goodman_CEVplus_Modal_Quantified_Bridge` translate between the CEV+
axiom stocks and the HOL-ZF fragment models.

## Session declarations

All active project sessions are declared in the root `ROOT` file.  Separate
`ROOT` files remain only for dated audit sessions, generated finite-core
replays, scratch material, and the optional Classicism prefix.  Consequently
the entire maintained development is discoverable with one command:

```sh
isabelle build -j 1 -D .
```

No additional `-d` options for Goodman subdirectories are required.

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
