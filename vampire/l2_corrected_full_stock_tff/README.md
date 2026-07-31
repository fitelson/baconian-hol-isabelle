# Corrected full-stock staged Vampire suite for L2

This suite tests Goodman's negative L2 route in a finite multisorted
representation of the relevant CEV+ stocks. It is intentionally TFF rather
than direct THF. Unary operators are reified as objects of sort `op1`, so
operator identity is not silently identified with THF meta-level extensional
equality. Modalized Functionality remains an explicit premise.

Run every file from this directory so that Vampire resolves the local
includes:

```sh
cd "/Users/fitelson/Library/CloudStorage/Dropbox/non-MUSIC/todo/Higher_Order_Stuff/Higher_Order_Metaphysics/vampire/l2_corrected_full_stock_tff"
```

## Corrections relative to the old finite probe

1. PP is typed correctly as purity of the unary-purity classifier:
   `pure_op2_at(W,pure_unary_classifier)`.
2. Purity of `Pure_Prop`, which belongs to the logical-purity schema, is kept
   distinct from PP.
3. Proposition and operator identity are represented by the world-relative
   relations `eq_prop_at` and `eq_op_at`, not by TFF meta-level equality.
   This preserves the modal gap between Recombination and QSS.
4. Neither stock assumes existence of a `fun-prime` proposition.
5. No file contains Goodman's T6 diagonal `D` or assumes that it is pure.
6. The Recombination-only and full-QLN stocks are separate.
7. The full-QLN bridge target asks Vampire to derive `exists fun-prime`.
8. The Recombination-only conditional targets import the extra
   `exists fun-prime` premise from a visibly separate file.
9. Weak L2 is a conjecture only in the L2 targets; it is never a stock axiom.

## Shared files

- `00_common_semantics.tff.in`: common vocabulary, finite logical-purity
  instances, relevant application closure, the explicit
  Recombination-to-QSS machinery, and definitions of `fun-prime`, `G`,
  sameness of kind, the three sufficient conditions, and weak L2.
- `01_recombination_PP_stock.tff.in`: finite relevant representation of
  `pp_recombination_PP_axioms`.
- `02_full_QLN_PP_stock.tff.in`: extends file 01 by zeroary and unary
  Exhaustion, corresponding to `pp_full_QLN_PP_axioms`.
- `03_exists_fun_prime_assumption.tff.in`: the isolated extra premise used
  only by files whose names contain `plus_fun_prime`.

## Stage 1: algebraic controls

These verify that the three proposed intermediate conditions really suffice
for weak L2 in the corrected representation:

```sh
vampire --mode portfolio --cores 1 --time_limit 60 05_classification_implies_L2.tff.in
vampire --mode portfolio --cores 1 --time_limit 60 06_orbit_implies_L2.tff.in
vampire --mode portfolio --cores 1 --time_limit 60 07_y_transport_implies_L2.tff.in
```

## Stage 2: full QLN plus PP

First test the bridge that should produce a `fun-prime` proposition:

```sh
vampire --mode portfolio --cores 6 --time_limit 600 10_full_QLN_derives_fun_prime.tff.in
```

Then run the three hard targets separately:

```sh
vampire --mode portfolio --cores 6 --time_limit 3600 11_full_QLN_implies_classification.tff.in
vampire --mode portfolio --cores 6 --time_limit 3600 12_full_QLN_implies_orbit.tff.in
vampire --mode portfolio --cores 6 --time_limit 3600 13_full_QLN_implies_y_transport.tff.in
```

The direct L2 file is a comparison target, not the preferred first search:

```sh
vampire --mode portfolio --cores 6 --time_limit 3600 14_full_QLN_implies_L2.tff.in
```

## Stage 3: Recombination-only plus PP

File 20 tests the presently open Recombination-only bridge without assuming a
`fun-prime` witness:

```sh
vampire --mode portfolio --cores 6 --time_limit 3600 20_recombination_derives_fun_prime.tff.in
```

Files 21--24 explicitly add `exists fun-prime`. They test what follows
conditional on that extra premise:

```sh
vampire --mode portfolio --cores 6 --time_limit 3600 21_recombination_plus_fun_prime_implies_classification.tff.in
vampire --mode portfolio --cores 6 --time_limit 3600 22_recombination_plus_fun_prime_implies_orbit.tff.in
vampire --mode portfolio --cores 6 --time_limit 3600 23_recombination_plus_fun_prime_implies_y_transport.tff.in
vampire --mode portfolio --cores 6 --time_limit 3600 24_recombination_plus_fun_prime_implies_L2.tff.in
```

## Interpretation of results

- `Theorem` or `Unsatisfiable` on a conjecture supplies a proof in this finite
  representation. The used premises must still be replayed in Isabelle before
  the result counts as a theorem of CEV+.
- `CounterSatisfiable` or `Satisfiable` supplies a model only for this finite
  representation. It is not a model of the full schematic theory.
- `Timeout` establishes neither derivability nor nonderivability.

The suite represents the exact named stocks only through the finitely many
type and logical-term instances displayed in the files. This is appropriate
for searching for a finite proof core, but it is not itself an encoding of
every member of the unbounded purity and application-closure schemata.

Codex has not run these files. A user run of file 20 on the first version of
the suite exposed a world-relative-identity error; that result is invalid and
the files have been corrected. A subsequent user run of corrected file 10
proved the expected full-QLN `exists fun-prime` bridge and explicitly used
zeroary Exhaustion. See `RESULTS_2026-07-30.md`.
