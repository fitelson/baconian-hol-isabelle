# Staged TFF search for the remaining L2 premises

These files are the multisorted first-order counterparts of the three
remaining THF hard targets:

1. `04b_full_T0_PP_implies_classification.tff.in`;
2. `06b_full_T0_PP_implies_orbit.tff.in`; and
3. `08b_full_T0_PP_implies_y_transport.tff.in`.

Run them from this directory so that Vampire resolves the local `include`:

```sh
cd vampire/l2_staged_tff
vampire --mode portfolio --cores 6 --time_limit 3600 \
  04b_full_T0_PP_implies_classification.tff.in
```

The shared file `00_full_t0_pp_base.tff.in` imports the corrected
unworlded-applicative TFF representation of the complete finite
\(T_0+\mathrm{PP}+\exists\fun'\) stock.  Its whitelist omits both `not_L2`
and the old `$false` conjecture.

The TFF encoding reifies unary operators as elements of the sort `op1`;
`app(X,P)` represents application and `compose(X,Y)` represents composition.
Consequently, a TFF proof is a theorem of this first-order representation.
It still requires Isabelle replay before it counts as a theorem of the full
schematic CEV+ theory.  A TFF model or timeout does not refute derivability in
THF or Isabelle.

The initial bounded runs are recorded in `RESULTS_2026-07-29.md`.
