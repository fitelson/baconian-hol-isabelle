# Staged THF search for L2

Run these files from this directory so that Vampire resolves the two local
`include` files:

```sh
cd vampire/l2_staged_thf
vampire --mode portfolio --cores 6 --time_limit 60 \
  01_reversible_implies_injective.thf.in
```

The files form three proof ladders.

1. **Composition classification**
   - `02a_one_way_agreement_transport.thf.in`
   - `02b_collision_implies_agreements.thf.in`
   - `02_collision_implies_agreements.thf.in` (unsplit comparison target)
   - `03_classification_implies_L2.thf.in`
   - `04_PP_implies_classification.thf.in` (hard target)
2. **Reversible-orbit reachability**
   - `05a_explicit_orbit_witness_implies_kind.thf.in`
   - `05b_orbit_implies_L2.thf.in`
   - `05_orbit_implies_L2.thf.in` (unsplit comparison target)
   - `06_PP_implies_orbit.thf.in` (strong hard target)
3. **Y-relative transport**
   - `07a_explicit_y_transport_witness_implies_kind.thf.in`
   - `07b_y_transport_implies_L2.thf.in`
   - `07_y_transport_implies_L2.thf.in` (unsplit comparison target)
   - `08_PP_implies_y_transport.thf.in` (weaker hard target)

Only a theorem proved in an earlier file is admitted as a lemma in a later
file.  In particular, file 02b admits the result targeted by file 02a, and
file 03 admits the result targeted by file 02b.  The
hard-target files contain the minimal represented PP background, the
existence of a `fun'` proposition, Goodman's diagonal `D`, and its verified
purity consequence.  They do not contain the denial of L2 or the conjecture
`$false`.

There is also a second tier of hard targets using the complete finite
background represented in the original one-hour THF probe:

- `04b_full_T0_PP_implies_classification.thf.in`
- `06b_full_T0_PP_implies_orbit.thf.in`
- `08b_full_T0_PP_implies_y_transport.thf.in`

Their common base, `00_full_t0_pp_base.thf.in`, imports the original theory by
an explicit whitelist.  It omits both `not_L2` and
`pp_funprime_implies_L2_target`, so none of the targets assumes the denial of
L2 or imports the old `$false` conjecture.

Finally, `09_successful_L2_reductions.thf.in` combines only lemmas proved in
the preceding split files.  It proves the three conditional results

1. composition classification implies weak L2;
2. `fun'`-orbit reachability implies weak L2; and
3. \(Y\)-relative transport implies weak L2.

No PP-to-premise conjecture is admitted in that file.

A Vampire theorem remains a result about the represented THF fragment.  Its
used premises must be replayed in Isabelle before it counts as a theorem of
the full schematic CEV+ theory.

The first bounded run is recorded in
`RESULTS_2026-07-29.md`.
