# Vampire search for Goodman's PP problem

This directory is a proof-search adjunct to the Isabelle development.  It does
not replace the deep embedding of CEV in Isabelle.

## Why the encoding is reified

Goodman's object-language identity is hyperintensional.  In particular,
`Box(p)` is the proposition `p = top`; it is not ordinary HOL necessity, and
object-language identities must not simply be translated as extensional
equality between HOL functions.  A direct shallow THF translation would
therefore strengthen the background theory and could produce a spurious
refutation.

The files here instead use separate first-order sorts for propositions and
unary propositional operators.  `holds(p)` says that the proposition represented
by `p` is true at the local CEV theory.  Operators are members of an opaque
sort, with application represented by `app`.  Built-in equality is used only
after passing to the local identity quotient.  Every nonlogical search lemma in
a benchmark must have an Isabelle theorem behind it.

This is deliberately asymmetric:

- a Vampire refutation is only a candidate proof and must be replayed in
  Isabelle;
- `Satisfiable`, saturation, or timeout establishes nothing about the full PP
  theory unless a separate model/translation theorem is proved;
- the purity and application-closure schemas are infinite, so a search file
  contains a documented finite, depth-bounded set of their consequences.

## Benchmarks

`goodman_t6_inv_calibration.in` is a calibration problem.  Its inputs are the
first-order images of independently machine-checked ingredients of
`CEV_Goodman_T6_Inv`: existence of a `fun'` proposition, purity and the defining
matrix of Goodman's liar `D`, the two T5 diagonal refutations, weak L2, the Inv
classification of the kind of `D`, and the relevant beta/composition
identities.  Vampire must reconstruct the final liar contradiction.

`goodman_t6_wi_master_inconsistent.in` isolates the propositional
inconsistency of Goodman's advertised WI master family.  Vampire refutes it
using only the master equation, `Pure(top)`, and `holds(top)`; the matching
deep-embedding result is `CEV_T6_WI_master_family_inconsistent` in
`theories/goodman/notes/Bacon_PP_Goodman_T6_WI_Master.thy`.  This benchmark and theorem do
not yet derive the master family from WI and L2.

`goodman_pp_recombination_depth1.in` removes `fun'` existence, L2, and Inv.  It
keeps the exact philosophically central assumptions at the represented types:
the target PP consequence `Pure(D)`, unique fundamentality, unary
Recombination, the definition of `fun'`, and the local truth tables needed by
the selected logical terms.  It is a bounded refutation probe, not an
equiconsistent encoding of the full schema stock.

The matching files whose names end in `_reified_thf.in` express the same
benchmarks in THF.  They do **not** declare the object-language operator type
as `prop > prop`.  `prop` and `op` remain opaque base types, and `app` is an
explicit curried symbol.  This uses THF's convenient higher-order syntax
without importing THF function extensionality into Goodman's object theory.
The TFF and reified-THF versions provide a refutation cross-check.  Vampire
5.0.1 proves the T6 contradiction from both encodings.  Its finite-model
builder, however, reports that it is not compatible with higher-order or
polymorphic input.  Thus the bounded PP model is searched for in TFF and should
be certified independently in Isabelle; a THF timeout on that satisfiable probe
is not evidence against the TFF model.

The current TFF model is certified in
`theories/goodman/models/finite/Bacon_PP_Vampire_Depth1_Model.thy`.  Its theorem
`v_depth1_model_certificate` proves the conjunction of every axiom in
`goodman_pp_recombination_depth1.in` from the printed three-element tables.
Build it independently with:

```sh
isabelle build -d . Higher_Order_Metaphysics_PP_Models
```

Run, for example:

```sh
vampire --mode casc --time_limit 30 vampire/goodman_t6_inv_calibration.in
vampire --mode casc --time_limit 30 vampire/goodman_t6_wi_master_inconsistent.in
vampire --mode casc --time_limit 30 vampire/goodman_pp_recombination_depth1.in
vampire --mode casc --time_limit 30 vampire/goodman_t6_inv_calibration_reified_thf.in
vampire --mode casc --intent sat --time_limit 30 \
  vampire/goodman_pp_recombination_depth1_reified_thf.in
```

The global project convention is that TPTP inputs use the `.in` extension.

## Staged L2 experiments

The `l2_staged_thf/` suite divides the proposed derivation of L2 from
\(T_0+\mathrm{PP}+\exists\mathsf{fun}'\) into independently testable
higher-order claims.  Vampire proves the algebraic bridges from collisions
on `fun'` propositions to agreement under left composition, and from each of
three proposed structural conditions to L2.  It does not prove any of those
three conditions from the represented PP background in the recorded bounded
searches.  The final combined target admits only lemmas proved in earlier
split targets.

The `l2_staged_tff/` suite tests the same three remaining conditions after
reifying unary operators into a multisorted first-order sort.  The initial
60-second, six-core runs time out in both representations.  These are
proof-search failures, not nonderivability results.  The README and results
ledger in each subdirectory record the exact dependency discipline and
outcomes.
