# Higher Order Metaphysics in Isabelle/HOL

This session is a first Isabelle/HOL scaffold for formalizing results in higher-order
metaphysics against the logical background of Andrew Bacon's *A Philosophical
Introduction to Higher-Order Logics*.

The development deliberately uses Isabelle/HOL as a metalanguage. Bacon-style
higher-order languages are represented as object languages, so object-language
identity, implication, quantification, lambda abstraction, and beta/eta principles
do not collapse into Isabelle/HOL's own equality and function space.

## Requirements and verification

The release requires Isabelle2025-2 and has no AFP or third-party theory
dependencies. From the repository root, run either:

```bash
isabelle build -D .
```

or:

```bash
./check_isabelle.sh
```

The precise division between verified theorems, conditional interfaces, and
open obligations is recorded in [`STATUS.md`](STATUS.md).

Current scope:

- object-language simple types: individuals, propositions, and arrow types;
- de Bruijn object-language terms with typed constants, application, abstraction,
  equality, negation, conjunction, disjunction, implication, higher-order universal
  quantification, and higher-order existential quantification;
- an intrinsic typing judgment over type contexts;
- renaming and substitution operations;
- starter preservation lemmas for renaming, substitution, and beta contraction;
- a Hilbert-style derivability system for the minimal higher-order logic `H`,
  including propositional classical tautologies, UI, EG, Ref, LL, beta/eta
  conversion in formula contexts, MP, Gen, and Inst;
- named object-language formulas for the Boolean identities and the Classicist
  identities from Bacon-Dorr Figures 3 and 4;
- a Classicism derivability system `C`, extending `H` with those identities and
  preserving well-typed formulahood;
- modal-logicism definitions for broad necessity, possibility, and entailment,
  plus typed modal schema terms and small `H`/`C` derivability sanity checks;
- restricted necessitation lemmas and a propositional equivalence-closure
  extension `CE` isolating the zero-ary Equivalence rule needed to move from
  provable biconditional-with-truth to boxed theoremhood;
- vector/zeta equivalence infrastructure in `Bacon_Zeta.thy`: typed iterated
  arrow types, vector application, fresh de Bruijn variables, finite context
  shifting, a freshness predicate for fresh context extensions, and a `CEV`
  derivability system with the full vector Equivalence rule and formula
  preservation;
- theorem-to-truth equivalence for `CEV`, proving that every `CEV` theorem is
  `CEV`-equivalent to object-language truth, with unrestricted `CEV`
  necessitation as a corollary;
- a standalone typed beta-eta conversion relation in `Bacon_Conversion.thy`,
  factored away from the derivability systems, with bridge lemmas showing that
  proposition-typed conversion yields biconditionals in `H`, `C`, `CE`, and
  `CEV`;
- an S4-style modal proof layer in `Bacon_S4.thy`, including local
  one-assumption `CEV` derivability, a deduction theorem for that local
  derivability relation, beta-reduction support for shifted terms, equality
  symmetry and transitivity, identity-transfer lemmas, and derived `CEV` proofs
  of the modal `K`, `T`, and `4` schemata, collected as `CEV_S4_package`;
- an initial abstract semantic layer in `Bacon_Semantics.thy`, with an
  applicative-structure locale, semantic environments, recursive interpretation
  of object terms, typed-evaluation preservation, semantic substitution and
  beta/eta conversion preservation, full soundness of `H` for the semantic
  validity predicate `valid_in_context`, and relative soundness theorems for
  `C`, `CE`, and `CEV` in progressively stronger semantic locales.
- a completeness interface in `Bacon_Completeness.thy`, defining semantic
  consequence, satisfiable assumption lists, countermodels, local soundness for
  `H_derivable` and `C_derivable`, and bridge theorems showing that the relevant
  countermodel property implies completeness.
- a canonical-theory layer in `Bacon_Canonical.thy`, now covering H/C
  Lindenbaum-Henkin extensions, canonical truth lemmas, substitutional
  term-model semantics, H/C Henkin-validity and term-model completeness
  biconditionals, explicit H/C countermodel packages, and the CE/CEV
  Henkin-closure interface.
- strengthened CE/CEV local consequence machinery for completeness: CE
  equivalence saturation, context-prefix propositional-equivalence closure,
  CEV context-equivalence Lindenbaum extensions, prefix/conservativity
  equivalences, and conditional CEV Henkin staging. The remaining named CEV
  construction obligation is `CEV_context_equiv_abstract_const_admissible`,
  i.e. fresh-constant abstraction through the full vector/zeta CEV layer.
- a Caie names layer in `Bacon_Caie.thy`: Caie's object-type correspondences
  (`e`, `t`, first-order properties, and property classifiers), an
  uninterpreted object-language counterfactual connective, the main maximal
  consistency/name/haecceity/projection vocabulary, deep-embedded Appendix C
  theorem statements 32-40, applied typing lemmas for the Caie predicates,
  verified beta-eta/H/CEV conversion bridges for `heq x`, `Q\<^sup>\<down>\<^sub>c`,
  `App (P\<^sup>\<up>\<^sub>c) R`, and `Q \<sim>\<^sub>\<down>c Z`, plus a local Caie CEV derivability
  wrapper over explicit finite assumption lists, typed assumption-package
  lemmas, derivability-level biconditional bridge eliminators
  `caie_CEV_derivable_bicond_left` / `caie_CEV_derivable_bicond_right`, and a
  named `caie_appendix_C_axiom_package` splitting the residual Caie
  assumptions into counterfactual principles and name/haecceity
  principles. The first residual target, `caie_Thm32`, is now locally derived
  from that axiom package after replacing the former beta-expanded
  down-`phae` shortcut with the component principle
  `caie_name_expanded_down_phae_components_principle`; generic CEV helpers
  assemble the boxed possible/positive-persistence/negative-persistence
  components into the old expanded `phae` principle, and the existing
  beta-eta bridge then transfers the result to official `caie_Thm32`. The
  second residual target, `caie_Thm33`, is now also locally derived from the
  package: five `phae`-up component principles are conjoined into
  `caie_Thm33_component_principles`, `beta_eta_caie_Name` expands `Name` into
  its boxed five-part definition, and `CEV_caie_Name_from_component_boxes` /
  `CEV_caie_Thm33_from_component_principles` bridge the component bundle to
  official `caie_Thm33`. The equality targets `caie_Thm34` and `caie_Thm35`
  are now package-derived from pointwise package principles:
  `caie_phae_up_down_pointwise_principle` and
  `caie_name_down_up_pointwise_principle` supply fresh-argument
  biconditionals, and CEV's new `ContextVectorEquivalence` rule closes them to
  the official higher-order equalities.  The Thm36 layer is also
  package-derived: `Bacon_Caie.thy` proves
  `CEV_contextual_unary_equivalence_admissible_holds`, proves the
  haecceity-up pointwise instance, beta-eta converts the classifier lambda
  point, derives `CEV_caie_Thm36_from_haecceity_up_extensionality`, and proves
  `caie_CEV_derivable_Thm36_from_axiom_package` /
  `caie_appendix_C_third_residual_target_from_axiom_package` from
  `caie_appendix_C_axiom_package` without a metatheoretic admissibility
  assumption.
- a finite Caie `M*` layer in `Bacon_Caie_Mstar.thy`, included in `ROOT` and
  the incremental checker. It reconstructs the two-world/two-individual table
  model, verifies `Pstar_is_Name`, `Astar_is_Name`, `bullet3_P_is_empty`,
  `Astar_nonempty`, `Mstar_name_coverage`, `name_class_is_rigid`,
  `name_class_boxed_coverage`, and `Mstar_name_plenitude_witness`, and packages
  the finite bullets as `Mstar_proposition29_core` and
  `Mstar_proposition29_finite_bullets`. It also records the abstract
  theorem-to-truth bridge for Proposition 29's first bullet:
  `nds_background_soundness` expresses the Proposition 27-style soundness
  premise, `mstar_nds_model_obligation` isolates the claim that the finite
  structure is an NDS model, and
  `Mstar_proposition29_bullet1_from_NDS_soundness` /
  `Mstar_proposition29_from_NDS_soundness` derive theorem-truth at M* and the
  full bundled Proposition 29 package conditionally from those two obligations.
  Thus the shallow M* file now makes the exact remaining paper-level dependency
  explicit, rather than assuming Proposition 27.

Build with:

```bash
isabelle build -D .
```

The portable checker runs the same session build:

```bash
./check_isabelle.sh
```

Report source and compiled PDF:

```bash
Baconian_HOL.tex
Baconian_HOL.pdf
```

The report includes the Caie local-derivability interface, its correspondence
with the Isabelle predicate `caie_CEV_derivable`, and the current dependency
sort for the Appendix C theorem statements, plus the finite `M*` checkpoint for
Caie's Proposition 29, including the rigid name-class witness.

The next natural layer is to discharge
`CEV_context_equiv_abstract_const_admissible`, most likely by proving the
renaming/substitution behavior needed for CEV theoremhood through `zeta_body`
and vector equivalence. Once that is in place, the existing countermodel
bridges give the corresponding CEV Henkin-validity and term-model completeness
theorems from the context-equivalence construction.

For the Caie branch, the current verified sort puts no full Appendix C theorem
statement in the definitional-only bucket:
`caie_appendix_C_definitional_targets = []`.  All nine statements 32-40 are in
`caie_appendix_C_principle_targets`, while the four beta-eta bridge facts are
available in arbitrary Caie contexts via
`caie_CEV_derivable_definitional_bridge_package`.  The explicit residual axiom
package now exists as `caie_appendix_C_axiom_package`; Isabelle verifies that
it is a typed assumption package and that its members are locally derivable
from it.  The specialization
`caie_appendix_C_axiom_package_definitional_bridge_package` records that those
four bridge facts are available over the axiom package itself.  The first
residual statement is now discharged as
`caie_appendix_C_first_residual_target_from_axiom_package`, deriving
`caie_Thm32` from the package rather than from the Appendix C target list, and
without assuming `caie_name_expanded_down_phae_principle` as a package member.
The package now assumes the smaller component-box principle for the down
projection and derives the expanded down-`phae` principle from it. It also
derives `caie_Thm33` from the five `phae`-up component principles and the
verified `Name` definitional bridge. The package now also derives official
`caie_Thm34` and `caie_Thm35` from pointwise up-down/down-up principles plus
CEV contextual vector equivalence, and derives official `caie_Thm36` from
`caie_haecceity_up_extensionality_principle` and the verified beta-eta
classifier bridge using the same CEV rule. It also
derives official `caie_Thm37` from the smaller
`caie_phae_up_hae_witness_principle`, using the verified upward-projection
beta-eta bridge to pass from `App (P\<^sup>\<up>\<^sub>c) (caie_heq x)` to
`caie_up_body P (caie_heq x)` before applying propositional contraposition.
Official `caie_Thm38` is now derived from
`caie_wname_dsim_surrogacy_principle`, whose left side expands down-similarity
as equality of down-projections; the proof uses `CEV_caie_dsim` to recover
Caie's displayed `Q \<sim>\<^sub>\<down>c Z` notation. It now also records the
whole-form beta-eta bridge
`beta_eta_caie_Thm38_wname_dsim_surrogacy` and derivability bridge
`caie_CEV_derivable_Thm38_wname_dsim_surrogacy_bridge`, so the final
package-level step uses `caie_CEV_derivable_bicond_right`. Official
`caie_Thm39` is derived in the same way from
`caie_hae_wname_dsim_identity_surrogacy_principle`, with
`beta_eta_caie_Thm39_hae_wname_dsim_identity_surrogacy` and
`caie_CEV_derivable_Thm39_hae_wname_dsim_identity_surrogacy_bridge` playing
the same role. Official `caie_Thm40` is derived from
`caie_wname_unique_name_down_eq_surrogacy_principle`; the Thm40 bridge uses
the beta-eta congruence helpers, now including object-biconditional
congruence, to push the down-similarity/down-equality bridge under the
existential witness and universal uniqueness contexts. Isabelle records the
package frontier as
`caie_appendix_C_axiom_package_verified_targets = [caie_Thm32, caie_Thm33,
caie_Thm34, caie_Thm35, caie_Thm36, caie_Thm37, caie_Thm38, caie_Thm39,
caie_Thm40]` and
`caie_appendix_C_axiom_package_remaining_targets = []`. The closure theorem
now uses derivability-level definitional bridge facts for the final Thm32,
Thm38, Thm39, and Thm40 conversions via `caie_CEV_derivable_bicond_right`.
The explicit source-to-target layer is recorded as
`caie_appendix_C_residual_bridge_pairs`, with
`caie_appendix_C_residual_target_from_axiom_package_using_bridge_pairs`
deriving each target from its bridge source.  The proof factors through
`caie_appendix_C_axiom_package_derives_residual_bridge_source` for the package
derivation of each source and `caie_CEV_derivable_residual_bridge_pair_imp`
for the verified bridge implication from source to target, then closes each
row by local Caie modus ponens.
`caie_appendix_C_residual_target_from_axiom_package` packages the residual
derivation layer by proving that every member of `caie_appendix_C_theorems` is
locally derivable from `caie_appendix_C_axiom_package`.
`caie_appendix_C_principle_target_from_axiom_package_using_bridges` gives the
same result over the verified principle-target bucket, and
`caie_appendix_C_axiom_package_closes_targets_from_residual_bridges` turns that
bucket-level derivation into the closure predicate.
`caie_appendix_C_axiom_package_closes_targets_from_verified` now proves
`caie_appendix_C_axiom_package_closes_targets` unconditionally. Next, the
general CEV completeness frontier remains
`CEV_context_equiv_abstract_const_admissible`.
