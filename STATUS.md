# PP Consistency Status

> **Complete Goodman-claims audit updated, 2026-07-27.**
> The controlling ledger is
> `reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md`.
> The reader-facing report is
> `reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.pdf`, with
> self-contained Forbes/Lucida source in the adjacent `.tex` file.
> The dedicated Isabelle session audits 96 principal theorem objects and
> passes with zero oracles, zero undischarged logical hypotheses, and zero
> flex-flex pairs.  T9's polymorphic cardinal results carry one ordinary
> type-sort hypothesis, reported separately.
>
> New checked results derive T9's PC injection and kind-fibre injection from
> their advertised specifications, formalize the exact fn.-60 denotational
> diagnosis in M1, and prove the displayed M5 collision calculation.  For
> M1 footnote 60, the exact-model theorem identifies the infinitary join with
> the interpretation of `Pure` and proves that PP is equivalent to its
> membership in the next pure stock.  Nonmembership is proved only under the
> additional PP-diagonal/QSS assumptions, not directly in Bacon's exact
> generic model.  The M7
> invariant-reachability equivalence is also checked.  The M5 countability argument in the
> notes is false: the world-indexed pair family is countable, just like the
> orbit.  It has been replaced by a uniform diagonal construction which, for
> every candidate `R`, produces a two-element pair outside every view of `R`,
> with only extreme proper views.  The associated invariant transposition
> fixes `R` and is nonidentity.
>
> Every determinate claim in the notes is now proved, refuted and repaired, or
> stated with the qualification on which it is true.  This is not a blanket
> verification of every sentence: T3 requires the recorded modal repair; T7b
> and the wide-Fun discussion in M4 are underspecified; the proposed general
> M5 collision argument and the fully instantiated M5 rebuilt model remain
> open.  The main PP consistency question and global semantic L2 also remain
> open.
>
> The earlier bounded-microreport Claude--Codex audit converged after four
> turns and its three precision repairs are incorporated.  A final
> adversarial re-audit of the newly completed M1, M5, and T9 results and of the
> Goodman-facing report is pending.

> **Eight-round recurrence-module debate complete; absorption remains open,
> 2026-07-27.**
> Claude and Codex ran eight full adversarial rounds, swapping the positive
> and negative roles after every turn.  No typed cone-natural absorbing
> enumerator was constructed, and no generated reflecting map, signature
> escape, or unconditional contradiction was found.
>
> The strongest surviving positive proposal is a countable
> recurrence-module stock.  An anti-recurrent self-fresh proposition `p`
> supplies a recurrence separator `Rec_p`; symmetric-difference partners
> collapse the ordinary uniqueness operator; modal composites of `Rec_p`
> largely collapse; and failures of a no-preimage condition are retained in
> the countable family `{Rec_p o F | F in S}` rather than forbidden.
> Equivariant bijections transport recurrence signatures, so the construction
> need not classify every generated reversible as identity or complement.
>
> The first load-bearing construction target is
> `pp_b_countable_recurrence_module_closed_extension`, preceded by:
>
> ```text
> pp_b_preimage_recurrence_compose
> pp_b_recurrence_transport_bijection
> pp_b_separator_transport_surjection
> ```
>
> The fastest negative test is a generated signature escape: find one closed
> logical unary operator `F` for which `Rec_p o F` is globally nonconstant
> but agrees with `Kbot` at `p`.  Adding that generated operator would
> immediately destroy separation at `p`.  No such operator was found in the
> debate.
>
> The debate also produced several paper-level lemmas that are not yet
> machine-checked: anti-recurrent self-fresh generic separators; recurrence
> modal-collapse identities; `M_E = not o Rec_p` under the separator recipe;
> constancy of the material-truth quotient diagonal on recurrence support;
> recurrence transport by equivariant bijections; and separator transport by
> surjective stock members.  These must not be reported as Isabelle theorems
> until formalized.
>
> The full transcript is
> `reports/CONSENSUS_ABSORPTION_ROLESWAP_2026-07-27.md`; the durable Claude
> checkpoint ledger is the adjacent `..._PROGRESS_...` file.  The final
> credence that an absorbing enumerator exists was approximately
> `0.40--0.43`: modestly improved, but still below even odds.
>
> **Base and vector-Equivalence soundness discharged; the fixed point is now
> the sole model-existence obligation, 2026-07-27.**
> `zf_model/Bacon_PP_ZF_Tree_CEV_Soundness.thy` gives a direct semantic proof
> of every CEV base axiom and every vector-Equivalence instance in the
> restricted tree Henkin model.  The development proves evaluator
> extensionality, shift and substitution, beta and eta compatibility, all
> Boolean and quantifier identities, Leibniz identity, modal C and CE, and
> the full typed vector-Equivalence schema.  Consequently
> `pp_t_base_sound` and `pp_t_zeta_sound` are theorems, not remaining model
> assumptions.
>
> For any typed cone-natural `E` satisfying the absorption equation,
> `pp_t_term_basis_fixed_point_answers_Goodman` now proves Goodman's
> consistency question directly.  The same hypothesis also yields the
> closed-form T6 alternative
>
> ```text
> not gvalid [] pp_L2 or not gvalid [] pp_TU.
> ```
>
> `pp_t_term_basis_fixed_point_has_L2_or_TU_counterworld` strengthens this
> to an actual Boolean-tree world at which one of those two closed
> denotations is false.
>
> Current analysis does not license selecting one disjunct: that would
> require either global semantic L2 for the generated stock or a
> classification of its pure reversible cone-natural operators.
>
> `zf_model/Bacon_PP_ZF_Tree_Range_Term_Basis.thy` now isolates the remaining
> construction problem exactly.  The inclusion
>
> ```text
> {E n | n in Nat} subset pp_t_enumerator_basis E U
> ```
>
> is automatic, since every `E n` is denoted by an application expression.
> Thus absorption is equivalent to expression surjectivity: every generated
> unary basis expression must equal `E n` for some natural index.  Moreover,
> any such fixed point has no generated `Ind -> Prop` expression that is
> `E`-reflecting at the root, and hence no generated index-separating
> expression.  This is the strongest presently checked diagonal restriction,
> not a construction or an unconditional impossibility theorem.
>
> **Repaired central stock reduced to the same self-reference fixed point,
> 2026-07-27.**
> `zf_model/Bacon_PP_ZF_Repaired_Central_Stock.thy` proves that zeroary
> Exhaustion is globally valid in every cone-natural basis model.  The key
> semantic lemma is that a pure proposition true at a world is locally
> equivalent to truth: its basis representative is cone-natural and hence a
> globally constant proposition.
>
> The theory names the exact self-reference forced by PP as
> `pp_t_self_applicative_pure`: the unary-stock classifier belongs, at the
> root, to the next-type pure stock.  The theorem
> `pp_t_basis_repaired_central_gvalid_iff` proves that this one membership
> fact is equivalent to global validity of the entire repaired stock
> `pp_recombination_zeroary_exhaustion_axioms`.
>
> For the explicit `Ind`-indexed term basis,
> `pp_t_term_basis_repaired_central_gvalid_from_fixed_point` proves that the
> existing absorption equation
>
> ```text
> pp_t_enumerator_basis E U = {E n | n in Nat}
> ```
>
> suffices for global validity of the repaired stock.  Thus zeroary
> Exhaustion adds no new model-construction burden.
>
> Finally, `repaired_central_stock_forces_L2_or_TU_failure` and
> `repaired_central_stock_has_explicit_L2_or_TU_failure` formalize T6's exact
> semantic contrapositive: any repaired central model satisfying base CEV
> soundness and vector-Equivalence soundness must fail global L2 or global
> TU.  The term-basis specialization combines this directly with the
> absorption equation.
>
> This checkpoint has been superseded in one respect by the entry above:
> `base_sound` and `zeta_sound` are now proved.  The absorption fixed point
> remains open.
>
> **The stabilizer-orbit relation is lifted to the actual tree action,
> 2026-07-27.**
> `zf_model/Bacon_PP_ZF_Tree_Stabilizer_Orbit.thy` defines actual
> precomposition `G \<circ> \<psi>` on the HOL-ZF proposition domain and proves
> that its raw Boolean-tree operator is exactly
> `pp_b_operator_of G \<circ> pp_b_operator_of \<psi>`.
> The closed logical term `pp_qd_stabilizer_relation` expresses
> `R_stab(q,F,G) := \<exists>\<psi>. (Bij \<psi> \<and> F = G \<circ> \<psi> \<and> \<psi> q = q)`.
> It is typed, generated, and its denotation is proved equal to the
> world-relative PER formulation.
>
> At the root, `pp_t_qd_world_bijective_root_iff` identifies the internal
> `Bij` clause exactly with literal bijectivity of `pp_b_operator_of \<psi>`.
> Hence each root witness is an ambient view-respecting bijection, induces a
> bijection on every cone profile, and has a view-respecting raw inverse.
> `pp_t_qd_stabilizer_orbit_root_iff_ambient` identifies the complete root
> relation with the intended ambient stabilizer action.
>
> `pp_t_qd_stabilizer_orbit_truth_congruent` proves truth congruence at every
> world.  `pp_t_qd_stabilizing_precomposition_relation_holds` proves that
> every stabilizing-precomposition collider is automatically related, so
> this entire collider species cannot violate the `D_R` guard.
> Finally, `pp_t_qd_stabilizer_relation_in_generated_stock` and
> `pp_t_qd_stabilizer_diagonal_in_generated_stock` put both `R_stab` and its
> quotient diagonal in the repaired central stock.
>
> The result does not establish tag homogeneity.  Stabilizer orbits are not
> known to exhaust all representations of a diagonal tag.  The exact next
> negative target is therefore a representation-completeness theorem modulo
> `R_stab`, or an explicit non-orbit representation refuting it.  The
> positive absorption fixed-point program remains open in parallel.
>
> **Closed object-language quotient diagonal and generated-stock closure
> checked, 2026-07-27.**
> `zf_model/Bacon_PP_ZF_Tree_Quotient_Diagonal_Builder.thy` defines the
> constant-free closed term `pp_qd_builder` of type
> `(Ind -> U) -> (Prop -> Prop -> Prop) ->
> (Prop -> U -> U -> Prop) -> U`, where `U = Prop -> Prop`.
> `pp_qd_builder_typed` and `pp_qd_builder_logical` check its formation and
> logical vocabulary.  `pp_t_qd_builder_apply_holds` proves pointwise that
> its denotation is exactly the PER-sensitive object-language `D_R` schema:
> equality is world-relative object identity and `R q F G` is truth of the
> relation proposition at the evaluation world.
>
> The closure result is available at both relevant levels.
> `pp_t_qd_den_in_enumerator_basis` puts `D_R(E,H,R)` in the raw applicative
> term basis when `H` and `R` are raw generated expressions.
> `pp_t_qd_den_in_generated_stock`, inside
> `pp_t_cone_natural_enumerator`, puts it in the repaired equivalence-saturated
> central stock whenever `H` and `R` are in that stock.  Thus no additional
> closure principle is needed to generate this diagonal.  What remains open
> is the mathematical premise needed for contradiction: a generated
> root-truth-congruent `R` and tag constructor `H` forcing homogeneity at an
> absorbed index.  The next direct test is the actual tree-model
> stabilizer-orbit action, not another encoding of `D_R`.
>
> **Ambient inverse and root-semantic quotient diagonal formalized;
> first tag tests are negative, 2026-07-27.**
> `zf_model/Bacon_PP_ZF_Tree_Ambient_Inverse.thy` now machine-checks the
> Boolean cone profile
> `X_w \<cong> 2 \<times> X_{w@[False]} \<times> X_{w@[True]}`, proves that every
> view-respecting ambient bijection induces a bijection on every cone, and
> proves that its inverse is again view-respecting.  The closed
> object-language inverse builder
> `\<lambda>\<psi> q. \<exists>p. (\<psi>p = q \<and> p)` is typed, logical, in the
> unary domain, and is proved pointwise correct against the raw inverse.
>
> `zf_model/Bacon_PP_ZF_Tree_Quotient_Diagonal.thy` formalizes the
> root-semantic `D_R` schema, separator representations, root-truth
> congruence, and tag homogeneity.  Its central theorem,
> `pp_qd_absorption_forces_tag_heterogeneity`, proves that if `D_R` is
> absorbed by `E`, then no separator tag at its absorbed index is
> `R`-homogeneous.  Isabelle exposed an essential premise: the argument
> needs root-truth congruence of `R`; homogeneity alone is insufficient.
>
> Two concrete Boolean tests are checked.  Singleton finite-observational
> agreement (with the tag itself observed) and stabilizer-orbit equivalence
> are both root-truth-congruent.  Nevertheless, the same separator tag has
> two representations separated by each relation, so neither relation is
> tag-homogeneous even in the two-point model.  Thus these natural relations
> do not close the contradiction route by themselves.
>
> The next step is to internalize the root-semantic `D_R` schema as a closed
> object-language builder over `E`, `H`, and `R`, then connect its generated
> denotation to the repaired central stock.  In parallel, the
> stabilizer-orbit test should be lifted from the two-point diagnostic to the
> actual tree-model operator action.  The direct consistency question remains
> open.

> **Absorption fixed-point consensus complete; mathematical question remains
> open, 2026-07-26.**
> An eight-round, sixteen-turn Claude--Codex debate attacked the exact
> absorption equation on both the homogeneous/generic and invariant/diagonal
> sides.  The participants reached consensus on the frontier, not on a
> construction or refutation.  No absorbing enumerator, uniform invariant, or
> unconditional generated escape term is known.
>
> The jointly verified metatheoretic advances are: a germ normal form for
> cone-natural unary operators; infinite-fiber reindexing canonicity and an
> inflationary set-level closure operator; cardinal-slack trivialization of
> unrestricted non-range meets and joins; a quotient-guarded diagonal schema
> `D_R` forcing heterogeneous separator-tag representations under absorption;
> two-sided separator transport and a group action on tag representations; and
> an ambient inverse theorem for every respecting raw bijection.  None of these
> results was machine-checked at the time of the debate; the ambient inverse
> and root-semantic `D_R` portions are now checked as recorded above.
>
> The next formal tranche is agreed and ordered:
>
> 1. formalize the ambient inverse theorem and the `D_R` schema;
> 2. test concrete `(H, R, p*)` instances, beginning with finite observational
>    relations and the stabilizer-orbit relation, for tag homogeneity or a
>    forced heterogeneous representation; and
> 3. develop the competing promise-bearing stable-fusion construction, with
>    quotient- and uniqueness-guarded terms as its primary falsification
>    class.
>
> The complete transcript is
> `reports/CONSENSUS_ABSORPTION_FIXED_POINT_2026-07-26.md`; its durable
> checkpoint ledger is the adjacent `..._PROGRESS_...` file.  The last pushed
> checked source snapshot is commit `cf0976e`.

> **`Ind`-enumerator construction reduced to one exact absorption fixed
> point, 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Range_Diagonal.thy` proves that root PER
> equivalence is literal equality at every object type.  Therefore root
> range-completeness is equivalent to all-world range-completeness, and both
> are equivalent to the raw set identity between the unary basis and the
> value set of `E`.  This corrects the earlier claim below that future-world
> lifting was an additional open obligation.
>
> The same theory machine-checks the strongest typed diagonal obstruction:
> a range-complete basis cannot contain an
> `E`-reflecting map `P : Ind \<rightarrow>\<^sub>o Prop`.  This is conditional,
> not an impossibility theorem.  Cone-naturality collapses every basis
> proposition to truth or falsity, so stock-internal index codes are only
> two-valued and the Cantor bridge is not generated.  The abstract theorem
> `pp_b_generic_separator_for_countable_stock` separately constructs an
> external separator for any countable cone-equivariant unary stock.
>
> `zf_model/Bacon_PP_ZF_Tree_Range_Term_Basis.thy` defines the explicit
> applicative basis generated from all closed logical denotations, all of
> `Nat` at `Ind`, and one distinguished cone-natural enumerator `E`.  The
> locale `pp_t_cone_natural_enumerator` verifies all five
> `pp_t_stock_basis` obligations and `E`-membership.  The checked theorem
> `pp_t_term_basis_range_complete_iff_fixed_point` leaves exactly:
>
> ```isabelle
> pp_t_enumerator_basis E pp_t_unary_type =
>   (\<lambda>n. E \<acute> n) ` {n. Elem n (pp_t_domain Ind)}.
> ```
>
> `pp_t_term_basis_self_classifies_from_fixed_point` discharges the
> remaining PP classifier condition from that equation.  No construction
> or refutation of the equation is claimed.  It is now the sole mathematical
> frontier; naive stage closure and the standard typed Cantor diagonal do
> not decide it.  The focused ZF-model session passes.  See
> `reports/IND_ENUMERATOR_FRONTIER_2026-07-26.md` and Claude's independent
> `reports/CLAUDE_IND_ENUMERATOR_CONSULT_2026-07-26.md`.

> **Seeded-basis model theorem and `Ind`-range criterion checked,
> 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Seeded_Stock.thy` packages the semantic
> construction over an arbitrary `pp_t_stock_basis`.  For every such basis it
> selects a root generic seed, transports it by cone lift, interprets `Pure`
> by the basis saturation and `Fun` by the local identity class of the
> transported seed, and proves global validity of the complete Recombination
> background: logical purity, application closure, unique proposition
> fundamentality, no other fundamentals, and zeroary and unary Recombination.
>
> The exact residual condition is now basis-parametric.
> `pp_t_seeded_recombination_PP_gvalid_iff_root` and its basis specialization
> `pp_t_basis_recombination_PP_gvalid_iff_root` prove that the full central
> stock is globally valid iff the unary-stock classifier belongs to the
> next-type basis stock at the root.  This is the sufficient-basis theorem
> requested by the classifier-frontier audit.
>
> `zf_model/Bacon_PP_ZF_Tree_Range_Classifier.thy` then verifies the live
> simultaneous route.  The closed, logical, well-typed term
> `pp_range_classifier_builder`, applied to any typed
> `E : Ind \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)`, is
> PER-equivalent to the classifier of the world-relative equivalence
> saturation of `range E`
> (`pp_t_range_classifier_builder_correct`).  The theorem
> `pp_t_range_complete_basis_self_classifies` proves that a basis containing
> such an `E` self-classifies whenever its unary stock agrees with that
> saturated range **at every world**.  The later theorem
> `pp_t_range_complete_all_worlds_iff_root` now proves that root
> range-completeness already entails this all-world hypothesis, because root
> PER equivalence is literal equality.
>
> Thus the positive problem has been reduced to one precise construction:
> exhibit a countable cone-natural application-closed basis, containing the
> logical denotations and a typed enumerator `E`, whose unary saturation is
> the saturated range of `E` at every world.  Alternatively, refute the
> existence of such an enumerator.  No existence or impossibility theorem is
> claimed yet.
>
> Both the focused ZF-model session and the full project build pass.  The new
> theories contain no `sorry` or `oops`, and `git diff --check` is clean.

> **Countable cone-natural basis abstraction checked, 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Basis_Stock.thy` defines
> `pp_t_basis_stock D`, the local-equivalence saturation of a typed
> type-indexed basis `D`.  The locale `pp_t_stock_basis` assumes exactly the
> current construction data: typedness, countability, cone naturality,
> inclusion of all closed logical denotations, and application closure up to
> root equivalence.
>
> Isabelle now proves that every such saturation is admissible and persistent,
> contains every closed logical denotation, is closed under application, and
> transports exactly through every Boolean-tree cone.  Its classifier is
> consequently cone-natural.
>
> The generic-seed theorem is generalized beyond the exact logical stock.
> `pp_t_generic_seed_recombines_basis_stock_at_root` constructs a typed root
> seed for the unary saturation of every countable cone-natural basis;
> `pp_t_basis_root_recombination_transports_to_cone` transports it; and
> `pp_t_basis_generic_seed_at_every_world` supplies one root seed whose cone
> lifts satisfy unary Recombination at their corresponding worlds.
>
> The abstraction is not merely sufficient-looking:
> `ClosedLogicalBasis` instantiates every locale assumption, and
> `pp_t_basis_stock_closed_logical_basis` proves that its saturation is
> extensionally identical to the previously constructed exact
> closed-logical stock.  The focused ZF-model session and full project build
> pass with no proof escapes.
>
> **Next exact route:** build the seeded internal interpretation uniformly
> over `pp_t_stock_basis`, prove the entire Recombination background globally
> valid, and derive `pp_t_basis_recombination_PP_gvalid_iff_root`.  Only after
> that theorem should the `D1` stabilization and `Ind`-indexed
> range-completeness instantiations be attempted.

> **Generic-seed background model and exact PP root reduction checked,
> 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Generic_Seed.thy` now carries the generic root
> seed through cone lift to every world, interprets `Fun_Prop` as the local
> identity class of that transported seed, and proves global unique
> fundamentality, no fundamentals at every non-proposition type, all
> closed-logical purity instances, every application-closure instance, and
> both zeroary and unary Recombination.  Hence
> `pp_t_generic_recombination_background_gvalid` validates the complete
> Recombination background in one concrete HOL-ZF Henkin interpretation.
>
> The remaining PP clause is isolated exactly.
> `pp_t_generic_target_PP_holds_iff` identifies its truth with membership of
> the exact unary-stock classifier in the next-type exact closed-logical
> stock.  `pp_t_generic_recombination_PP_gvalid_iff` makes that condition
> equivalent to global validity of the whole central stock.
> `pp_t_closed_logical_stock_persistent` and
> `pp_t_closed_logical_stock_all_worlds_iff_root` reduce the all-worlds
> condition to one root fact, and
> `pp_t_generic_recombination_PP_gvalid_iff_root` states the final exact
> boundary.
>
> Supporting cone results are also checked: every closed logical proposition
> denotation is root-truth constant; cone-invariant elements have
> world-independent equivalence classes; closed-logical stock membership
> transports through the cone relation; and the stock classifier is itself
> cone-natural.  None of these facts proves that the classifier belongs to
> the stock.  Thus the model validates the entire background but is not yet a
> model of PP.
>
> **Next exact route:** define a countable cone-natural typed basis and its
> local-equivalence saturation, prove a sufficient-basis model theorem, then
> instantiate either the one-step basis generated by the old classifier or an
> `Ind`-indexed range-complete basis with all of `Nat` explicitly included at
> type `Ind`.  The latter route can define its range classifier internally,
> but root range-completeness must first be lifted to every world and the
> logical range-classifier builder must itself belong to the stock.  Merely
> adjoining the old classifier is not enough: application closure changes the
> unary stock, so PP asks for the new classifier.  Unary stabilization is a
> sufficient discharge condition, not something presently proved.
> Claude/Codex independently audited this frontier in
> `reports/CONSENSUS_PP_CLASSIFIER_FRONTIER_2026-07-26.md`.  They agreed on
> the checked results and the “sufficient basis, then concrete
> instantiations” strategy; the runner recorded no formal consensus because
> the first proposed range-completeness corollary omitted the two premises
> just stated.

> **All-type cone gluing and unconditional exact-stock Recombination
> checked, 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Generic_Seed.thy` constructs, for every countable
> stock of cone-equivariant proposition operators, one proposition whose
> reserved Boolean cones diagonalize against every nonuniversal operator.
> The exact stock of denotations of closed, typed, constant-free unary terms
> is proved countable.  The denotations of `λq.¬□q`, `λq.◇□q`, and
> `λq.(◇□q ∨ ◇□¬q)` are proved cone-equivariant, and one generic seed
> satisfies the Recombination implication for all three simultaneously.
>
> The all-type support/gluing obligation is now discharged.  The proof uses
> `pp_t_sibling_component`, a type-sensitive two-branch amalgamation relation:
> it is equality at `Ind`, universal at `Prop`, and closed under higher-order
> application.  `pp_t_sibling_component_iff_logical` verifies that the
> explicit recursive sibling merge realizes the corresponding logical
> relation.  `pp_t_support_rel` then tracks local equality inside the support
> cone, root equality above it, and sibling-component equality off it.
>
> `pp_t_cone_transform_invariant_all` proves simultaneously at every object
> type that `pp_t_cone_restrict` and `pp_t_cone_extend` lie in their typed
> domains and preserve the appropriate support relation.  The canonical
> witness theorem `pp_t_cone_canonical_invariant_all` proves that restriction
> and supported extension realize `pp_t_cone_rel`; consequently
> `pp_t_cone_left_total_all`, `pp_t_cone_right_total_all`, and
> `pp_t_cone_compatible_all` hold at every type and cone.
>
> The formerly conditional locale `pp_t_cone_totality` is now instantiated as
> `UnconditionalCone`.  The final theorem
> `pp_t_generic_seed_recombines_exact_closed_logical_stock` gives, without
> semantic assumptions, a typed proposition that satisfies root unary
> Recombination for the full exact closed-logical stock.
>
> **Next exact route:** transport this root seed to every world by cone lift,
> interpret `Fun_Prop` as the local identity class of the transported seed,
> prove global unique fundamentality and all closed-logical Recombination
> instances, and only then attack PP for that repaired central stock.

> **Full closed-logical stock constructed; moving-seed tree model refuted,
> 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Logical_Stock.thy` defines
> `pp_t_closed_logical_stock`, the local-identity closure of the denotations
> of all closed, well-typed, constant-free object terms.  It proves that this
> stock is admissible, contains every evaluation of every such term, is least
> among admissible stocks with that property, and is closed under application.
> The object-language logical-purity instances and all application-closure
> instances are globally valid under the resulting `Pure` interpretation.
>
> The enlarged stock exposes a decisive new Recombination obstruction.  The
> closed logical operator
> `λq.(◇□q ∨ ◇□¬q)` says that its argument eventually settles to truth or
> falsity.  The moving fundamental seed settles on every future branch, so
> this operator applies necessarily to the seed.  The proposition whose
> truth alternates with word length never settles on any cone, so the operator
> does not apply to every proposition.  Isabelle proves both the semantic
> no-go `pp_t_closed_logical_stock_not_recombines` and the failure of
> Goodman's actual object-language formula,
> `pp_t_closed_logical_unary_recombination_not_gvalid`.
>
> Thus the Boolean-tree domains, structural evaluator, and Henkin-model
> instantiation remain usable, but the true-child-cone interpretation of the
> unique fundamental proposition cannot model the central stock.  The earlier
> two-operator Recombination result remains correct but was not exhaustive.
> PP was not tested for this stock because unary Recombination already fails.
> **Next exact route:** replace the moving seed by a logically generic
> proposition whose future copies realize every proposition behavior relevant
> to closed logical operators, or prove that no such seed can coexist with
> unique fundamentality on this frame.

> **Branching HOL-ZF model scaffold instantiated; first logical
> Recombination obstruction passed, 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Tree_Frame.thy` is the live positive construction.
> Its worlds are finite Boolean words ordered by prefix.  A proved bijection
> with `Nat` lets propositions remain the preconstructed set
> `Power Nat`, without unused or duplicated world coordinates.
>
> The theory rebuilds every typed domain and the world-indexed logical
> relation.  It proves application closure, persistence, nonemptiness, and
> reflexivity, symmetry, and transitivity at every object type.
> `pp_t_eval_fundamental` simultaneously proves type preservation and
> relational invariance for the terminating structural evaluator, including
> lambda abstraction and both higher-order quantifiers.
> `DefaultTreeConstants.TreeHenkin` is consequently a concrete
> `henkin_action_model`.
>
> The moving seed at `w` is the proposition true exactly on the subtree rooted
> at `w@[True]`.  `pp_t_moving_internal_parameters` interprets `Fun` as its
> local identity class.  The object-language theorems
> `pp_t_moving_unique_fundamental_gvalid` and
> `pp_t_moving_no_fundamentals_gvalid` prove global unique fundamentality at
> `Prop` and every no-other-fundamentals instance.
>
> The first logical-purity stress test is positive.  The evaluator's exact
> denotations of `λq.¬□q` and `λq.◇□q` are respectively
> `pp_t_not_box_classifier` and `pp_t_diamond_box_classifier`.
> Their local identity classes form the admissible fragment
> `pp_t_obstruction_pair_pure`; the two containment lemmas connect that
> fragment to the actual closed logical terms.
> `pp_t_moving_obstruction_pair_recombines` proves unary Recombination for
> this entire fragment at every world.  The true child falsifies the
> `□¬□p` antecedent, and the incomparable false child falsifies the
> `□◇□p` antecedent.
>
> This is not yet a model of the central stock.  **Next obligation:** enlarge
> the purity interpretation from these two closed logical denotations to all
> closed logical denotations and application closure, prove global unary
> Recombination for the enlarged stock, and then tackle PP for the stock's own
> classifier.  Base CEV soundness and vector-Equivalence remain downstream.

> **Extensional full frame excluded; hyperintensional replacement opened,
> 2026-07-26.**
> The full-frame pivot solved the evaluator/domain circularity but exposed a
> second obstruction.  `pp_zf_extensional_identity_blocks_recombination` proves
> that if object identity is interpreted as metalanguage equality, the two
> closed logical operators `λq.(q=⊤)` and `λq.¬(q=⊤)` defeat unary
> Recombination for every proposed fundamental proposition.
> `pp_zf_logical_purity_blocks_recombination` packages the exact consequence:
> any purity interpretation containing all closed logical operators fails the
> Recombination kernel.  Thus no choice of the parameter `Pure` can repair the
> extensional HOL-ZF frame.  This is a limitation of Claude's initial
> full-frame recommendation, not evidence that the central stock itself is
> inconsistent.
>
> `zf_model/Bacon_PP_ZF_Hyper_Frame.thy` implements the required refinement
> without returning to closure evaluation.  Propositions remain preconstructed
> subsets of `Nat`, but object identity is the world-indexed relation
> `pp_h_eqv`.  At proposition type, `P ≈_w Q` means agreement at every
> future world `v≥w`; at arrow types it is the induced logical relation.
> Arrow domains are genuine HOL-ZF functions restricted to those respecting
> this relation at every world.
>
> The new theory proves typed application, persistence of equivalence,
> nonemptiness of every domain, and reflexivity, symmetry, and transitivity at
> every object type.  It also proves
> `pp_h_prop_eqv_truth_iff`: identity with truth at `w` is exactly truth
> throughout the tail above `w`.  Distinctness can therefore disappear later,
> as required; it is no longer illicitly rigid.
>
> `pp_h_eval` now gives the terminating structural evaluator over these
> domains.  Its equality clause denotes the proposition
> `{w | pp_h_eqv σ w x y}`; `pp_h_eval_Eq_holds` proves the exact world-level
> biconditional.  The clauses for negation, conjunction, disjunction,
> implication, and both quantifiers are also proved.  The next construction
> target is the combined typing/relational fundamental lemma for `pp_h_eval`,
> needed to show that lambda denotations belong to the restricted arrow
> domains, followed by a new `henkin_action_model` interpretation.

> **Preconstructed HOL-ZF full frame instantiated, 2026-07-26.**
> `zf_model/Bacon_PP_ZF_Full_Frame.thy` implements Claude's recommended
> semantic pivot in a separate Isabelle session,
> `Higher_Order_Metaphysics_PP_ZF_Model`.  The object domains are fixed before
> denotation: `Ind` is `Nat`, `Prop` is `Power Nat`, and
> `σ→τ` is the genuine HOL-ZF function set `Fun Dσ Dτ`.
> `pp_zf_default_in_domain` and `pp_zf_domain_nonempty` prove every domain
> inhabited; `pp_zf_app_closed`, `pp_zf_lambda_closed`, `pp_zf_beta`, and
> `pp_zf_eta` prove the full application/abstraction interface.  The equality
> PER has exactly these domains as its diagonal, and
> `pp_zf_per_domain_nonempty` proves all PER domains nonempty.
>
> `pp_zf_eval` is structural recursion on the object term.  Quantifiers range
> over the already constructed domains, so no closure evaluation or semantic
> self-call occurs.  The locale `pp_zf_constants` proves type preservation and
> renaming/shift, then instantiates `henkin_action_model` as the sublocale
> `ZFHenkin`.  `DefaultZFConstants.ZFHenkin` is a concrete nonvacuous instance.
>
> The theory also implements Claude's internal-relation recommendation as a
> negative-control candidate.
> `pp_zf_internal_constants Pure` interprets every `Pure_σ` as the
> characteristic function of the exposed relation `Pure σ`, and interprets
> every `Fun_σ` as the characteristic function of
> `pp_zf_fundamental σ`.  The latter selects exactly `Empty` at proposition
> type and nothing at every other type.  The extensional-identity theorem above
> shows that this candidate cannot validate the central stock, regardless of
> the choice of `Pure`; it is retained as a checked negative control.
>
> This is a **relative** construction: `HOL-ZF` axiomatizes a ZFC universe as
> an HOL type.  Nothing in the project presents it as a pure-HOL consistency
> certificate.

> **Closure-evaluator route closed, 2026-07-26.**
> `frontier/Bacon_PP_Central_Model_Obligations.thy` now proves the typed
> quantifier-cycle witness
> `F = λa. ∀P^(Ind→Prop). P a` and proves that the corresponding closure is
> self-related at `Ind→Prop` for every application operation that returns
> proposition-tagged results there.  Hence the closure lies in the PER domain
> traversed while evaluating `F a`; the instance `P := F` returns the identical
> application call.  This defeats every well-founded closure evaluator on the
> proposed carrier.  STLC strong normalization is irrelevant because the loop
> is caused by semantic quantifier instantiation, not beta reduction.
>
> Independently, the quantifier range would be the diagonal of
> `pp_uval_per app`, while `app` is the function being defined.  This
> dependence is nonmonotone, so an elementary least-fixed-point repair is not
> available.  `henkin_action_model` is also too weak by itself for the promised
> endpoint: it has no semantic clauses for constants, application, abstraction,
> equality, conjunction, or disjunction; base CEV and zeta soundness remain
> separate obligations in `pp_central_stock_model`.
>
> The honest next move was a preconstructed typed-domain model with genuine
> function data at arrow types, so domains and application exist before term
> interpretation.  The HOL-ZF route has now been implemented, with its
> additional set-theoretic assumptions explicit in the new session.  Claude
> independently returned the same
> verdict in `reports/CLAUDE_CLOSURE_EVALUATOR_CONSULT_2026-07-26.md`.
> `isabelle build -D . Higher_Order_Metaphysics_PP_Frontier` is clean.

> **Direct central-stock model program opened, 2026-07-26.**
> `frontier/Bacon_PP_Central_Model_Obligations.thy` now fixes the exact
> positive certificate as the locale `pp_central_stock_model`.  An
> interpretation must discharge the denotable Henkin clauses, global soundness
> of base CEV and vector Equivalence, and
> `gvalid_set pp_recombination_PP_axioms`.  The theorem
> `central_stock_answers_Goodman` then yields the positive answer to the
> consistency question.  QSS failure and the fate of `fun′` are kept separate
> as post-settlement diagnostics.
>
> The same theory proves a generic semantic exclusion theorem for every
> CEV+-inconsistent extension and specializes it to all four audited T6 stocks.
> It also proves the orbit-classifier negative control:
> `pp_orbit_classifier_falsifies_recombination` and
> `pp_all_invariant_operator_indices_fail_recombination`.  Thus a unary purity stock
> broad enough to contain the classifier of the fundamental proposition's
> orbit cannot model Recombination.
>
> The unbounded representation is now fixed to one recursive universal carrier,
> `pp_uval`, containing propositions as word-sets and higher values as typed
> closure codes.  `pp_uval_per` defines the type-indexed PER by structural
> recursion on every object type for an arbitrary application operation;
> symmetry, transitivity, tag soundness, and application compatibility are
> machine-proved.  `DefaultClosurePER` gives a concrete nonempty
> interpretation, showing that the all-type PER interface itself is
> consistent.  It is deliberately not the term model.  The closure-evaluator
> block above supersedes the originally stated next obligation.  The central
> settlement locale remains the target, but it must now be instantiated from
> preconstructed domains.
> `isabelle build -D . Higher_Order_Metaphysics_PP_Frontier` is clean.

> **Recombination--QSS repair, 2026-07-26.**
> `frontier/Bacon_PP_QSS_Recombination_Bridge.thy` now isolates and proves
> the strongest result obtained by Bacon's unary Recombination step alone.
> From pure unary operators `X,Y`, a fundamental `r`, and `Xr=Yr`,
> `CEV_QSS_modal_core_from_recombination` derives both
> `∀q(Xq=Yq)` and `∀q□(Xq=Yq)`.  It deliberately does **not** derive
> `□∀q(Xq=Yq)`: moving the box across the universal closure is the missing
> zeroary step in the printed QSS argument.
>
> The repaired central stock is
> `pp_recombination_zeroary_exhaustion_axioms`, namely the original
> Recombination/PP background plus zeroary Exhaustion.
> `CEV_QSS_from_recombination_with_zeroary_exhaustion` proves QSS over this
> stock in every ambient context.  Purity closure first makes the
> pointwise-identity sentence pure; zeroary Exhaustion then yields its
> necessity; derived unary Modalized Functionality yields `X=Y`.
> `CEV_fun_prime_from_contextual_QSS` proves `Fun(p) → fun′(p)`, and
> `CEV_exists_fun_prime_from_QSS_and_unique_fundamentality` eliminates the
> unique-fundamental existential to prove `∃p fun′(p)`.  Thus
> `CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion` derives,
> rather than assumes, the central T6 existence premise.
>
> The four T6 routes have been translated to this repaired central stock:
> `CEV_Goodman_T6_Inv_repaired_central_stock`,
> `CEV_Goodman_T6_TU_repaired_central_stock`,
> `CEV_Goodman_T6_WI_repaired_central_stock`, and
> `CEV_Goodman_T6_RS_repaired_central_stock` all derive `ObjFalse`.
> The Inv/TU/WI translations replace their explicit `∃fun′` axiom with the
> proved bridge; RS already supplies its own route and is monotone over the
> repaired stock.  A clean whole-project Isabelle build passes.  A separate
> theorem-object audit of all nine exported bridge/T6 theorems reports no
> oracles, hypotheses, flex-flex pairs, or sort hypotheses; the new theory
> contains no proof escape.

> **Current theorem-verification tranche, 2026-07-25.** Goodman T2a--T2d are
> machine-proved.  `frontier/Bacon_PP_Goodman_Fun_Prime_Closure.thy` proves
> that `fun′(p)` is preserved by every pure reversible operator, that negation
> belongs to that group, and hence that `fun′(p) → fun′(¬p)`.
> `frontier/Bacon_PP_Goodman_Fun_Prime_Nontriviality.thy` proves
> `¬fun′(⊤)`, `¬fun′(⊥)`, and, for any typed `p`,
> `fun′(p) → (p ≠ ⊤ ∧ p ≠ ⊥ ∧ p ≠ ¬p)`.  It also proves the last
> inequality already in bare CEV.  Claude Opus 5 independently clean-built
> and adversarially audited both developments; the T2b audit additionally
> machine-checked that its two refutations need only the purity of `id`,
> `K⊤`, and `K⊥`, so neither PP nor application closure is used there.
> `frontier/Bacon_PP_Goodman_Fun_Prime_Attainment.thy` proves both the
> parameter and exact object-language universal forms of T2c:
> `fun′(r) → ∀p(Pure(p) → ◇(r=p))`.  The proof uses the inequality operator
> `λq.¬(q=p)` and the constant-truth operator to diagonalize against
> `fun′(r)`.  Claude Opus 5 independently clean-built and adversarially
> audited the theory, inspected the exported theorem objects, recomputed every
> de Bruijn step, and returned PASS.  Its audit also machine-reproved T2c over
> only the purity schema plus application closure: PP itself, QSS,
> Recombination, Persistence, and fundamentality are unused.
> `frontier/Bacon_PP_Goodman_Fun_Prime_Possibly_Pure.thy` proves T2d:
> `fun′(r) → ◇Pure(r)`.  The proof specializes T2c to `p=⊤`, transports
> purity along `r=⊤`, and uses derived possibility monotonicity.  It does not
> need PP or Persistence: `Pure(⊤)` is itself a purity-schema axiom and hence
> is necessitable in the axiom-extension calculus.  Claude Opus 5 returned
> PASS after independently re-proving possibility monotonicity, identity
> transport, the PP-free strengthening, and Goodman's original arbitrary-`p`
> route with Persistence.  The exact qualification is that this strengthening
> uses axiom-extension necessitation; it is not a local-consequence result.
> Its report is `reports/CLAUDE_AUDIT_GOODMAN_T2D_2026-07-25.md`.
> T2e is machine-proved using the literal formula `□r ∨ □¬r`.  T2f is now
> machine-proved as one conditional theorem containing all fifteen pairwise
> inequalities among `⊤`, `⊥`, `r`, `¬r`, `(r=⊤)`, and `(r=⊥)`.
> Claude Opus 5 independently rebuilt the proofs and replayed T2a--T2f over
> the PP-free core of purity plus application closure.  PP and Persistence
> are unused; application closure is needed.  T1 is also complete through
> its advertised consequences: the pure-proposition classification, the
> biconditional-operator classification, and the exact WI-to-Inv collapse
> are all machine-proved and independently audited by Claude Opus 5, PASS.
> T3 is now sharply diagnosed.  Necessitated QSS plus Persistence
> machine-proves only possible identity of the relevant pure operators
> (`CEV_T3_modal_core`), not the actual identity required by `fun′`.
> The literal Section 4 stock, including the globally assumed `∃fun′`, is now
> named `pp_T3_advertised_axioms`.
> Exact T3 is machine-proved after adding either zeroary Exhaustion
> (`CEV_Goodman_T3_advertised_with_exhaustion`) or the strictly weaker
> pure-identity rigidity principle (`CEV_Goodman_T3_heredity_rigid`).
> Unrestricted identity rigidity is machine-refuted in the `fun′` setting,
> and `Goodman_T3_advertised_modal_abstraction_countermodel` strengthens the
> two-world obstruction with a global actual `fun′` witness, unique
> fundamentality at every world, global QSS, Persistence, Necessity of
> Identity, and Modalized Functionality.  T3 still fails.  Thus Goodman's
> advertised premise list omits a genuine rigidity assumption; a full
> countermodel to every unbounded member of `pp_T3_advertised_axioms` has not
> yet been constructed.  `pp_stock_fun_prime_hereditary` independently
> verifies the semantic heredity claim in Bacon's substitution action:
> necessitated QSS plus the fact that each certified pure operator is itself
> fixed by every substitution entails heredity.  The latter is the semantic
> premise missing from the advertised object-language proof and is stronger
> than Persistence of the predicate `Pure`.
> Claude independently audited the encodings and derivations and confirmed
> this verdict.
> T4 is now machine-proved in a stronger exact object-language form:
> `∀C(Pure(C) → ¬fun′_{t→t}(C(r)))`.  The proof constructs
> `D_C(q)=¬C(q)(q)` and the two pure predicates `λX.(D_C=X)` and `λX.⊥`;
> they agree at `C(r)` but are distinct at `D_C`.  The headline theorem is
> stated over the exact closed PP-free stock
> `pp_T4_axioms = pp_purity_schema ∪ pp_application_closure_schema`, so PP
> and `fun′(r)` are formally absent rather than merely unused in the proof
> script. Claude Opus 5 independently clean-built, fully unfolded, and
> theorem-object audited the result, returning PASS WITH QUALIFICATIONS.
> The remaining qualification is semantic: repository Isabelle does not yet
> formalize a model witnessing non-vacuity of this weak stock.
> A separate theorem now records that promoting
> `fun′(r)` from an antecedent to an axiom makes the theory inconsistent;
> the conditional formulation is therefore essential.
> T5 is now machine-proved in its exact object-language form:
> `fun′(r) → ∃q(fun′(q) ∧ q ≠ r ∧ q ≠ ¬r)`.  The headline theorem
> `CEV_Goodman_T5` uses the literal closed stock
> `pp_T5_axioms = pp_purity_schema ∪ pp_application_closure_schema ∪
> {pp_target_PP}`; it contains no existence axiom for `fun′`, L2, Inv, WI,
> TU, RS, Exhaustion, Persistence, Recombination, fundamentality, or Purity
> of Fun.  The proof runs the T6 liar against the two-element hypothesis,
> with the `q=r` branch using injectivity at `r` and the `q=¬r` branch using
> `X∘¬`; the separate refutation of `D(¬d)` correctly uses `¬∘D∘¬`.
> Claude Opus 5 independently reconstructed the proof, clean-built it,
> audited all ten theorem objects, and ran decisive negation-order and
> premise-deletion controls, returning PASS WITH QUALIFICATIONS.  The
> qualifications are semantic: T5 proves no inconsistency by itself, and
> non-vacuity of its `fun′(r)` antecedent remains open.
> These remain conditional derivability results: consistency and non-vacuity
> of CEV plus the core are open, and the equation of repository CEV with
> Goodman's presentation of `T₀` remains a prose audit.
>
> Unary,
> proposition-valued Modalized Functionality is now proved in bare CEV in
> `frontier/Bacon_PP_Modalized_Functionality_Derived.thy`. Claude's adversarial
> audit found the proof correct and non-circular, but emphasized that this is
> `pp_modalized_functionality σ Prop`, not the full two-type schema. The exact
> Goodman T6-Inv vocabulary and QLN-free axiom package are encoded in
> `frontier/Bacon_PP_T6_Encoding.thy`; the same theory now machine-proves
> `Pure(D)` by an explicit constant-free abstraction, PP, application closure,
> beta conversion, and equality transport.
> `frontier/Bacon_PP_Goodman_Composition.thy` now supplies the next verified
> layer: the composition beta law, both unit laws, associativity, purity of
> composition over the exact T6 core (and arbitrary extensions of it), and
> local-assumption versions of application closure and equality reasoning.
> `frontier/Bacon_PP_Goodman_T6_Inv.thy` now proves the first T6 contradiction:
> `[] ; pp_T6_Inv_axioms ⊢CEV+ ⊥`, where the stock is exactly the purity
> schema, application-closure schema, PP at `t→t`, `∃fun′`, weak L2, and Inv.
> The proof eliminates both existential witnesses inside the object-language
> calculus and contains no QLN, Recombination, Exhaustion, fundamentality,
> Persistence, Purity of Fun, WI, TU, RS, or strong-L2.
> `frontier/Bacon_PP_Goodman_T6_TU.thy` proves the truth-uniformity route
> from the exact analogous stock with TU in place of Inv.  The preserving
> branch diagonalizes with `Z∘D`; the flipping branch eliminates an explicit
> inverse and diagonalizes with the conjugate `Z∘D∘Z⁻¹`.  This establishes
> `CEV_Goodman_T6_TU` without Inv, WI, strong-L2, RS, QLN, or any
> fundamentality assumptions.
> `frontier/Bacon_PP_Goodman_T6_WI.thy` proves the WI route over the exact
> core plus `∃fun′`, weak L2, and WI.  It first machine-proves WI⇒TU directly,
> using excluded middle on each biconditional witness, and then translates the
> checked TU contradiction through an explicit axiom-translation theorem.
> This imports no Exhaustion, Inv, Recombination, Persistence, fundamentality,
> or Purity of Fun.
> `frontier/Bacon_PP_Goodman_T6_WI_Master.thy` separately formalizes the
> displayed master family from Goodman's WI route and proves that family
> inconsistent in CEV+. Once
> `a_A ↔ ∀C(Pure(C) → (a_C ↔ ¬A))` is assumed, only `Pure(⊤)` is needed for
> the contradiction. The remaining master-route obligation is the substantive
> derivation of the family from WI, weak L2, the liar matrix, and `fun′(r)`;
> the verified WI⇒TU proof does not establish that intermediate equation.
> Literal theoremhood over the already inconsistent exact WI stock is recorded
> transparently by `CEV_Goodman_T6_WI_advertised_master_claim_ex_falso` and
> is not counted as the intended master-equation derivation.
> `frontier/Bacon_PP_Goodman_T6_RS_Encoding.thy` and
> `frontier/Bacon_PP_Goodman_T6_RS.thy` prove the final T6 route from the
> exact core plus strong-L2 and RS. RS supplies its own nonempty `fun′`-only
> specification, so there is no separate `∃fun′` axiom. The headline theorem
> is `CEV_Goodman_T6_RS`. Per the current verification policy, a single
> consolidated Claude audit will be run only after all Goodman
> object-language targets are proved.
> A controlling T1--T9 matrix is in
> `reports/GOODMAN_OBJECT_LANGUAGE_VERIFICATION_2026-07-25.md` (local,
> gitignored), with T9 correctly separated as meta-level cardinal arithmetic.

> **Driving handoff, 2026-07-25.** Start with **[CODEX_HANDOFF.md](CODEX_HANDOFF.md)**,
> not this file. It states the problem precisely (X and A), records the audit of
> this repo against Goodman's own notes, lists the ground rules (60s timeout,
> no `sorry`, bisect don't guess), records the completed unary Intensionality
> theorem, and ranks what to do next. This file is the long-form record and
> contains superseded material — every withdrawn claim is listed in §8 of the
> handoff.

> **Earlier Codex checkpoint (superseded by the tranche above).**
> `frontier/Bacon_PP_Intensionality.thy` proved
> `CEV_unary_intensionality`.

Status date: 2026-07-25.

## Current verdict on Goodman's question

Open, and further from settled than earlier drafts of this file suggested. A
consensus review (Claude Fable 5 + Codex gpt-5.6-sol, transcript at
`reports/PP_consensus_stocktaking_2026-07-25.md`) produced corrections that are
recorded here and applied below.

**The formal target is not what the semantic work has been aiming at.** The
natural formalization of Goodman's question in this repository is the
*axiom-extension* consistency statement over
`pp_recombination_PP_axioms` (`Bacon_PP_Question.thy`), whose calculus proves
necessitation for added principles. Answering it positively requires **global,
all-worlds** validity of the whole axiom set. **No formal statement of any kind
connects a word-action theorem to that target.** Semantic progress below must
not be read as progress on the defined question until that bridge exists.

Three specific discrepancies, all verified against the sources:

1. The positive witness theorems are **root-level**, and the all-worlds guarded
   theorem uses a *shifting*-fundamental presentation,
   `pp_fundamental_at i r P <-> pp_view i P = r`. That is **not** the fixed-`Fun`
   condition the target needs, which is `pp_view i P = pp_view i r` --- since
   `Fun_r = \P. Id(P, r)` and local identity is `pp_operator_equal`. The two
   coincide only where `pp_view i r = r`. The guarded theorem therefore does not
   discharge the necessitated instances.
2. `Bacon_Semantics.thy`'s `applicative_structure` locale requires `lam_den_type`
   for *every* meta-function between domains --- full-function comprehension ---
   so it **cannot host countable Henkin domains** at all. A new Henkin soundness
   interface with denotable rather than full function spaces is needed before
   modelhood is even statable.
3. The interpreted universes stop one type level **below** the target PP
   instance, whose outer constant lives at `((Prop->Prop)->Prop)->Prop`.

What genuinely has changed is that the problem is sharply localized and several
of the project's own conjectures have been correctly killed: FIN-base, the naive
IDX repair, the automorphism attack on base definability, and the unguarded
envelope condition. The hard kernel --- a countable self-classifying stock in its
all-worlds fixed-`Fun` form --- has never been constructed or even approximated.

Consensus credence: **~0.6 that the axiom-extension package is consistent**
(~0.7 for the weaker local-consequence version; the implication runs one way
only), and **~0.25--0.30 that the word-action geometric core can be completed**
after the interface redesign.

### Corrections applied

- "PP is true in the word-action M-set" is **overstated**; see the corrected
  statement under that heading below.
- "The entire difficulty is self-classification" is **withdrawn**. For the
  axiom-extension question, fixed-`Fun` all-worlds validity, the unbounded typed
  evaluator, a new soundness interface, and background modelhood are
  *independent* obligations.
- "The envelope condition is false" is an informal meta-argument with no
  corresponding lemma, and refutes only the *unguarded* sufficient condition;
  the guarded seed-aware cover's satisfiability is open.
- "The priority problem largely collapses" concerns requirement bookkeeping for
  a fixed countable family set only. The construction secures QLN by *pruning* ---
  making every pure member of the stock parameter-free --- not by exhibiting a
  rich self-classifying stock.
- The decision-basis verdict carries a cone-determinedness asterisk: the
  `p_pure` rule covers `Pure` only on cone-determined operators, so operators
  with the argument occurring *under* a `Pure` are outside the shield, and
  inclusion of the actual term-generated domain in the closure is unproved.
- Both `oterm` bridges under-interpret `App` as well as `Lam`, so the
  propositional bridge covers **no** `Pure`- or `Fun`-application at all.
- "Exactly one fundamental proposition" means existence plus uniqueness *up to
  object-language identity at each world*, together with the separate all-type
  schema forbidding fundamentals at every other type. Neither is discharged by
  any existing witness theorem.

## Verified background

The active background session contains only H, C, CE, genuine theorem-level
CEV, and their semantic infrastructure. It proves clean Henkin completeness:

```isabelle
H_clean_Henkin_valid_iff_proves
C_clean_Henkin_valid_iff_proves
CE_clean_Henkin_valid_iff_proves
CEV_clean_Henkin_valid_iff_proves
```

It also proves consistency of the CEV identity-separator diagram and obtains
diagram-preserving quotient arrows:

```isabelle
CEV_identity_separator_consistent
CEV_identity_modal_successor
CEV_identity_arrow_separates_unequal_classes
```

The quotient/category semantics still needs a uniform fresh-name construction,
quotient-valued term evaluation, the quantifier clauses, and the full truth
lemma.

## Verified PP semantic machinery

### Generic witness and Bacon function spaces

`Bacon_PP_Generic_Witness.thy` proves a QLN witness theorem for every countable
stock of classifier indices.

`Bacon_PP_MSet.thy` formalizes Bacon's local unary function space and proves:

```isabelle
pp_fun_invariant_iff_equivariant
pp_equivariant_operator_is_classifier
pp_fun_invariant_is_classifier
pp_countable_invariant_function_stock_has_QLN_witness
```

Thus the classifier/generic-witness semantics is not an ad hoc replacement for
Bacon's function domain.

### The purity operator is equivariant; Recombination is what fails

**Corrected billing.** What is proved is `pp_second_order_invariant
pp_purity_operator`: the intended denotation of `Pure_{t->t}` is equivariant and
necessitated under a natural *shallow second-order action* routed through the
section `pp_fun_lift`. Three things are missing before "the target PP instance is
true in the word-action M-set" is licensed: (i) membership of
`pp_purity_operator` in the recursive Bacon carrier at `(t -> t) -> t`;
(ii) agreement of that shallow action with the `pp_dom` class action there;
(iii) a compositional interpretation reaching type `((Prop->Prop)->Prop)->Prop`,
one level above where the universes stop.

`Bacon_PP_Purity_Operator.thy` gives the purity predicate at type
`(t -> t) -> t` its natural value and shows that value is invariant:

```isabelle
pp_purity_operator_root
pp_purity_operator_equivariant
pp_purity_operator_necessitated
pp_purity_operator_second_order_equivariant
pp_purity_of_pure_holds_in_word_action
```

So the intended denotation is equivariant and necessitated; *under the intended
but unformalized interpretation* this would verify the target instance. With the
full function domain, however:

```isabelle
pp_full_stock_has_no_recombination_witness
```

No proposition has an orbit escaping every proper classifier index, because the
orbit is indexed by words while the indices exhaust the powerset. The
consistency question is therefore a size question about the Henkin domains, not
a question about whether invariance is preserved.

### FIN-base is false

`Bacon_PP_LevelClasses.thy` constructs cyclic length-modulo partitions and one
Pure-free family realizing infinitely many pairwise distinct invariant unary
operators:

```isabelle
pp_cyclic_level_partition_iff
pp_cyc_family_values_pairwise_distinct
pp_cyc_family_realises_infinitely_many_invariant_values
```

The semantic combinatorics is machine-checked. The displayed Pure-free terms
for the construction have not yet been connected to a full deep-embedded
M-set term semantics.

### The naive uniform-index repair is false

`Bacon_PP_Uniform_Index.thy` proves:

```isabelle
pp_naive_IDX_base_counterexample
```

Equality to a value in the range of a Pure-free family does not imply that the
value is invariant. The same theory corrects the cyclic-family analysis:

```isabelle
pp_cyc_family_lifted_universal_not_invariant
pp_cyc_family_invariant_iff
```

The invariant base of the cyclic family is exactly:

```text
CycCarrier(b) or box (not CycCarrier(b)).
```

Hence this family refutes FIN-base but satisfies the desired Pure-free
base-definability condition.

### Exact general reduction

`Bacon_PP_Orbit_Stability.thy` proves for every equivariant binary family:

```isabelle
pp_binary_family_invariant_iff_parameter_orbit_stable
pp_parameter_orbit_stable_iff_root_fibre_stable
pp_binary_family_invariant_iff_root_fibre_stable
```

The open problem is therefore a parameter-freezing problem. Ordinary modal
evaluation moves every free parameter together, whereas invariance compares
the current root fibre with the fibre obtained after moving only the indexed
parameter.

## The tree-conjugation coherence diagram is complete

`Bacon_PP_TreeAut.thy` gives an explicit accessibility automorphism preserving
the propositional Boolean/modal fragment but carrying an invariant unary
operator, under conjugation, to a non-invariant one.
`Bacon_PP_TreeAut_Functions.thy` proves the domain and application obligations
at the single type `t -> t`.

`Bacon_PP_TypeCoherence.thy` now closes the remaining obligations at every
Bacon type. The recursion over types is carried by an Isabelle type class
`pp_dom` with three parameters: a carrier, the family of local equivalences the
monoid action induces, and the conjugation. The class deliberately omits the
action itself, since tree conjugation does not commute with it; what
conjugation does preserve is the induced local equivalences, and those suffice
to define higher-type identity, the local function domains, and the quantifier
domains. The single class axiom that drives everything is

```text
eqv i (conj x) (conj y)  =  eqv (tw i) x y
```

whose base instance is exactly `pp_img_cone_equal_iff`.

Nothing has been quietly replaced by a convenient substitute. At the concrete
type `t -> t` the class notions are proved to coincide with Bacon's own:

```isabelle
pp_carrier_fun_base_iff        (* the carrier IS pp_function_space_member *)
pp_eqv_fun_base_iff_fun_view   (* the equivalence IS equality of pp_fun_view *)
pp_fixed_fun_base_iff          (* the conjugation IS pp_tree_conjugate *)
```

Obligations now discharged at every Bacon type:

```isabelle
pb_id_conjugate   pb_id_carrier   pb_id_fixed     (* higher-type equality *)
pb_all_carrier    pb_all_fixed                    (* universal quantification *)
pb_ex_carrier     pb_ex_fixed                     (* existential quantification *)
pb_neg_fixed      pb_and_fixed    pb_box_fixed    (* Boolean and modal *)
pp_fixed_app      pb_K_fixed      pb_S_fixed      (* application, combinators *)
```

The last line is the induction on object-language terms: conjugation-fixedness
is closed under application, and `S` and `K` are fixed outright, so by
combinatory completeness every closed term built from fixed constants denotes a
fixed carrier element.

### The resulting non-definability theorem

```isabelle
pp_purity_not_conjugation_fixed
```

There is no conjugation-fixed carrier member at type `(t -> t) -> t` whose root
truth tracks invariance. Hence invariance is not definable from
conjugation-fixed constants.

### The signature side condition is discharged

The Pure-free language contains `Fun` as well as the logical constants, and in
the intended model `Fun` is the local identity predicate for the fundamental
proposition. So `Fun` is conjugation-fixed exactly when that witness is.
`Bacon_PP_Symmetric_Witness.thy` shows the witness can always be so chosen.
Local symmetrization fails --- gluing symmetric views cone by cone runs into the
proper index `{P. pp_swap_all P = P}` (`pp_symmetric_propositions_proper`).
Global symmetrization across the cone pair `[0, n]`, `[1, n]`, which `pp_tw`
exchanges, works:

```isabelle
pp_paired_witness_symmetric
pp_view_paired_witness
pp_symmetric_generic_witness_for_countable_proper_stock
pp_countable_stock_has_symmetric_generic_QLN_witness
pp_countable_function_stock_has_symmetric_QLN_witness
```

For every countable stock there is a QLN witness `R` with `pp_img R = R`.

## Correction: tree conjugation cannot refute base definability

This supersedes the earlier handoff's "recommended first attack". The
coherence diagram completes, and the non-definability theorem is real, but it
does **not** touch the base-definability condition. Machine-checked:

```isabelle
pp_stock_locus_conjugation_stable
```

The base-definability condition quantifies over the loci
`{b. Y b is an invariant member of L}`, where `L` is the stock of denotations of
closed Pure-free terms of type `t -> t`. Every member of `L` is
conjugation-fixed, so `L` is conjugation-stable and pointwise fixed, and for a
Pure-free family `Y` we have `Y (pp_img b) = pp_tree_conjugate (Y b)`. Then:

- if `Y b` is in `L`, then `pp_tree_conjugate (Y b) = Y b`, so the invariance
  claims at `b` and at `pp_img b` are literally the same claim;
- if `Y b` is not in `L`, the membership conjunct fails at both parameters.

Either way the locus is `pp_img`-stable. This is the cancellation the earlier
handoff warned about, and the argument uses nothing special about `pp_tw`: it
applies to every automorphism fixing the signature. The parity family is not a
counterexample either --- what its non-stability shows is that its values are
not in `L`, not that the locus moves.

**Tree conjugation is therefore removed from the list of live attacks on base
definability.** It refutes only the stronger claim that invariance is definable
as a predicate over the whole function domain at `t -> t`.

## Exact remaining consistency frontier

Two attacks remain, and they are no longer symmetric in promise.

1. Base definability, now known to be immune to automorphism arguments. Any
   refutation must come from a diagonal or counting argument that constructs a
   Pure-free family defeating an enumeration of candidate Pure-free
   definitions. Plain cardinality does not suffice: there are countably many
   Pure-free families and countably many Pure-free formulas, and one definable
   set may contain continuum-many propositions.
2. The alternative model route: construct a countable, orbit-generic,
   self-classifying Henkin stock. The generic-witness theorem already supplies
   QLN for *any* countable stock, so the whole difficulty is
   self-classification. Correctly typed, the condition is that the domain at
   `sigma -> Prop` contain the classifier of the pure elements of `sigma`; it is
   not a set membering itself, and simple typing blocks the Russell
   self-application, so there is no Cantor-style no-go in sight.

   Note where the cost is and is not. Reading `pp_unary_recombination` and
   `pp_unary_exhaustion` in `Bacon_PP_Question.thy`, the only nonzero-arity QLN
   instance required is the unary one, quantifying over the *pure* elements of
   the domain at `Prop -> Prop` together with the fundamental proposition. So
   the escapability burden falls only on the invariant part of that one domain.
   The domain at `(Prop -> Prop) -> Prop` may be as large as one likes, which is
   why housing the purity operator costs nothing by itself, and why the zeroary
   instances are free (pure propositions are `{}` or `UNIV`, and `pp_sem_box`
   fixes both). The entire difficulty is that the stock of pure elements at
   `Prop -> Prop` grows when the language is enlarged by `Pure` and by a name
   for the witness.

## The self-classifying stock: the priority problem largely collapses

`frontier/Bacon_PP_Stock_Requirements.thy` (see the session layout note below)
begins route 2, and the first finding is that most of the anticipated
priority/forcing machinery is not needed.

Every element of the term-generated domain at `t -> t` over the seed `r` is
`Y r` for an equivariant binary family `Y` in which the seed occurs only as the
argument: abstracting the seed turns `Fun` into `\x. \P. Id(P, x)`, and `Pure`
is `pp_purity_operator`, which is parameter-free and equivariant. And
`Bacon_PP_Orbit_Stability.thy` already proves that `Y r` is invariant exactly
when `Y` is constant on the orbit of `r`.

So build the witness to defeat orbit-constancy. For each *non-constant* family,
place two propositions separating it into the orbit; for each *constant*
family, place one proposition escaping the index of its constant value. Both
kinds of requirement are met by prescribing values at reserved cones, the
paired cones are independent and inexhaustible, and hence the requirements do
not interact: no priority ordering, no injury.

```isabelle
pp_prescribed_orbit_witness
pp_two_orbit_values_defeat_stability
pp_nonconstant_family_not_invariant
pp_countable_family_stock_has_generic_witness
```

The last is the main theorem: for every countable set of equivariant families
there is a tree-symmetric `r` such that every *invariant* value of the stock
comes from a globally constant family --- so it is parameter-free --- and
satisfies unary QLN. The pure part of the stock is thereby made independent of
the witness, which is what removes the circularity.

Sanity check, also proved: at such a witness `Fun` is *not* pure
(`pp_fundamentality_not_pure_when_required`), since it is the value of the
non-constant family `pp_operator_equal`. That is as it should be --- Purity of
Fun is exactly what this question does not assume, and a construction that made
it true for free would be answering a different question.

### What the collapse does not cover

The dependence of the family set on the seed is not fully removed, and the
residue is now identified exactly: it is the object-language *quantifier
domains*, and nothing else. `Fun` is handled by abstraction and `Pure` is
parameter-free, but a quantified term is interpreted over the Henkin domains,
which are generated from the seed.

This residue is not repaired by the separation requirements, and the reason is
worth recording. Consider a family of the shape

```text
Y b P  =  forall X in D. Psi X P
```

in which the parameter `b` does not occur. It is constant, so the separation
requirements never touch it, yet its index `{P. forall X in D. Psi X P}` moves
when `D` moves. So `pp_family_constant_index` gives
`index (Y_r r) = index (Y_r {})` but not `index (Y_r {}) = index (Y_s {})`, and
the escape requirement can no longer be posed independently of the seed. Nor
does a monotone union of domains repair it: enlarging a domain changes the
denotation of quantified terms already present, so it is not merely that new
families arrive. A stage-wise construction would additionally need a
persistence theorem, to the effect that each term's denotation is eventually
constant along the chain of domains.

What can be stated exactly is the hypothesis under which the construction goes
through unchanged, and it is now a theorem:

```isabelle
pp_seed_dependent_stock_has_generic_witness
pp_uniform_envelope_gives_generic_witness
```

If one countable set of propositions covers the requirements of every family
that any seed can produce --- for instance because a single countable envelope
`Fam0` contains `Fam s` for every seed `s` --- then the witness exists outright,
with no priority ordering and no injury. **The remaining obligation on route 2
is therefore that one uniformity condition on the object language, not a
forcing construction.**

Two scope notes on this part. The conclusion is root-level QLN; validating PP
at every world with `Fun_r = pp_operator_equal r` needs the corresponding
tail-orbit requirements as well, and the all-worlds guarded theorem in
`Bacon_PP_Generic_Witness.thy` uses a different, shifting-fundamental
presentation that cannot simply be substituted. And none of this yet shows the
resulting structure models H, Classicism, CE and CEV.

## Attacking the uniformity condition

Two results, both machine-checked. Neither proves the condition; together they
shrink it and close off the obvious way of achieving it.

### The requirement reduces to a diagonal set

`frontier/Bacon_PP_Diagonal_Reduction.thy`. For an equivariant binary family
`Y` put `D_Y = {b. Y b b is true at the root}`. Then:

```isabelle
pp_equivariant_diagonal_is_classifier   (* Y b b = pp_classifier D_Y b *)
pp_orbit_index_iff_diagonal             (* the reduction *)
```

The second says that when `Y r` is pure --- equivalently, when `Y` is constant
along the orbit of `r` --- the orbit sits inside `pp_operator_index (Y r)`
exactly when it sits inside `D_Y`. Note it needs only orbit-stability, not
equivariance.

This matters because `pp_operator_index (Y r)` is the quantity whose
seed-independence was in doubt, and `D_Y` is a function of the family alone: it
does not mention the seed and is obtained by a single root-truth test rather
than by evaluating `Y` at the seed. The construction also shrinks to one
required proposition per family instead of three, with separators needed only in
the degenerate case where the diagonal is universal and the family is
non-constant --- a constant family with universal diagonal has a universal index
outright (`pp_constant_family_diagonal`):

```isabelle
pp_diagonal_stock_witness
pp_diagonal_envelope_witness
```

### The domains cannot be frozen by choosing the seed inside them

`frontier/Bacon_PP_Seed_Nontriviality.thy`. The cheapest route to
seed-independence would be to take the seed from a domain that was already
closed before the seed was introduced --- the term model over the seed-free
language. Adjoining it would then enlarge nothing, the domains would stay
fixed, and the envelope hypothesis would hold outright.

That route is now closed. A closed seed-free term has no free parameter, so its
denotation is invariant, and the only invariant propositions are `{}` and
`UNIV`. An invariant proposition has a one-point orbit, and a one-point orbit is
trapped inside a proper classifier index:

```isabelle
pp_invariant_orbit_singleton
pp_invariant_seed_fails_recombination
pp_no_seed_inside_an_invariant_domain
```

The trap is not exotic. The two relevant classifiers are exactly the modal
operators,

```isabelle
pp_box_is_classifier_UNIV        (* pp_sem_box     = pp_classifier {UNIV} *)
pp_box_neg_is_classifier_empty   (* pp_sem_box o - = pp_classifier {{}}   *)
```

so they are Pure-free definable and belong to any stock closed under the
logical constants. The failure cannot be dodged by trimming the stock:

```isabelle
pp_extreme_seed_fails_definable_recombination
pp_seed_must_be_contingent
pp_seed_not_extreme
```

**The fundamental proposition must therefore be genuinely contingent, and must
lie outside every seed-free domain.**

### Requirements only where they are needed

`frontier/Bacon_PP_Seed_Aware_Requirements.thy`. The requirement sets above are
imposed on every family whether or not it causes trouble at its own seed, and
that waste is not harmless: it can demand escapes that are impossible to
supply. The guarded version imposes a requirement only when the value at the
seed is pure and its index is proper:

```isabelle
pp_seed_aware_diagonal_stock_witness
pp_seed_aware_below_diagonal          (* the guarded cover is the weakest *)
```

The sharpest instance is the membership test `T = \b. \c. exists X:Prop. Id(X,b)`
below: its diagonal is the whole proposition domain, so the unguarded
requirement demands a proposition escaping the domain, yet its value at its own
seed has universal index and satisfies QLN outright. The guarded cover drops it.

### Verdict: the envelope condition is false

Not merely unproved. The argument, which is meta-level because it turns on the
term semantics:

1. A seed belongs to its own domain, so each fibre of `s |-> D_Prop(s)` is
   countable; continuum-many seeds therefore give continuum-many distinct
   proposition domains.
2. The membership test `T = \b. \c. exists X:Prop. Id(X,b)` has diagonal set
   exactly `D_Prop(s)`, since root-level identity is genuine equality. So `T`
   turns distinct domains into distinct families.
3. Hence the union of the family sets over all seeds has the cardinality of the
   continuum, and no countable `Fam0` contains every `Fam s`.

One correction to an earlier draft of this note. The obvious candidate
`\b. \c. forall X. (X --> c)` does **not** witness seed-dependence: whenever the
domain contains `UNIV`, as any logical domain must, that term has value `c` and
its diagonal is seed-independent. The membership test is what does the work.

### Verdict: no generic fixed-point theorem is available either

The seed space is Cantor space, which is compact Polish, but that alone gives
no fixed point --- continuous self-maps of Cantor space can be fixed-point-free.
Nor is there monotonicity to exploit: `exists X. Id(X,b)` makes the diagonal
`D_Prop(s)` while `forall X. not Id(X,b)` makes it the complement, so existential
and universal occurrences have opposite variance and quantifier alternation
destroys any uniform order behaviour. `pp_escape` is defined by `SOME` and has
no reason to be continuous or monotone. So Banach needs a guardedness theorem
that is not available, Knaster--Tarski needs monotonicity that fails, and Baire
category yields no fixed point.

### Where that leaves the route

The shape of the problem has changed even though it is not solved. What must be
uniform is now the family of diagonal sets rather than indices of seed-evaluated
operators; the requirement set has been cut to those families that actually
cause trouble; the natural way of freezing the domains is refuted; the envelope
form of the hypothesis is false; and the off-the-shelf fixed-point theorems are
ruled out.

## The persistence theorem: false in general, with two usable substitutes

`frontier/Bacon_PP_Domain_Persistence.thy`. The stage-wise construction would
need each term's denotation to settle down along an increasing chain of domains.
It does not.

### It fails

```isabelle
pp_universal_denotation_does_not_persist
```

Along an increasing chain whose stages are even *finite*, the denotation of the
single term `forall X : Prop. X` --- read semantically as
`pp_forall_over D id` --- differs from its limit value at **every** finite stage.
The chain is `D n = {- {0^k} | k < n}`, so the stage values are
`- {0^k | k < n}`, strictly decreasing forever. A stage-wise construction
therefore cannot assume persistence; it has to earn it.

### Substitute one: the limit is always recoverable from the stages

```isabelle
pp_forall_over_Union    (* limit = intersection of the stage values *)
pp_exists_over_Union    (* limit = union of the stage values        *)
```

Neither needs the chain to be increasing. The limit denotation need not equal
any stage denotation, but it is always determined by the sequence of them. For a
fusion construction this is the correct replacement for persistence.

### Substitute two: persistence under a finite-image bound

```isabelle
pp_finite_image_persistence
```

If the quantified body takes only finitely many values over the limit domain,
the denotation does stabilize. This is exactly what the counterexample violates
--- there the body is the identity and takes infinitely many values. Note this
is a condition on the term and the limit domain together, not on the chain.

### Persistence is exactly finite attainment

```isabelle
pp_persistence_iff_attained
```

For an increasing chain the stage values decrease, so eventual stabilization is
equivalent to the limit value being reached at one single finite stage. That
converts persistence from a statement about tails into a concrete attainment
question.

### Variance, and why Knaster--Tarski is unavailable

```isabelle
pp_forall_over_antitone
pp_exists_over_monotone
```

Universal quantification is antitone in the domain and existential quantification
is monotone. Both variances are realized, so a term with alternating quantifiers
has no uniform variance in the domain. This is the checked form of the
obstruction noted earlier.

## Do Henkin closure chains admit finite-image bounds? No --- but that was the
## wrong condition, and the right one holds

`frontier/Bacon_PP_Attainment.thy`. This answers the question left open above,
and in doing so it defuses the counterexample.

### Finite image is unusable here

The simplest quantified term of all, `forall X : Prop. X`, has the identity as
its body, so its image over the limit domain *is* the limit domain, which is
infinite in any nondegenerate model:

```isabelle
pp_identity_image_is_the_domain
pp_identity_body_has_no_finite_image_bound
```

So no Henkin chain satisfies the finite-image hypothesis for that term.

### Attainment is the right condition, and it is weaker

What the proof of `pp_finite_image_persistence` actually uses is only that some
*finite* part of the domain already cuts the intersection down to its limit
value:

```isabelle
pp_finitely_attained            (* the definition *)
pp_finitely_attained_persistence
pp_finite_image_gives_attainment   (* finite image is a special case *)
```

### Closure supplies attainment exactly where finite image fails

Comprehension puts the value of `forall X. X` into the domain at the quantified
type. That single element attains the intersection, so persistence holds for the
identity body however large the domain is:

```isabelle
pp_closed_domain_attains_identity
pp_closed_domain_identity_persistence
```

More generally a monotone body attains at the least proposition and an antitone
body at the greatest, and any domain closed under the Boolean connectives
contains both `{}` and `UNIV`:

```isabelle
pp_monotone_body_attains
pp_antitone_body_attains
```

### The counterexample is not a Henkin chain

```isabelle
pp_counterexample_domain_not_closed
```

The chain that refutes persistence has a limit domain that provably does *not*
contain the value of `forall X. X` over it. So it is not closed under
comprehension, and the refutation does not transfer to the chains we care
about. The earlier negative result stands as stated --- persistence is not a
general fact about increasing chains --- but it does not obstruct the
construction.

### The remaining gap is real: non-contingency defeats attainment

`frontier/Bacon_PP_Attainment_Failure.thy`. The gap left above --- bodies at
quantified type `Prop` that are neither monotone nor antitone --- is not
hypothetical, and the counterexample is about as innocent as it could be.

The body is **non-contingency**, `f X = box X or box (not X)`. It is Pure-free,
parameter-free, and of modal depth one, and it is mixed in variance exactly as
predicted:

```isabelle
pp_decided_not_monotone     (* {} is decided everywhere, its supersets need not be *)
pp_decided_not_antitone     (* UNIV likewise *)
```

The domain is generated by `C_n = {w. length w <= n}`. A world `i` decides `C_n`
exactly when `n < length i`:

```isabelle
pp_decided_shortprop
```

Deep enough into the tree the cone holds only long words and `C_n` is uniformly
false there; at shallower worlds the cone holds both short and long words. So the
sets of deciding worlds shrink to nothing, while every *finite* family of
generators is still decided somewhere. Hence:

```isabelle
pp_decided_defeats_attainment
pp_decided_denotation_does_not_persist
```

Crucially this is not an artefact of taking too small a domain. Decidedness is
inherited by complements, intersections and boxes:

```isabelle
pp_decided_Compl   pp_decided_Int   pp_decided_box
```

so generating a Boolean and modal algebra from the `C_n` leaves the deciding
worlds exactly where they were. The positive results really do stop at the
monotone and antitone cases.

### Caveat, and what is now open

What has been exhibited is a legitimate domain of propositions closed under the
connectives and the modality --- the form in which the question was posed. It is
*not* a domain shown to arise as the Henkin closure of a language over a seed.
To promote this into an obstruction for the consistency construction one would
still have to realize the `C_n`, or something with the same decidedness
behaviour, as denotations of terms over a seed. That looks plausible, since
`C_n` is a depth predicate and the seed is contingent by `pp_seed_not_extreme`,
but it is not proved and should not be assumed.

So the position is symmetric and sharp. Persistence holds for monotone and
antitone bodies by closure; it fails for a simple mixed body over a
Boolean-and-box-closed domain; and the single remaining question is whether that
failure can be realized inside a seed-generated domain.

## Can it be realized over a seed? Almost certainly not

`frontier/Bacon_PP_Decided_Realization.thy` takes up that question, and the
answer is negative for the closure that a single seed actually generates.

### Deciding worlds form an up-set

```isabelle
pp_decided_deeper
pp_decided_accessible
```

If `X` is decided at `i` it is decided at every deeper world, so each set of
deciding worlds is an up-set and the counterexample needs a strictly decreasing
sequence of up-sets with empty intersection.

### A refutation test: one nowhere-decided proposition kills it

```isabelle
pp_nowhere_decided_gives_attainment
pp_parity_nowhere_decided
pp_domain_with_parity_attains
```

If the domain contains even one proposition decided *nowhere*, the intersection
is already empty at that single element and attainment holds. Such propositions
exist in abundance in the ambient model --- every parity proposition is one.

This should not be oversold, and Codex was right to push back on an earlier
draft that did. Genericity does **not** force a nowhere-decided Boolean or modal
combination of the seed; quite the reverse, at a world where `pp_view i r` is
extreme that same world decides every Boolean and modal term in `r`. So this is
a way of killing a proposed realization when it happens to apply, not an
obstruction guaranteed to fire.

### The obstruction that does fire: finitely generated domains always attain

Decidedness passes through the Boolean connectives, the modality, and --- as
Codex pointed out --- propositional identity as well, since local identity just
*is* a boxed biconditional here:

```isabelle
pp_operator_equal_is_boxed_biconditional
pp_bmclosure_operator_equal
```

So a world deciding a generating family decides everything the family generates:

```isabelle
pp_bmclosure                (* Boolean-and-modal closure, inductively *)
pp_decided_bmclosure
pp_bmclosure_attains
pp_single_seed_closure_attains
```

Hence a domain generated by **finitely many** propositions always attains, at
its generators. In particular the closure of a single seed under Booleans, box
and identity always attains, and **the attaining element is the seed itself** ---
whether or not any nowhere-decided proposition is around.

A related check, agreed with Codex: a *length-only* seed cannot define the `C_n`
at all. If `r = {w. length w in E}`, the generated submodel is the linear
reflexive frame with valuation `E`; if `E` is not eventually constant then
`box E = box (-E) = {}` and the algebra is inside `{{}, UNIV, E, -E}`, while if
`E` is eventually constant every generated set is too. Either way the
one-generated Boolean-modal algebra is *finite*, so it cannot contain infinitely
many distinct `C_n`.

### Verdict

The counterexample **cannot** be realized from the closure of a seed under the
Boolean connectives, the modality and propositional identity. Any realization
must get its non-attainment from the quantifiers, from higher-type
constructions, or from `Pure`, and there it would have to manufacture infinitely
many propositions with the finite intersection property on deciding worlds and
empty total intersection, while producing neither a nowhere-decided proposition
nor any finite attaining family.

Realization in the *full* Henkin closure is therefore still open, and neither of
us can construct it or rule it out. Both Claude and Codex judge it unlikely, but
that is a judgement and not a proof. The counterexample of
`Bacon_PP_Attainment_Failure.thy` accordingly stays a statement about
Boolean-and-box-closed domains, exactly as stated there.

## The finite decision basis is proved, and the quantifiers do not break it

`frontier/Bacon_PP_Decision_Basis.thy`. The target above is now a theorem, and
in the strong form that was expected to fail.

The suspicion was that quantification breaks the induction, because a bound
variable ranges over propositions that need not be decided wherever the seed is.
That is unfounded. A universally quantified denotation is just an intersection,
`pp_forall_over D f = Inter (f ` D)`, and what has to be decided is not the bound
variable but the *body's value*, which is itself a domain element. And
decidedness is preserved by arbitrary intersections, since an intersection of
sets each `{}` or `UNIV` is again `{}` or `UNIV`:

```isabelle
pp_view_Inter
pp_decided_Inter
```

Existential quantification follows, being a complement of an intersection of
complements. So decidedness at a world is preserved by complement, the modality,
and arbitrary intersection --- which between them cover the Boolean connectives,
propositional identity, and quantification **at every type**:

```isabelle
pp_qclosure                    (* the logical closure, inductively *)
pp_decided_qclosure
pp_qclosure_operator_equal
pp_qclosure_forall
pp_qclosure_exists
```

Hence the target theorem, and its strong single-seed form:

```isabelle
pp_qclosure_finite_decision_basis
pp_seed_decision_basis          (* ALL X : D. pp_decided r <= pp_decided X *)
pp_seed_domain_attains_decided
pp_counterexample_not_realizable_over_seed
```

**The non-contingency counterexample cannot be realized inside the Pure-free
logical closure of a seed, at any type.** The seed alone is a decision basis.

The contrapositive is the tool to reach for when testing any future proposed
realization:

```isabelle
pp_non_attaining_domain_not_finitely_generated
```

a domain that fails to attain is not contained in the logical closure of any
finite set of its members.

### Scope: `Pure` is not covered, and why

The closure covers the Boolean connectives, the modality, propositional identity
and quantification at every type. It does not cover `Pure`, and that is not an
oversight. A purity value is necessitated, so its views are upward closed --- but
upward closed is not the same as `{}` or `UNIV`. A local function whose views are
invariant at every world of positive depth but not at the root has a purity value
undecided at the root, however the seed behaves there. So decidedness is not
preserved by `Pure` and the induction has no case for it.

That leaves a clean division. Inside the Pure-free logical fragment generated by
a seed the counterexample is dead. Any realization must run through `Pure`
itself.

## `Pure` does not break it either: the last route is closed

`frontier/Bacon_PP_Pure_Decision_Basis.thy`.

### `Pure` really does compute the counterexample's body

```isabelle
pp_purity_of_meet     (* Pure (\P. b and P) = box b or box (not b) *)
```

Applying `Pure` to the operator that conjoins with `b` gives exactly
non-contingency of `b`. So the body of the counterexample was never an arbitrary
choice --- it is what `Pure` computes, and this is the strongest reason to have
expected `Pure` to be the way in.

### It is not the way in

```isabelle
pp_cone_determined
pp_decided_generators_give_purity
pp_decided_generators_decide_purity
```

If a world decides every generator, then the cone above it is *uniform* for the
generators, so any function determined by them cannot vary there; its local view
is therefore invariant, the world lies inside the purity value, and that value is
necessitated and so decided there. Adding `Pure` to the closure preserves the
decision basis:

```isabelle
pp_pclosure                          (* closure including Pure *)
pp_decided_pclosure
pp_pclosure_finite_decision_basis
pp_pure_seed_decision_basis
pp_pure_seed_domain_attains_decided
```

**The non-contingency counterexample is unrealizable in the full logical closure
of a seed, `Pure` included. The seed alone remains a decision basis.**

What defeats the realization is not that `Pure` cannot reach non-contingency ---
`pp_purity_of_meet` shows it can. It is that `Pure` can only reach the
non-contingency of things *determined by the generators*, and at a world where
the generators are decided everything so determined is invariant, hence pure,
hence decided. The operator that would be needed --- one becoming invariant
exactly below some finite depth --- requires a depth predicate as a parameter,
which is precisely what the construction cannot supply.

## The cone-determinedness induction is now done

`frontier/Bacon_PP_Cone_Determined.thy`. The side condition
`pp_cone_determined` was previously assumed. It is now proved, by induction over
the generating operations, at both levels.

Propositions:

```isabelle
pp_cone_det_prop
pp_qclosure_cone_det          (* everything in the propositional closure *)
pp_cone_determined_purity     (* purity values, via equivariance *)
```

Unary operators, with the closure `pp_fclosure` whose rules are the identity,
cone-determined constants, complement, the modality and arbitrary intersection
--- between them the Boolean connectives, propositional identity and
quantification at every type:

```isabelle
pp_fclosure
pp_fclosure_cone_determined
pp_fclosure_member            (* and they stay inside Bacon's function domain *)
```

The payoff is that the `p_pure` side condition is **discharged rather than
assumed**:

```isabelle
pp_fclosure_purity_in_pclosure
pp_fclosure_purity_cone_det
```

so `pp_pure_seed_decision_basis` no longer rests on an unproved hypothesis about
the operators it quantifies over.

The reason the induction goes through is uniform: every logical operation
computes the local view of its result from the local views of its arguments ---
complement commutes with the view, so does the modality, so does arbitrary
intersection, and so, by `pp_purity_operator_equivariant`, does `Pure`. Nothing
in the logical vocabulary can see the world except through the generators.

### What is still not closed

Two things, and they are narrower than the caveat they replace.

1. Operators in which the argument occurs *inside* a `Pure`, such as
   `\P. Pure (\Q. P and Q)`, are not generated by `pp_fclosure`. That particular
   one is harmless --- by `pp_purity_of_meet` it is `\P. box P or box (not P)`,
   whose local views do not depend on the world at all --- but the general case
   needs a closure one type up and is not treated.
2. The connection to the project's deep-embedded `oterm` syntax. What is
   formalized is an induction over semantic generating operations, which is the
   content the surrogate needs; identifying those with the denotations of
   `oterm` constructors is the remaining bridge.

Gap 2 is the *same* bridge the fixed-term theorem of `Bacon_PP_TypeCoherence`
needs. The two outstanding gaps of this kind in the development have now
converged into one.

## The bridge to `oterm` is built, for the propositional fragment

`frontier/Bacon_PP_Oterm_Bridge.thy`. Gap 2 above is now partly closed: the
semantic closures are connected to the project's deep-embedded syntax.

`pp_eval` gives `oterm` an M-set valuation, interpreting variables,
propositional constants, the Boolean connectives, object-language identity and
quantification at `Prop`. The modality needs no clause of its own, since
`Bacon_Modal` defines `box A` as `Eq Prop A ObjTrue` and the identity clause
already delivers it:

```isabelle
pp_eval_ObjBox     (* pp_eval Dom V (box A) env = pp_sem_box (pp_eval Dom V A env) *)
```

Two inductions over `oterm`:

```isabelle
pp_eval_in_qclosure           (* denotations lie in the propositional closure *)
pp_eval_abstract_in_fclosure  (* abstracting a de Bruijn position gives an operator *)
```

The second is the one the `Pure` results need, and it yields the bridge proper:

```isabelle
pp_eval_abstract_cone_determined
pp_eval_purity_in_pclosure
```

So for terms of the interpreted fragment, cone-determinedness is no longer a
surrogate assumed of the operators --- it is derived from the syntax. Combined
with `pp_pure_seed_decision_basis`, the seed is a decision basis for the
denotations of these terms.

### What the bridge does not cover

Abstraction and application are given the value `{}`. This is a deliberate
under-interpretation, harmless for the theorems above since `{}` lies in every
closure, but it means the bridge says nothing about terms whose meaning depends
on them --- in particular nothing about quantification at higher types, and
nothing about *iterated* `Pure`, which is what the target PP instance itself
involves.

Interpreting those needs a value universe for the higher domains, which is the
same obstacle `Bacon_PP_TypeCoherence` works around with a type class.

## Extending the bridge above the propositional fragment

`frontier/Bacon_PP_Higher_Bridge.thy`.

First, what the type class can and cannot do here, since this is easy to get
wrong. `pp_dom` supplies a carrier, the local equivalence and the conjugation at
*every* object type, and the coherence theorems hold at all of them. What it does
not supply is a single HOL type in which values of *different* object types sit
together --- and an evaluation function on `oterm` needs exactly that, because a
de Bruijn environment mixes types. The class and the bridge are therefore
complementary, not alternatives: the class gives type-indexed coherence with no
evaluation function, the bridge gives an evaluation function up to a fixed level.

The universe here goes to level two --- `Prop`, `Prop -> Prop` where the pure
stock lives, and `(Prop -> Prop) -> Prop` where `Pure_{t->t}` itself lives --- and
is tied back to the class by

```isabelle
pp_fclosure_is_class_carrier
```

which says the operator level is Bacon's local function domain, i.e. the class
carrier at `pp_base => pp_base`.

```isabelle
pp_veval                        (* the higher-type valuation *)
pp_veval_ok
pp_veval_prop_in_pclosure
pp_gok_purity                   (* Pure at Prop -> Prop is a good value *)
pp_fok_decided                  (* Pure at Prop is non-contingency *)
pp_fok_fundamental              (* Fun is local identity with the seed *)
```

Covered: application at both levels, quantification at `Prop` and at
`Prop -> Prop`, and `Pure` at both types. Since a variable bound by a
`Prop -> Prop` quantifier may be fed to `Pure_{Prop->Prop}` and the result to
`Pure_{Prop}`, **iterated `Pure` is inside the fragment**, which the propositional
bridge could not reach. Denotations lie in `pp_pclosure G`, so
`pp_pure_seed_decision_basis` applies.

### Two different reasons things are still missing

These should not be run together.

**A design limit.** `Lam` is left uninterpreted in this theory. Certifying an
operator built by abstraction needs it to lie in `pp_fclosure`, and the natural
induction breaks at `App`: an application whose operator *and* argument both vary
with the abstracted variable is not covered by the operator closure, which has no
application rule. So operators enter only through the domain `DF` and the
constants. The propositional bridge does certify abstractions
(`pp_eval_abstract_in_fclosure`), so the two bridges are complementary --- that
one has `Lam` but no higher types, this one has higher types but no `Lam`.
Closing the overlap needs an operator closure with an application rule, and that
is a real piece of work not done here.

**A hard limit.** The target PP instance is
`Pure_{(t->t)->Prop} (Pure_{t->t})`, whose outer constant lives at
`((Prop->Prop)->Prop)->Prop`, one level above this universe. That particular
level is a mechanical extension. Adding *all* levels is not, and cannot be done
this way: a HOL datatype has values at only finitely many type levels, while the
object language has terms at unboundedly many.

So the gap is now precise rather than vague. Any *fixed* instance of the question
is reachable by extending the universe far enough. A statement quantifying over
*all* object types is not, and would need either a set-theoretic model of the
type hierarchy or a class-indexed family of evaluation functions in place of a
single one. The class already supplies the type-indexed coherence side; what no
HOL type can supply is the single evaluation function such a statement would have
to quantify over.

## Session layout and build times

The project is split so that work in progress verifies quickly.

- `Higher_Order_Metaphysics` --- the background session.
- `Higher_Order_Metaphysics_PP` in `pp/` --- settled PP results. Stable base.
- `Higher_Order_Metaphysics_PP_Frontier` in `frontier/` --- work in progress, a
  leaf session over the stored heap of the PP session, with
  `options [timeout = 60]`.

Editing a frontier theory rebuilds only that theory, in about five seconds; the
whole project rebuilds in a few seconds when cached. The timeout makes a
runaway proof fail fast with a line number instead of hanging the build. Move
theories down from `frontier/` into `pp/` once they are settled.

## Scope notes

- `pp_purity_not_conjugation_fixed` is an internal theorem about
  conjugation-fixed carrier members. The step from it to "Purity is not
  Pure-free definable" uses combinatory completeness at the meta level, each of
  whose steps is one of the checked closure theorems above, together with
  fixedness of the non-logical constants, which
  `Bacon_PP_Symmetric_Witness.thy` supplies for `Fun`.
- `Bacon_PP_TypeCoherence.thy` establishes the recursive carriers,
  conjugations, higher-type identity, and quantifier coherence. It does not
  contain a deep-embedded object-language term-denotation induction, and does
  not by itself establish that the construction models H, Classicism, CE, and
  CEV at every recursively generated type. Those remain open.
- At a function type, `pp_eqv []` is extensional equality on the carrier, not
  HOL equality on arbitrary representatives. Statements about `L` should be
  read modulo that equality. At `t -> t` the source carrier is everything, so
  there the two coincide.

## Hygiene

- No active theory imports Caie material.
- `ContextVectorEquivalence` is absent from the active logic.
- No active theory contains `sorry`, `oops`, `admit`, or
  `quick_and_dirty`.
- The complete active project builds with Isabelle2025-2.

Earlier Caie and contextual-rule material is preserved under
`quarantine/2026-07-24_pre_core_cleanup/`.

## Step 1 done: the axiom-extension soundness interface

`frontier/Bacon_PP_Axiom_Soundness.thy`. The first ranked step is complete.

It is deliberately **not** a model construction. It is a locale enumerating the
semantic obligations plus the conditional theorem: global validity of every
member of `T` implies axiom-extension consistency of `T`.

```isabelle
henkin_action_model                    (* the locale *)
gvalid / gvalid_set                    (* global = every world, every env *)
ObjFalse_not_gvalid
CEV_axiom_soundness
CEV_axiom_consistent_of_gvalid
pp_recombination_question_of_gvalid    (* instantiated to the target *)
pp_full_QLN_question_of_gvalid
```

Two design points, both answering defects the review found:

- **Denotable, not full, function spaces.** The locale never quantifies over
  meta-functions. It asks only that a well-typed *term* denote in the domain of
  its type. `applicative_structure`'s `lam_den_type` demands a denotation for
  every meta-function between domains, which makes countable Henkin domains
  impossible; this locale admits them.
- **Global validity.** `gvalid` quantifies over all worlds and all well-typed
  environments, so a root-level theorem cannot be mistaken for the obligation.

`base_sound` (all CEV theorems globally valid) and `zeta_sound` (vector
equivalence) are carried as explicit hypotheses of the theorems rather than
folded into the locale, because they are precisely what a concrete model must
earn and they should be visible in the statement.

**The locale is proved satisfiable** (`triv_model`, a collapsed boolean
structure), so the conditional theorems are not vacuous. That witness does *not*
satisfy `base_sound` or `zeta_sound` — supplying a structure that does is the
remaining work.

### The obligation checklist

1. A structure satisfying the locale. Countable Henkin domains are admissible.
2. `base_sound` — background modelhood, now one hypothesis rather than a
   scattered obligation.
3. `zeta_sound` — pointwise identity at `Prop`-valued arrow types, pushed
   through the `app_vec`/`fresh_vars` bookkeeping of `zeta_body`.
4. `gvalid_set pp_recombination_PP_axioms` — every axiom true at **every** world
   under **every** well-typed environment. This is where the fixed-`Fun`
   all-worlds core lives, and where the existing root-level witness theorems do
   not reach.

Four separable jobs with a machine-checked statement of how they combine. It
also makes the discipline explicit: a word-action theorem bears on Goodman's
question only by way of item 4, and only if stated at every world.

## Step 2 done (negative result): the refutation attack in CEV+

`frontier/Bacon_PP_Positive_Diagonal.thy`. The consensus plan required at least
one line that tries to *refute* consistency. It was run and **found no
contradiction**. The honest report is a mapped seam, not a result.

The attack was aimed at the argument-under-`Pure` seam. First finding: that seam
is not new. `pp_diagonal_operator` is already `pp_diagonal_builder` applied to
`Pure`, i.e. it is `λq. ¬ Pure (K q)`. So the base camp's derivations were
already running through it, and what was missing was only the un-negated form.

New checked material:

```isabelle
pp_positive_builder / pp_positive_diagonal        (* λq. Pure (K q) *)
typed_pp_positive_builder / typed_pp_positive_diagonal
pp_positive_builder_purity_axiom                  (* closed, constant-free *)
pp_positive_diagonal_pure_recombination           (* it is in the pure stock *)
pp_positive_diagonal_pure_full_QLN
pp_positive_diagonal_recombination_instance       (* its QLN instance at R *)
```

So the calculus proves: the positive diagonal is pure, and Recombination applies
to it, giving `□(Pure (K R)) → ∀q. Pure (K q)` under `Fun R`. The attack then
splits, and **neither branch closes**:

- **Consequent holds.** Every constant operator pure. In the full-QLN set,
  Exhaustion on each `K q` at `R` yields `q → □q` for all `q` — modal collapse.
  Striking, but not a contradiction: nothing in the axiom set asserts that any
  proposition is contingent, and under collapse the base camp's
  `pp_fundamental_forces_diagonal_nonnecessity` reduces to `Pure (K R)`, which
  *agrees* with this branch rather than refuting it.
- **Antecedent fails.** Then `◇¬Pure (K R)`, and the base camp independently
  gives `◇Pure (K R)`. Together: `Pure (K R)` is contingent. Consistent. Adding
  persistence turns this into `¬Pure (K R)`, still consistent with a possibility
  claim.

**The missing principle, named.** Both branches would close given a 5 or B
principle: `◇Pure (K R)` plus persistence would deliver `□Pure (K R)` and fire
Recombination. `Bacon_Modal` states K, T and 4 only; no 5 or B is stated or
derived anywhere in the development. **Whether CEV proves one is now the single
highest-value open question**, because it cuts both ways:

- if CEV proves 5, this refutation branch may close;
- and simultaneously the word-action model *fails* obligation item 2
  (`base_sound`), since `pp_sem_box` is S4 but not S5 — its `□`-images are
  up-closed under the accessibility order, and the complement of an up-closed
  set is not up-closed unless trivial.

One question, both programmes. It should be decided before more model-building.

**Scope of the negative result, stated so it is not oversold.** The search was
confined to type `Prop → Prop` operators built from `Pure` and the constant
builder. It did not try higher types, iterated `Pure`, or the
no-other-fundamentals schema, and used the unique-fundamentality axiom only as
the base camp already does. This is therefore **weak** evidence for consistency
and should not move the ~0.6 credence much — call it ~0.62.

## Step 2 follow-on: the named question, answered — and it is bad news

`frontier/Bacon_PP_Modal_Five.thy`. Step 2 named one question as highest-value:
does the background give a 5 principle? It is now settled on the semantic side,
and the answer is more drastic than expected.

```isabelle
modal_5 A = Imp (Neg (□A)) (□ (Neg (□A)))
applicative_structure.eval_ObjTrue
applicative_structure.modal_5_valid          (* no extra hypotheses *)
pp_sem_box_not_two_valued                    (* checked, not asserted *)
```

**5 is valid in every applicative structure**, from two of the locale's own
axioms. The reason is structural, not modal. `□A` abbreviates
`Eq Prop A ObjTrue`, and the evaluation clause is

```isabelle
eval ρ (Eq σ M N) = truth_den (eq_den σ (eval ρ M) (eval ρ N))
```

so every identity proposition — hence every `□` — denotes in the two-element
image of `truth_den`. `Neg` likewise. So `¬□A`, when true, denotes
`truth_den True`, and `eq_den_refl` makes `□(¬□A)` true. The modal fragment of
this semantics is not S4-with-extras; **`□` is two-valued**.

### Does CEV *prove* `modal_5`? The completeness results do NOT settle it

Checked against the sources. **No**, and for three separable reasons:

1. `CEV_completeness_from_countermodels` has exactly the right shape
   (`valid_in_context Γ A ⟹ Γ ⊢CEV A`) but is conditional on
   `CEV_countermodel_property`, which is **defined and never proved** anywhere
   in the repo. It is a hypothesis, not a theorem.
2. The two *unconditional* biconditionals — `CEV_clean_canonical_valid_iff_proves`
   and `CEV_clean_Henkin_valid_iff_proves` — are **syntactic**. "Valid" there
   means membership in every clean canonical world / Henkin theory, i.e. every
   maximal consistent set of formulas. They relate provability to
   maximal-consistent-set membership and cannot import a model-theoretic fact.
3. Nothing in `Bacon_Intended_Quotient` or `Bacon_Supported_Canonical` builds an
   `applicative_structure` from a Henkin theory.

So the link *valid in every applicative structure ⟹ CEV-provable* is exactly
what is missing. Nor does the `modal_4` route extend: `CEV_eq_truth_of_eq`
substitutes identicals into `F = λx. (M = x) = ⊤`, and substitution of
identicals needs a **positive** identity premise, whereas 5 supplies a negative
one. That is weak evidence 5 is *not* CEV-provable and that this semantics is
**incomplete** — validating more than CEV proves.

### Correction to the first version of this section

The first write-up of this result claimed `base_sound` **fails** for the word
action. That was wrong, and the error mattered, so it is recorded rather than
quietly fixed. `base_sound` is a hypothesis of the `henkin_action_model` locale
in `Bacon_PP_Axiom_Soundness`, and that locale has clauses for `Neg`, `Imp`,
`Forall`, `Exists` and `shift` but **no `Eq` clause**. It does not force
two-valued identity. What is actually shown is only that the word action is not
an `applicative_structure` with `pp_sem_box` interpreting `ObjBox`.

**The correct statement is conditional.** `pp_sem_box_refutes_five_pattern`
(checked) shows the word action refutes the 5 pattern outright — `pp_sem_box`
images are up-closed under left extension, complements are down-closed, and
boxing a down-closed proper subset gives `{}`. Hence:

> **If CEV proves 5, `base_sound` fails for the word action. If it does not,
> the word action survives this test.**

Likewise the refutation consequence is narrower than first stated: Codex's
S4-branching objection is refuted as an objection about *applicative-structure
modelhood*, but survives as an objection about *derivability*, since CEV is not
known to be complete for that class.

**Credence.** ~0.6 stands. The step-2 bump to ~0.62 is withdrawn (it rested on
the S4-countermodel picture). The plan is **not** re-scoped: the word-action
route is not closed, it is contingent on the 5 question.

### The one question that decides both

Does CEV prove `modal_5`? It must be settled by **finding a derivation, or a
clean Henkin theory `T` with `Neg (□A) ∈ T` and `□(Neg (□A)) ∉ T`** — not by the
completeness theorems. `CEV_supported_modal_successor` and
`CEV_identity_modal_successor` are the natural machinery for the countermodel
direction; note their `box_absent` hypothesis is the very thing at issue, so the
construction needs a handle on which boxes sit in a supported world.

## The Henkin countermodel to 5: built down to one lossless residue

`frontier/Bacon_PP_Five_Countermodel.thy`.

```isabelle
CEV_not_proves_modal_5_of_consistent_diagram
```

> Let `S` be a clean Henkin theory, `□A ∉ S`, and suppose
> `insert (□A) (CEV_identity_diagram Γ S)` is consistent (with a fresh-constant
> reserve). Then `¬ Γ ⊢CEV modal_5 A`.

Every modal step is discharged. The mechanism: `□X` *is* the identity
`Eq Prop X ObjTrue`, so `□X ∈ S` puts it in `CEV_identity_diagram Γ S`, which is
inherited by any Henkin theory extending the diagram. So 5 fails at `S` exactly
when some such extension makes `□A` true while `S` does not — **failure of
euclideanness**, "not necessary here, necessary at a successor."

**The residue is provably tight, not a convenient hypothesis.** By
`CEV_identity_diagram_derivable_implies_box_derivable`, inconsistency of
`insert (□A) (diagram Γ S)` means `diagram Γ S ⊢ ¬□A`, which yields
`□(¬□A) ∈ S` — i.e. *5 holding at S for A*. So the hypothesis is necessary as
well as sufficient: **the 5 question just is this consistency question.** The
reduction loses nothing.

**The premises are proved satisfiable** (`modal_5_reduction_premises_satisfiable`,
via `CEV_supported_counterworld` and a new `CEV_not_proves_box_const`). So the
reduction is not vacuous.

### Two corrections to the first version of this section

Both found by Codex, both confirmed against the sources.

1. **The first version of this theorem was vacuous.** It used the *full*
   identity diagram and required `CEV_fresh_extendible_base` of it. But
   reflexive identities `Eq Prop (Const c Prop) (Const c Prop)` are theorems,
   so they lie in every clean Henkin theory and its diagram; hence
   `CEV_identity_diagram_consts_UNIV` — **no constant is ever fresh for the
   full diagram**, and the premise is unsatisfiable. Repaired by moving to the
   `C`-supported diagram, where `UNIV - C` is an infinite reserve, and using
   `CEV_clean_Henkin_extension_from_block`.
2. **"The constant-substitution lemma is missing" was wrong.** It exists:
   `CEV_proves_subst_const` (`Bacon_Clean_Canonical_Base.thy:2438`) and
   `CEV_set_derivable_subst_const_clean` (`Bacon_Clean_Completeness.thy:785`).
   My earlier search reported no matches because the shell command errored on a
   zsh glob, which I misread as a negative result.

### The genericity route is closed, not merely unfinished

With substitution available, the obstruction is freshness, and it is structural.
Step `box_negbox_not_S` needs `□(¬□c)` to lie in the `C`-supported diagram,
forcing `c ∈ C`. Genericity needs `c` fresh for that same diagram, forcing
`c ∉ C`. Shrinking to `C' ⊆ C` with `c ∉ C'` restores freshness but drops
`□(¬□c)` from the diagram, breaking inheritance.

> **The diagram must mention `c` to transmit the modal fact, and must not
> mention `c` to be generic in it.**

So deciding the residue needs a different idea — a direct analysis of which
boxed formulas a supported diagram can derive, or a proof-theoretic argument
about CEV itself.

### Status, stated honestly

The countermodel is **not built**. What is built is a lossless reduction with
*satisfiable* premises, plus a proof that the obvious way of finishing cannot
work. The conditional from the previous section is unchanged: if CEV proves 5
then `base_sound` fails for the word action; if not, the word action survives.
Neither disjunct is established.

## AUDIT against Goodman's own notes, §2 (2026-07-25)

Source: `PP_project_notes` (Goodman, July 2026). These notes are the
**specification**; where the repo differs, the repo is wrong. Two divergences,
both material. Everything else matches.

### T₀ (core theory)

| §2 item | Repo | Verdict |
|---|---|---|
| H: tautologies, MP, Gen, UI, βη bidirectional at type t | `H_proves` PC/MP/Gen/UI/Beta/Eta (+EG, Inst, Ref, LL) | MATCH |
| Rule of Equivalence, **on open formulas** | `CE_proves.PropEquivalence`, stated in context `Γ` | MATCH |
| **Modalized Functionality** `□∀x(Xx = Yx) → X = Y` | — | **ABSENT** |
| `□ := (= ⊤)` | `ObjBox A = Eq Prop A ObjTrue` | MATCH |
| Purity schema (closed, only logical vocabulary) | `pp_purity_schema` (`consts_of M = {}`) | MATCH |
| Application closure | `pp_application_closure` | MATCH |
| Persistence (only where flagged) | `pp_persistence`, in flagged set only | MATCH |
| — | `C_proves`: BooleanIdentity, IdentityIdentity, Absorb/Dist Disj-Forall, Absorb/Dist Conj-Exists as primitive axioms | **RESOLVED — not extra** |

**`C_proves` resolved against Bacon–Dorr, *Classicism*, Figure 4.** The four
quantifier identities there — Absorption-∨∀, Distribution-∨∀, Absorption-∧∃,
Distribution-∧∃ — match the repo's exactly, and the text states: *"All of these
identities are easily seen to be instances of Logical Equivalence"* (with the
worked case for Absorption-∨∀), while Appendix A proves the converse, that they
recover the remaining instances. So Figure 4 and Logical Equivalence are
equivalent axiomatizations, and T₀'s Rule of Equivalence already yields the
whole stock. **The repo is not stronger than T₀ anywhere.**

Consequence: repo ⊊ T₀ strictly (weaker only, by MF). So **refutations do
transfer up cleanly**, and my mid-audit worry that they might not is withdrawn.
Consistency results still do not transfer down.

**H resolved against Bacon's book and the Classicism paper.** The book's
Definition 5.1 lists PC1–PC3, UI, β, η with MP and Gen; the Classicism paper
additionally treats Ref, LL and EG as H-axioms (*"the Absorption identities for
UI and EG, and the Identity Identity for Ref and LL"*), which is exactly the
repo's `H_proves`. Goodman's §2 gloss is abbreviated, not divergent. Also
matching: the book requires logics to be closed under the Rule of Substitution
for non-logical constants, which the repo has as `CEV_proves_subst_const`.

### Bacon's appendix model

| §2 item | Repo | Verdict |
|---|---|---|
| M = finite sequences under concatenation | `pp_word = nat list` | MATCH |
| `D_t = P(M)` | `pp_sem_prop = pp_word set` | MATCH |
| `i·p = {j : j∘i ∈ p}` | `pp_view i P = {j. j @ i ∈ P}` | MATCH |
| true iff contains the root | `pp_root_true P ⟷ [] ∈ P` | MATCH |
| function domains = maps respecting the action (Def 7.2) | `pp_function_space_member` | MATCH |
| invariant = fixed by every substitution | `pp_invariant_proposition`, `pp_fun_invariant` | MATCH |
| `Fun_t` = applies to denotations of the constants (just `r`) | `pp_fundamental_classifier r = {i. pp_view i P = r}` | MATCH |
| **`Pure_σ` = applies, at each substitution, to denotations of closed terms with no non-logical constants** | `pp_purity_operator F = {i. pp_fun_invariant (pp_fun_view i F)}` | **DIVERGES — invariance, not definability** |

### Divergence 1 is WITHDRAWN (checked against the Classicism PDF)

Reading Bacon–Dorr's *Classicism* directly overturns this. **Footnote 18 (p. 16):
"C includes Modalized Functionality (see §1.5)."** And §1.5 (p. 17) exhibits

> **Intensionality** `□∀z⃗(Xz⃗ ↔ Yz⃗) → X = Y`

and proves it is a **theorem of Classicism**, from the Logical Equivalence
instance `λz⃗.(Xz⃗ ∧ ∀z⃗.(Xz⃗ ↔ Yz⃗)) = λz⃗.(Yz⃗ ∧ ∀z⃗.(Xz⃗ ↔ Yz⃗))` plus Booleanism and
η-conversion. Intensionality has the *weaker* antecedent (`↔`, not `=`), so it is
stronger than MF; hence `C ⊢ MF`.

The bridge to this repo is p. 15: any H-theory closed under Propositional
Equivalence together with ξ or ζ is closed under Logical Equivalence. The repo
has both — `CE_proves.PropEquivalence` and `CEV_proves.VectorEquivalence`, whose
`zeta_body` *is* Bacon–Dorr's ζ-Equivalence. So repo-CEV contains Classicism,
proves Intensionality, and proves MF.

**Three things follow, all corrections to what I reported earlier:**

1. The repo's theory was **not weaker** than T₀. Both refutations and consistency
   results transfer.
2. My explanation of step 2's null result — that Goodman's liar was
   *inexpressible* because QSS and `fun′` were out of reach — is **withdrawn**.
   QSS is reachable. Step 2 found nothing because it searched too small a space.
3. `frontier/Bacon_PP_Modalized_Functionality.thy` is retained but re-framed: MF
   is a **derivation target**, not a missing axiom. Its `pp_T0_*` sets are
   expected to be deductively equivalent to the originals, and
   `pp_T0_consistency_implies_old` should have a converse.

**Next task, precisely.** Prove unary Intensionality in repo-CEV by the §1.5
route (instantiate ζ at `F := λz.(Xz ∧ ∀w.(Xw ↔ Yw))`, `G := λz.(Yz ∧ ∀w.(Xw ↔ Yw))`,
whose pointwise biconditional is an H-theorem; rewrite the shared conjunct to `⊤`
via `□A = (A = ⊤)`; discharge by the Boolean identity for `A ∧ ⊤`; finish with η).
Then MF follows since `Xz = Yz` gives `Xz ↔ Yz` by Ref and LL.

### Superseded: the original Divergence 1 write-up

The repo's `CEV_proves.VectorEquivalence` is *derivable* in T₀ (RoE on open
formulas → Gen → necessitation, available since `□A := A = ⊤` and RoE turns a
theorem `A` into `A = ⊤` → MF). The converse fails: **MF applies under
hypotheses; the rule is theorem-level only** — [Bacon_Zeta.thy:245](Bacon_Zeta.thy:245)
says so deliberately. So repo ⊊ T₀, strictly.

MF is exactly the identity-introduction principle QSS needs (concluding `X = Y`
from pointwise agreement, under hypotheses). No MF ⟹ no QSS ⟹ no `fun′` ⟹ the
T6 liar `D := λp.∀X∀q(Pure(X) ∧ fun′(q) ∧ p = Xq → ¬Xp)` is **inexpressible**.
That, not consistency, is why the step-2 refutation search found nothing.

### Divergence 2: the repo uses the invariance reading of purity

Goodman's M2 is titled "**The invariance reading of purity is not an option**":
identifying purity with invariance contradicts QSS given a fundamental
proposition; exotic invariant operators are unavoidable background structure,
and "the live question is only ever which invariants are *certified* pure."

The repo's `pp_purity_operator` is the invariance reading. Consequently
`pp_purity_of_pure_holds_in_word_action` — which proves
`pp_second_order_invariant pp_purity_operator`, correctly — does **not** show PP
holds in the word action. And Goodman's **M1 says PP fails at t→t in this very
model, necessarily so** (the model verifies Purity of Fun, QSS and a fundamental
proposition, so by Bacon's fn.-59 argument it cannot also verify PP there).
So the repo's interpretive claim is not merely unsupported, it is **false**.

Corroboration that the underlying model is right and only the reading is wrong:
M1 computes `Pure_t` at the bottom type as the non-contingency operator
`λp.(□p ∨ □¬p)`, and the repo's `pp_purity_of_meet` gives
`pp_purity_operator (λP. b ∩ P) = pp_decided b` with
`pp_decided X = □X ∪ □(−X)` — the same operator.

### Consequences for the record

- **Withdraw** the claim that PP holds in the word action. It contradicts M1.
- **Withdraw** all consistency credences (~0.55, ~0.40–0.45). They concern a
  theory strictly weaker than T₀ in one respect and possibly stronger in
  another (the `C_proves` axiom stock), so **neither** refutations **nor**
  consistency results transfer cleanly until the `C` question is resolved.
- Step 2's null result is **not** evidence for consistency; it is evidence the
  formalized theory is too weak to state the argument.
- A sweep is needed of every result depending on the invariance reading.

## Agreed next steps (consensus review, 2026-07-25)

Ranked. Full reasoning in `reports/PP_consensus_stocktaking_2026-07-25.md`.

1. **Axiom-extension Henkin soundness interface.** A typed Henkin action-model
   interface with *denotable* (not full) function spaces, plus the conditional
   theorem *global validity of every member of `T` implies axiom-extension
   consistency for `T`*, stated for the complete axiom set. Not a model
   construction --- strictly the contract. Medium, 2--4 weeks. Fixes what every
   downstream result must meet, and stops root-level results being mistaken for
   consistency evidence.

2. **Time-boxed refutation attack in CEV+.** Look for a finite inconsistent core
   from the target PP instance, application closure, necessitated Recombination
   and unique fundamentality, using the existing `Bacon_PP_Diagonal` derivations
   as base camp. First attention to the argument-under-`Pure` seam --- the one
   place the unrealizability shield does not reach --- but the search must be
   broad across the four principles jointly. Medium, 3--4 weeks, sharply
   time-boxable. A refutation settles everything; a mapped-out failure closes the
   seam and legitimately raises the consistency credence.

3. **All-worlds fixed-`Fun` self-classifying core.** A countable typed stock and
   one contingent `r` such that at *every* world, for every *locally* pure member
   of the `Prop->Prop` domain, Recombination holds with `Fun = \P. Id(P, r)`
   throughout. The live risk is **entanglement**, not counting: prescribing a
   cone of `r` constrains every tail view through it, so requirements at
   different worlds are no longer independent, which is what breaks the old
   no-injury argument. Confront that first. High to very high.

4. **All-type relational evaluator and `Lam`/`App` closure.** A type-indexed
   interpretation relation over an *untyped applicative structure*, with object
   types interpreted as PERs by plain recursion --- no datatype, hence no ceiling.
   Acceptance criteria: an operator closure with an application rule covering
   argument-under-`Pure` (or an explicit counterexample to the corresponding
   decidedness-preservation lemma), and all-type discharge of the
   no-other-fundamentals schema. High. Upgrades several results to their billed
   strength.

5. **One-week cross-class calibration probe.** Test the package in one
   structurally different arena --- e.g. a Fraenkel--Mostowski group action with
   finite supports, where purity is empty support --- asking only whether the same
   self-classification knot reappears. Strictly diagnostic. Low to medium.
   Settles whether the tree action deserves the remaining months.

## Goodman object-language verification update (2026-07-25, T7a)

`frontier/Bacon_PP_Goodman_T7_Absorption.thy` now machine-proves the
absorption theorem. With `D` Goodman's liar, `d = D(r)`, and
`a_Z = D(Zd)`, the exact stock

```
pp_T7_full_axioms =
  {pp_exists_fun_prime, pp_L2} ∪ pp_T6_core_PP_axioms
```

derives the closed result saying that some `fun′` witness `r` satisfies both
`¬a_id` and `∃Z(G Z ∧ a_Z)`. The decisive exported theorems are
`CEV_Goodman_T7a_parameter` and `CEV_Goodman_T7a`.

The proof does not assume Inv, WI, TU, RS, QLN, Recombination, Exhaustion,
fundamentality, Persistence, or Purity of Fun. It:

1. obtains `¬D(D r)` from the checked T5 diagonal refutation;
2. uses classical quantifier duality to extract pure `X` and `fun′ q` with
   `D r = X q` and `X(D r)`;
3. applies weak L2 to obtain `X = D ∘ Z` for some `Z ∈ G`;
4. transports `X(D r)` to `D(Z(D r))`; and
5. eliminates `X`, `q`, `Z`, and the original `r` witness inside CEV+.

The complete Isabelle session clean-builds, and the new theory contains no
proof escape. The consolidated Claude audit remains deferred until T7b and
T8 are complete.

## Goodman object-language verification update (2026-07-25, T8 encoding/T8b)

`frontier/Bacon_PP_Goodman_T8_Encoding.thy` fixes a literal finite target for
T8. It defines the advertised five base operators (`id`, necessity,
possibility, constant true, constant false), enumerates their 31 nonempty
subsets, builds the corresponding kind properties, and renders both
pairwise-distinctness claims as object-language formulas. Isabelle proves
that each list has length 31 and that the complete growth claim is typed.
These are encoding certificates, not yet the T8c derivation.

`frontier/Bacon_PP_Goodman_T8_Kind_Uniqueness.thy` machine-proves T8b.
`CEV_Goodman_T8_kind_uniqueness` says that if one proposition has
representations `p = X(q)` and `p = Y(s)`, where `X,Y` are pure and `q,s`
are `fun′`, then `X ≈ Y`. The proof uses only equality transport and the
literal weak-L2 axiom instance.

## Goodman object-language verification update (2026-07-26, T8c and scope closure)

`frontier/Bacon_PP_Goodman_T8_Growth.thy` now machine-proves T8c.
`CEV_Goodman_T8c` proves that any `fun′` witness yields the literal
pairwise-distinctness formulas for the 31 generated pure unary operators and
their 31 values. `CEV_Goodman_T8c_closed` object-linguistically eliminates
the witness and proves the closed existential `pp_T8_growth_result` from

```
pp_T8_full_axioms =
  {pp_exists_fun_prime, pp_L2} ∪ pp_T6_core_PP_axioms.
```

The crucial purity step does not silently classify the generated formulas as
constant-free: each contains `Pure` through `fun′`. The proof abstracts that
constant, applies the purity schema to the resulting closed builder, uses PP
to make the purity predicate pure, applies application closure, beta-converts,
and transports purity across equality. For subset separation, a base kind in
the symmetric difference supplies a realizing proposition. T8b plus the ten
T8a base-kind separations refute every representation by an omitted base
kind. This yields all operator inequalities, and `fun′` functionality lifts
them to the 31 value inequalities.

T7b is not a determinate formal target in the supplied source. Page 4 of
Goodman's PDF contains only the prose sentence that the
“diagonal-on-kinds likewise has no fixed point but a shifted one.” It supplies
no diagonal term, definitions of fixed and shifted point, binders, or exact
stock beyond PP at `(t→t)→t`. Any current encoding would therefore be a new
conjectural reconstruction, not verification of Goodman's theorem. T9 is
explicitly advertised as meta-level cardinal counting. Thus the precise
object-language suite is closed: every determinate target is now
machine-checked or, for T3, has its exact advertised gap and repaired
theorems recorded. The next step is the single consolidated Claude
adversarial audit requested after completion.

## Consolidated Goodman audit and repair (2026-07-26)

The single consolidated adversarial audit of T1--T8 returned **PASS WITH
QUALIFICATIONS**. It checked the exact stocks, binders, theorem/local
boundaries, witness eliminations, and exported theorem objects. Every
principal theorem except the two T8c exports was initially oracle-free with
no hypotheses or flex-flex constraints. The two T8c exports inherited one
`Code_Generator.holds_by_evaluation` oracle from each of two finite-list
distinctness lemmas proved by `eval`.

Both `eval` proofs have now been removed. Nonempty subsequences are proved
distinct from `distinct_set_subseqs`; generated kind properties are proved
injective by decoding the right-associated disjunction syntax and using
injectivity of the kind atoms. A focused post-repair session checks
`CEV_Goodman_T8c` and `CEV_Goodman_T8c_closed` and fails unless each has zero
oracles, zero undischarged hypotheses, and zero flex-flex constraints. The
post-repair check passes.

The audit's purported second finding was an audit error, not a repository
defect. `CEV_Goodman_T3_heredity_with_exhaustion` exists in
`Bacon_PP_Goodman_Heredity_Exhaustion.thy` as the corollary over
`insert pp_zeroary_exhaustion pp_T3_axioms`.
`CEV_Goodman_T3_heredity_min` is the sharper underlying theorem over the
smaller stock `pp_T3_min_axioms`; it does not make the corollary's name stale.

The substantive qualifications remain. T3's advertised premise list has a
modal gap; T7b is not uniquely formalizable from Goodman's one prose
sentence; T9 is a meta-level cardinal argument. Most importantly, T6 proves
only conditional contradictions: PP plus L2 and Inv/WI/TU, or PP plus
strong-L2 and RS. It does not prove PP alone inconsistent. Semantic
consistency and non-vacuity of the complete PP stock remain open, as does a
fully internal equivalence theorem between repository CEV and Goodman's
presentation of `T0`.

The natural next verification phase is model-theoretic. Goodman's M-claims
can be given a matrix parallel to T1--T9, using the existing substitution
word-action infrastructure and the definability reading of purity. The
highest-value targets for the eventual consistency problem are the semantic
status of L2 and the structure of the pure reversible group `G`.

## Goodman T6-WI master derivation (2026-07-26)

`frontier/Bacon_PP_Goodman_T6_WI_Master.thy` now derives Goodman's exact
advertised WI master claim directly from the stated T6-WI stock.  This closes
the route-specific gap previously hidden by the independently verified
inconsistency of that stock.

The proof is explicitly non-explosive:

1. `CEV_T6_WI_master_forward` derives the left-to-right implication from the
   liar matrix and the core PP principles.
2. `CEV_T6_WI_master_reverse` derives the right-to-left implication using WI,
   L2, and the pure reversible-group reindexing argument.
3. `CEV_T6_WI_master_at_direct` and
   `CEV_T6_WI_master_family_direct` combine and quantify those directions.
4. `CEV_T6_WI_rhs_operator_equiv` transports the direct formula through the
   beta-equivalent lambda encoding of Goodman's proposition-indexed operator.
5. `CEV_T6_WI_advertised_master_direct` proves the guarded advertised family,
   and `CEV_Goodman_T6_WI_advertised_master_claim_direct` proves the exact
   closed quantified claim from `pp_T6_WI_axioms`.

The older theorem
`CEV_Goodman_T6_WI_advertised_master_claim_ex_falso` is retained under its
explicit name as a logically valid but methodologically weaker comparison.
Both the Frontier and Models sessions build, `git diff --check` passes, and
the theory contains no proof escape.

## T3 semantic calibration (2026-07-26)

`pp/Bacon_PP_Heredity_Semantics.thy` now proves the model-side heredity result
that was previously only asserted in Goodman's M4 discussion.  For an
arbitrary certified stock of proposition operators, define `fun′` as
injectivity of evaluation on that stock.  If:

1. every substitution-view of the fundamental witness satisfies that
   injectivity condition (the semantic form of necessitated QSS);
2. each certified operator belongs to Bacon's unary function space and is
   fixed by every substitution; and
3. some substitution makes `p` play the same role as the fundamental witness,

then `p` is `fun′` at the root.  The exported theorems are
`pp_stock_fun_prime_hereditary` and its equivariant corollary
`pp_stock_fun_prime_hereditary_equivariant`.

This result does not repair the advertised CEV+ derivation.  It explains why
the claim is valid in the intended substitution semantics while the stated
object-language assumptions prove only possible operator identity:
Persistence preserves the applicability of `Pure`; the semantic proof needs
the stronger fact that the pure operators themselves are substitution-fixed.

The theory now also proves the sharp converse model obligation
`pp_failed_heredity_requires_noninvariant_pure_pair`.  Any failed heredity
instance supplies distinct certified operators `F,G` agreeing at the proposed
counterexample, and at least one of `F,G` must be substitution-noninvariant.
Thus a full countermodel to the advertised T3 stock cannot use Bacon's
intended interpretation of purity by closed pure denotations: it must certify
an exotic noninvariant operator as pure.  This isolates the remaining
countermodel burden without claiming that the unbounded PP and purity schemas
have already been modeled.

## Goodman M1--M7 completion (2026-07-27)

The determinate M-claims are now machine-checked.

- **M1:** `Bacon_PP_Goodman_M1_Complete.thy` defines Goodman's exact
  footnote-59 operator
  `D p ↔ ∀X q. Pure(X) ∧ Fun(q) ∧ p = X q → ¬X p`, proves its typing,
  constructs a closed constant-free builder by abstracting `Pure` and `Fun`,
  checks the two beta contractions, derives the liar's purity from PP, Purity
  of Fun, and application closure, and proves the contradiction from QSS plus
  unique proposition-level fundamentality.
- **M3:** `Bacon_PP_Goodman_M3_Complete.thy` proves that every countable
  invariant Boolean stock has a free, hence `fun′`, generator by branch
  gluing. It also states the exact finite-cylinder product topology, proves
  each necessary-cone class nowhere dense, and proves the complete `fun′`
  class meager.
- **M5:** `Bacon_PP_ZF_Bacon_10_1.thy` formalizes the rebuilt-model gluing
  theorem. `Bacon_PP_ZF_Goodman_M5_Rebuild.thy` applies it while holding the
  exotic cone-natural unary operator fixed, discharging the rebuilding step
  rather than leaving it conditional on Theorem 10.1.
- **M6:** `Bacon_PP_Goodman_M6.thy` proves separation of every pair of
  distinct substitutions by a `fun′` proposition, failure of one-coordinate
  orbit-diagonal independence, and a strict pair of `fun′` propositions whose
  inclusion blocks a joint assignment at every view.
- **M7:** `Bacon_PP_ZF_Goodman_M7.thy` constructs the branch diagonal against
  any countable exact closed unary stock and proves that no such stock can
  exhaust the reachable unary proposition domain.

Together with the earlier M2 and M4 theories, this closes the precise M1--M7
verification suite. `isabelle build -D . -o timeout=60` passes for both the
Frontier and HOL-ZF sessions. A single consolidated adversarial audit of this
completed suite is the next checkpoint; it should scrutinize theorem scope,
especially the distinction between exact closed-term stocks and broader
semantic domains.

## Semantic L2 in Bacon's exact tree model (2026-07-27)

`zf_model/Bacon_PP_ZF_Goodman_L2_Model.thy` now gives a direct semantic
formalization of Goodman's L2 over the exact Boolean stock induced by closed,
constant-free object-language unary terms.

The theory checks:

- the exact semantic predicates `fun′`, reversible operator, `G`, same kind,
  pairwise L2, and global L2;
- existence of an exact-stock `fun′` proposition from the generic-separator
  theorem;
- closure of the exact stock under object-language composition;
- closure of `G` under identity, inverse, and composition, and equivalence of
  the induced same-kind relation;
- exact denotations of identity, truth, falsity, necessity, possibility, and
  complement;
- the modal fixed-point restrictions on `fun′`, plus the stronger extreme-view
  facts `□p \neq \bot` and `◇p \neq \top` for every exact-stock `fun′` input;
- collision classification for all twenty-five ordered pairs among identity,
  truth, falsity, necessity, and possibility; hence semantic L2 on this entire
  five-operator base stock; and
- the exact counterexample criterion
  `¬L2 ↔ ∃X Y p q. pp_b_exact_L2_counterexample X Y p q`.

This is a strict partial result, not a global proof of L2. Any remaining
counterexample must involve at least one exact closed logical operator outside
the five-operator base. The next semantic attack should therefore enlarge the
classified stock by closure under complement and composition, beginning with
the modal Boolean fragment, and seek either a general normal-form separation
argument or the first cross-input collision between inequivalent normal forms.
