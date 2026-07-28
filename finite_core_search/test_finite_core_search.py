from __future__ import annotations

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from finite_core_search.axioms import (
    Bounds,
    Profile,
    bounded_axiom_pool,
    entry,
)
from finite_core_search.coverage import (
    boolean_identities,
    classicist_identities,
    compatible_beta_contracts,
    compatible_eta_contracts,
)
from finite_core_search.context_c_input import (
    HEADER as CONTEXT_HEADER,
    MAGIC as CONTEXT_MAGIC,
    emit_context_c_input,
)
from finite_core_search.prover import saturate, validate_result
from finite_core_search.schematic_vampire import emit_schematic_problem
from finite_core_search.terms import (
    OBJ_FALSE,
    PROP,
    const_names,
    infer_type,
    priority_logical_terms,
    type_universe,
)
from finite_core_search.vampire import build_ground_graph


class FiniteCoreSearchTests(unittest.TestCase):
    def test_depth_three_has_1446_types(self) -> None:
        types = type_universe(3)
        self.assertEqual(len(types), 1446)
        self.assertTrue(all(ty.depth <= 3 for ty in types))

    def test_priority_terms_are_closed_logical_and_typed(self) -> None:
        names = set()
        for name, term in priority_logical_terms():
            self.assertNotIn(name, names)
            names.add(name)
            self.assertIsNotNone(infer_type((), term), name)
            self.assertEqual(const_names(term), frozenset(), name)
        for required in {
            "identity",
            "negation",
            "constant_truth",
            "constant_falsity",
            "diagonal_builder",
            "positive_diagonal_builder",
            "HO_child_xor",
            "T4_diagonal_builder",
            "T6_purity_builder",
            "fn59_diagonal_builder",
            "RS_diagonal_builder",
        }:
            self.assertIn(required, names)

    def test_strict_depth_one_pool_respects_depth_and_size(self) -> None:
        bounds = Bounds(
            type_depth=1,
            type_budget=0,
            term_size=3,
            term_cell_cap=0,
            rounds=2,
            node_cap=5000,
        )
        pool, metadata = bounded_axiom_pool(
            Profile.CENTRAL_RECOMBINATION, bounds
        )
        self.assertEqual(metadata["selected_type_count"], 6)
        self.assertTrue(metadata["exhaustive_at_displayed_syntactic_bounds"])
        purity = [axiom for axiom in pool if axiom.family == "purity"]
        self.assertTrue(purity)
        self.assertTrue(
            all(
                axiom.source_type is not None
                and axiom.source_type.depth <= 1
                and axiom.formula.args[1].nodes <= 3
                for axiom in purity
            )
        )

    def test_first_priority_tranche_has_four_named_diagonals(self) -> None:
        bounds = Bounds(
            type_depth=1,
            type_budget=0,
            term_size=2,
            term_cell_cap=0,
            priority_extensions=True,
        )
        pool, metadata = bounded_axiom_pool(
            Profile.CENTRAL_RECOMBINATION, bounds
        )
        sources = {
            axiom.source
            for axiom in pool
            if axiom.family == "purity"
            and axiom.source.startswith("priority_")
        }
        self.assertEqual(
            sources,
            {
                "priority_T4_diagonal_builder",
                "priority_T6_purity_builder",
                "priority_fn59_diagonal_builder",
                "priority_RS_diagonal_builder",
            },
        )
        self.assertFalse(metadata["exhaustive_at_displayed_syntactic_bounds"])
        graph = build_ground_graph(pool, bounds)
        self.assertIn(OBJ_FALSE, graph.formulas)
        self.assertTrue(graph.rules)

    def test_small_pools_are_well_typed(self) -> None:
        bounds = Bounds(
            type_depth=3,
            type_budget=6,
            term_size=2,
            term_cell_cap=30,
            rounds=2,
            node_cap=5000,
        )
        for profile in Profile:
            pool, metadata = bounded_axiom_pool(profile, bounds)
            self.assertEqual(metadata["complete_type_universe_count"], 1446)
            self.assertGreater(len(pool), 0)
            self.assertTrue(
                all(infer_type((), axiom.formula) == PROP for axiom in pool)
            )

    def test_synthetic_false_is_only_a_search_hit(self) -> None:
        synthetic = [
            entry(
                "synthetic_test_only",
                OBJ_FALSE,
                "not a Goodman axiom",
            )
        ]
        bounds = Bounds(rounds=1, node_cap=100)
        result = saturate(synthetic, bounds)
        validate_result(synthetic, result)
        self.assertTrue(result.found)
        self.assertEqual(
            result.support,
            frozenset({synthetic[0].stable_id}),
        )

    def test_schematic_problem_has_guarded_ui_and_positive_target(self) -> None:
        bounds = Bounds(
            type_depth=1,
            type_budget=0,
            term_size=2,
            term_cell_cap=0,
            priority_extensions=True,
        )
        with TemporaryDirectory() as directory:
            root = Path(directory)
            problem = root / "schematic.tff.in"
            metadata = emit_schematic_problem(
                problem,
                root / "manifest.json",
                Profile.CENTRAL_RECOMBINATION,
                bounds,
            )
            text = problem.read_text()
        self.assertEqual(metadata["ui_templates"], 82)
        self.assertIn("witness(", text)
        self.assertIn("derive_objfalse,conjecture,derived(", text)
        self.assertNotIn("conjecture,$false", text)

    def test_added_cev_base_instances_are_typed(self) -> None:
        for identity in boolean_identities():
            self.assertEqual(infer_type((), identity), PROP)
        for ty in type_universe(1):
            for identity in classicist_identities(ty):
                self.assertEqual(infer_type((), identity), PROP)

    def test_compatible_beta_eta_contractions_preserve_prop_type(self) -> None:
        for _, term in priority_logical_terms():
            if infer_type((), term) != PROP:
                continue
            for reduct in compatible_beta_contracts(term):
                self.assertEqual(infer_type((), reduct), PROP)
            for reduct in compatible_eta_contracts(term):
                self.assertEqual(infer_type((), reduct), PROP)

    def test_context_c_input_has_all_singleton_contexts(self) -> None:
        bounds = Bounds(
            type_depth=1,
            type_budget=0,
            term_size=2,
            term_cell_cap=0,
            context_depth=1,
            priority_extensions=True,
        )
        with TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "input.bin"
            metadata = emit_context_c_input(
                binary,
                root / "input.json",
                Profile.CENTRAL_RECOMBINATION,
                bounds,
            )
            header = CONTEXT_HEADER.unpack(
                binary.read_bytes()[: CONTEXT_HEADER.size]
            )
        self.assertEqual(header[0], CONTEXT_MAGIC)
        self.assertEqual(header[3], 7)
        self.assertEqual(len(metadata["selected_types"]), 6)
        self.assertGreater(metadata["eg_edges"], 0)


if __name__ == "__main__":
    unittest.main()
