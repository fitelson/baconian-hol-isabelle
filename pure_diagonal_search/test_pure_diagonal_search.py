from __future__ import annotations

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from finite_core_search.axioms import Bounds, Profile
from finite_core_search.prover import saturate, validate_result
from finite_core_search.terms import Eq, Lam, PROP, Var, infer_type, pp_pure

from pure_diagonal_search.candidates import (
    BUILDER,
    CLASSIFIER,
    UNARY,
    beta_normalize,
    classifier_uses,
    enumerate_candidates,
)
from pure_diagonal_search.replay import emit_purity_audit
from pure_diagonal_search.run_search import (
    candidate_pool,
    candidate_seed_terms,
)


class PureDiagonalSearchTests(unittest.TestCase):
    def setUp(self) -> None:
        self.candidates = list(
            enumerate_candidates(
                max_builder_size=6,
                per_cell_cap=0,
                classifier_occurrences=1,
                maximum_classifier_quantifier_depth=0,
            )
        )

    def test_priority_and_generated_candidates_are_typed(self) -> None:
        self.assertTrue(self.candidates)
        self.assertIn(
            "diagonal_builder",
            {candidate.name for candidate in self.candidates},
        )
        self.assertTrue(
            any(candidate.source == "generated" for candidate in self.candidates)
        )
        for candidate in self.candidates:
            self.assertEqual(infer_type((), candidate.builder), BUILDER)
            self.assertEqual(infer_type((), candidate.diagonal), UNARY)
            self.assertEqual(infer_type((), candidate.normal_form), UNARY)

    def test_generated_tranche_obeys_structural_filters(self) -> None:
        for candidate in self.candidates:
            if candidate.source != "generated":
                continue
            self.assertEqual(len(candidate.uses), 1)
            self.assertEqual(
                max(use.quantifier_depth for use in candidate.uses),
                0,
            )

    def test_classifier_occurrences_need_not_be_applications(self) -> None:
        builder = Lam(
            CLASSIFIER,
            Lam(PROP, Eq(CLASSIFIER, Var(1), Var(1))),
        )
        uses = classifier_uses(builder)
        self.assertEqual(len(uses), 2)
        self.assertTrue(all(use.argument is None for use in uses))

    def test_beta_normalization_removes_outer_redex(self) -> None:
        candidate = next(
            value
            for value in self.candidates
            if value.name == "diagonal_builder"
        )
        normalized = beta_normalize(candidate.diagonal)
        self.assertNotEqual(normalized.tag, "App")
        self.assertEqual(infer_type((), normalized), UNARY)

    def test_reference_saturator_derives_candidate_purity(self) -> None:
        candidate = next(
            value
            for value in self.candidates
            if value.name == "diagonal_builder"
        )
        bounds = Bounds(
            type_depth=1,
            term_size=2,
            term_cell_cap=0,
            rounds=8,
            node_cap=20000,
        )
        pool, _ = candidate_pool(
            Profile.CENTRAL_RECOMBINATION, bounds, candidate
        )
        result = saturate(pool, bounds, candidate_seed_terms(candidate))
        validate_result(pool, result)
        self.assertIn(pp_pure(UNARY, candidate.diagonal), result.proofs)

    def test_generated_audit_uses_verified_generic_theorem(self) -> None:
        with TemporaryDirectory() as directory:
            theory, root = emit_purity_audit(
                Path(directory),
                Profile.CENTRAL_RECOMBINATION,
                self.candidates[:2],
            )
            text = theory.read_text()
            root_text = root.read_text()
        self.assertIn(
            "finite_core_pure_logical_builder_application", text
        )
        self.assertIn("PURE-DIAGONAL-AUDIT-CLEAN", text)
        self.assertNotIn("sorry", text.lower())
        self.assertIn("Goodman_Pure_Diagonal_Audit", root_text)


if __name__ == "__main__":
    unittest.main()
