from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .axioms import AxiomEntry, Bounds
from .terms import (
    Conj,
    Eq,
    Forall,
    Imp,
    Neg,
    OBJ_FALSE,
    OBJ_TRUE,
    PROP,
    Term,
    Type,
    infer_type,
    priority_logical_terms,
    subst0,
)


@dataclass(frozen=True)
class ProofNode:
    conclusion: Term
    rule: str
    premises: tuple[Term, ...] = ()
    axiom_id: str | None = None
    witness: Term | None = None
    support: frozenset[str] = frozenset()

    def as_json(self) -> dict[str, object]:
        return {
            "conclusion": self.conclusion.isabelle(),
            "conclusion_compact": self.conclusion.compact(),
            "rule": self.rule,
            "premises": [p.isabelle() for p in self.premises],
            "axiom_id": self.axiom_id,
            "witness": self.witness.isabelle() if self.witness else None,
            "support": sorted(self.support),
        }


@dataclass
class SearchResult:
    found: bool
    proofs: dict[Term, ProofNode]
    rounds_completed: int
    saturated: bool
    node_cap_hit: bool

    @property
    def false_proof(self) -> ProofNode | None:
        return self.proofs.get(OBJ_FALSE)

    @property
    def support(self) -> frozenset[str]:
        proof = self.false_proof
        return proof.support if proof else frozenset()

    def proof_dag(self) -> list[ProofNode]:
        if not self.found:
            return []
        return self.proof_dag_for(OBJ_FALSE)

    def proof_dag_for(self, target: Term) -> list[ProofNode]:
        if target not in self.proofs:
            return []
        ordered: list[ProofNode] = []
        seen: set[Term] = set()

        def visit(term: Term) -> None:
            if term in seen:
                return
            node = self.proofs[term]
            for premise in node.premises:
                visit(premise)
            seen.add(term)
            ordered.append(node)

        visit(target)
        return ordered


def _closed_subterms(term: Term) -> set[tuple[Term, Type]]:
    result: set[tuple[Term, Type]] = set()

    def walk(current: Term) -> None:
        ty = infer_type((), current)
        if ty is not None:
            result.add((current, ty))
        for arg in current.args:
            if isinstance(arg, Term):
                walk(arg)

    walk(term)
    return result


def _better(new: ProofNode, old: ProofNode) -> bool:
    return (len(new.support), new.rule, new.conclusion.nodes) < (
        len(old.support),
        old.rule,
        old.conclusion.nodes,
    )


def saturate(
    pool: list[AxiomEntry],
    bounds: Bounds,
    seed_terms: Iterable[tuple[Term, Type]] = (),
) -> SearchResult:
    proofs: dict[Term, ProofNode] = {}
    id_to_axiom = {axiom.stable_id: axiom for axiom in pool}

    def add(node: ProofNode) -> bool:
        if infer_type((), node.conclusion) != PROP:
            raise AssertionError(
                f"search produced ill-typed formula: {node.conclusion.compact()}"
            )
        old = proofs.get(node.conclusion)
        if old is None or _better(node, old):
            proofs[node.conclusion] = node
            return True
        return False

    for axiom in pool:
        add(
            ProofNode(
                axiom.formula,
                "axiom",
                axiom_id=axiom.stable_id,
                support=frozenset({axiom.stable_id}),
            )
        )

    add(ProofNode(OBJ_TRUE, "obj_true"))

    closed_terms: set[tuple[Term, Type]] = set()
    for term, ty in seed_terms:
        if infer_type((), term) != ty:
            raise ValueError(
                f"ill-typed seed term {term.compact()} at {ty.short()}"
            )
        closed_terms.add((term, ty))
    for _, term in priority_logical_terms():
        ty = infer_type((), term)
        assert ty is not None
        closed_terms.add((term, ty))
    for axiom in pool:
        closed_terms.update(_closed_subterms(axiom.formula))

    # Reflexivity is a base theorem of H.  The cap avoids spending an entire
    # initial tranche on large schema subterms.
    ref_terms = sorted(
        closed_terms,
        key=lambda pair: (pair[0].nodes, pair[1].nodes, pair[0].compact()),
    )[: min(bounds.node_cap // 4, 5000)]
    for term, ty in ref_terms:
        add(ProofNode(Eq(ty, term, term), "ref", witness=term))

    node_cap_hit = False
    for round_number in range(1, bounds.rounds + 1):
        before = len(proofs)
        snapshot = list(proofs.values())

        for node in snapshot:
            formula = node.conclusion
            if formula.tag == "Conj":
                left, right = formula.args
                add(
                    ProofNode(
                        left,
                        "conj_left",
                        (formula,),
                        support=node.support,
                    )
                )
                add(
                    ProofNode(
                        right,
                        "conj_right",
                        (formula,),
                        support=node.support,
                    )
                )
            if formula.tag == "Neg" and formula.args[0].tag == "Neg":
                inner = formula.args[0].args[0]
                add(
                    ProofNode(
                        inner,
                        "double_negation",
                        (formula,),
                        support=node.support,
                    )
                )
            if formula.tag == "Forall":
                sigma, body = formula.args
                for witness, witness_ty in closed_terms:
                    if witness_ty != sigma:
                        continue
                    instance = subst0(witness, body)
                    add(
                        ProofNode(
                            instance,
                            "forall_elim",
                            (formula,),
                            witness=witness,
                            support=node.support,
                        )
                    )

        snapshot_map = dict(proofs)
        implications: dict[Term, list[tuple[Term, ProofNode]]] = {}
        for formula, node in snapshot_map.items():
            if formula.tag == "Imp":
                antecedent, consequent = formula.args
                implications.setdefault(antecedent, []).append(
                    (consequent, node)
                )
        # Introduce only conjunctions that are active antecedents.  This
        # supplies the premises of application closure without generating
        # the quadratic set of all conjunctions of proved formulas.
        for antecedent in implications:
            if antecedent.tag != "Conj":
                continue
            left, right = antecedent.args
            left_node = snapshot_map.get(left)
            right_node = snapshot_map.get(right)
            if left_node is not None and right_node is not None:
                add(
                    ProofNode(
                        antecedent,
                        "conj_intro",
                        (left, right),
                        support=left_node.support | right_node.support,
                    )
                )
        for antecedent, antecedent_node in list(snapshot_map.items()):
            for consequent, implication_node in implications.get(
                antecedent, []
            ):
                implication = Imp(antecedent, consequent)
                add(
                    ProofNode(
                        consequent,
                        "mp",
                        (antecedent, implication),
                        support=(
                            antecedent_node.support
                            | implication_node.support
                        ),
                    )
                )

        # A proved pair of converse implications yields the displayed
        # biconditional needed by zeroary/vector Equivalence.
        implication_nodes = [
            (formula, node)
            for formula, node in list(proofs.items())
            if formula.tag == "Imp"
        ]
        implication_lookup = {formula: node for formula, node in implication_nodes}
        for formula, node in implication_nodes:
            left, right = formula.args
            converse = Imp(right, left)
            converse_node = implication_lookup.get(converse)
            if converse_node is not None:
                add(
                    ProofNode(
                        Conj(formula, converse),
                        "conj_intro",
                        (formula, converse),
                        support=node.support | converse_node.support,
                    )
                )

        # The zeroary case of vector Equivalence.
        for formula, node in list(proofs.items()):
            if (
                formula.tag == "Conj"
                and formula.args[0].tag == "Imp"
                and formula.args[1].tag == "Imp"
            ):
                left_imp, right_imp = formula.args
                left, right = left_imp.args
                if right_imp.args == (right, left):
                    add(
                        ProofNode(
                            Eq(PROP, left, right),
                            "prop_equivalence",
                            (formula,),
                            support=node.support,
                        )
                    )

        for formula, node in list(proofs.items()):
            negated = Neg(formula)
            neg_node = proofs.get(negated)
            if neg_node is not None:
                add(
                    ProofNode(
                        OBJ_FALSE,
                        "contradiction",
                        (formula, negated),
                        support=node.support | neg_node.support,
                    )
                )

        if OBJ_FALSE in proofs:
            return SearchResult(True, proofs, round_number, False, False)
        if len(proofs) >= bounds.node_cap:
            node_cap_hit = True
            return SearchResult(
                False, proofs, round_number, False, node_cap_hit
            )
        if len(proofs) == before:
            return SearchResult(False, proofs, round_number, True, False)

    return SearchResult(False, proofs, bounds.rounds, False, node_cap_hit)


def minimize_support(
    pool: list[AxiomEntry],
    result: SearchResult,
    bounds: Bounds,
    seed_terms: Iterable[tuple[Term, Type]] = (),
) -> tuple[list[AxiomEntry], SearchResult]:
    if not result.found:
        return [], result
    by_id = {axiom.stable_id: axiom for axiom in pool}
    core_ids = list(sorted(result.support))
    current_result = result
    for candidate in list(core_ids):
        trial_ids = [axiom_id for axiom_id in core_ids if axiom_id != candidate]
        trial_pool = [by_id[axiom_id] for axiom_id in trial_ids]
        trial_result = saturate(trial_pool, bounds, seed_terms)
        if trial_result.found:
            core_ids = trial_ids
            current_result = trial_result
    return [by_id[axiom_id] for axiom_id in core_ids], current_result


def validate_result(
    pool: Iterable[AxiomEntry], result: SearchResult
) -> None:
    ids = {axiom.stable_id for axiom in pool}
    for node in result.proofs.values():
        if not node.support <= ids:
            raise AssertionError("proof support contains an unknown axiom")
        for premise in node.premises:
            if premise not in result.proofs:
                raise AssertionError("proof DAG has a missing premise")
