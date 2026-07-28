from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess

from .axioms import AxiomEntry, Bounds
from .terms import (
    Conj,
    Eq,
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
class GroundRule:
    name: str
    premises: tuple[Term, ...]
    conclusion: Term
    kind: str
    axiom_id: str | None = None
    witness: Term | None = None


@dataclass(frozen=True)
class GroundGraph:
    formulas: tuple[Term, ...]
    rules: tuple[GroundRule, ...]
    complete: bool
    cap_hit: bool


@dataclass(frozen=True)
class VampireResult:
    status: str
    szs_status: str | None
    command: tuple[str, ...]
    returncode: int
    output_path: Path


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


def _formula_key(formula: Term) -> tuple[int, str]:
    return (formula.nodes, formula.compact())


def _atom_name(formula: Term) -> str:
    digest = hashlib.sha256(formula.isabelle().encode()).hexdigest()[:20]
    return f"d_{digest}"


def build_ground_graph(
    pool: list[AxiomEntry],
    bounds: Bounds,
) -> GroundGraph:
    """Build the finite rule graph independently of derivability.

    The graph is exact for the proof rules currently implemented by
    ``prover.saturate``.  Its classical Horn models agree with the least
    forward-closure model on whether ``ObjFalse`` is derivable.
    """

    closed_terms: set[tuple[Term, Type]] = set()
    for _, term in priority_logical_terms():
        ty = infer_type((), term)
        assert ty is not None
        closed_terms.add((term, ty))
    for axiom in pool:
        closed_terms.update(_closed_subterms(axiom.formula))

    ref_terms = sorted(
        closed_terms,
        key=lambda pair: (pair[0].nodes, pair[1].nodes, pair[0].compact()),
    )[: min(bounds.node_cap // 4, 5000)]

    universe: set[Term] = {axiom.formula for axiom in pool}
    universe.update({OBJ_TRUE, OBJ_FALSE})
    universe.update(Eq(ty, term, term) for term, ty in ref_terms)
    cap_hit = False

    while True:
        before = len(universe)
        additions: set[Term] = set()
        for formula in tuple(universe):
            if formula.tag in {"Conj", "Imp"}:
                for child in formula.args:
                    if (
                        isinstance(child, Term)
                        and infer_type((), child) == PROP
                    ):
                        additions.add(child)
            elif formula.tag == "Neg":
                child = formula.args[0]
                if isinstance(child, Term) and infer_type((), child) == PROP:
                    additions.add(child)
                if child.tag == "Neg":
                    additions.add(child.args[0])
            elif formula.tag == "Forall":
                sigma, body = formula.args
                for witness, witness_ty in closed_terms:
                    if witness_ty == sigma:
                        additions.add(subst0(witness, body))

        implications = [f for f in universe | additions if f.tag == "Imp"]
        implication_set = set(implications)
        for formula in implications:
            left, right = formula.args
            converse = Imp(right, left)
            if converse in implication_set:
                additions.add(Conj(formula, converse))

        for formula in universe | additions:
            if (
                formula.tag == "Conj"
                and formula.args[0].tag == "Imp"
                and formula.args[1].tag == "Imp"
            ):
                left_imp, right_imp = formula.args
                left, right = left_imp.args
                if right_imp.args == (right, left):
                    additions.add(Eq(PROP, left, right))

        for formula in additions:
            if infer_type((), formula) != PROP:
                raise AssertionError(
                    f"ill-typed graph formula: {formula.compact()}"
                )
        universe.update(additions)
        if len(universe) > bounds.node_cap:
            cap_hit = True
            ordered = sorted(universe, key=_formula_key)
            universe = set(ordered[: bounds.node_cap])
            break
        if len(universe) == before:
            break

    rules: list[GroundRule] = []
    for axiom in pool:
        rules.append(
            GroundRule(
                f"seed_{axiom.stable_id}",
                (),
                axiom.formula,
                "axiom",
                axiom_id=axiom.stable_id,
            )
        )
    rules.append(GroundRule("seed_obj_true", (), OBJ_TRUE, "obj_true"))
    for index, (term, ty) in enumerate(ref_terms):
        conclusion = Eq(ty, term, term)
        if conclusion in universe:
            rules.append(
                GroundRule(
                    f"seed_ref_{index}",
                    (),
                    conclusion,
                    "ref",
                    witness=term,
                )
            )

    implication_set = {f for f in universe if f.tag == "Imp"}
    for formula in sorted(universe, key=_formula_key):
        if formula.tag == "Conj":
            left, right = formula.args
            if left in universe:
                rules.append(
                    GroundRule(
                        f"conj_left_{len(rules)}",
                        (formula,),
                        left,
                        "conj_left",
                    )
                )
            if right in universe:
                rules.append(
                    GroundRule(
                        f"conj_right_{len(rules)}",
                        (formula,),
                        right,
                        "conj_right",
                    )
                )
            if left.tag == "Imp" and right.tag == "Imp":
                antecedent, consequent = left.args
                if right.args == (consequent, antecedent):
                    equality = Eq(PROP, antecedent, consequent)
                    if equality in universe:
                        rules.append(
                            GroundRule(
                                f"equivalence_{len(rules)}",
                                (formula,),
                                equality,
                                "prop_equivalence",
                            )
                        )
        if formula.tag == "Neg" and formula.args[0].tag == "Neg":
            inner = formula.args[0].args[0]
            if inner in universe:
                rules.append(
                    GroundRule(
                        f"double_negation_{len(rules)}",
                        (formula,),
                        inner,
                        "double_negation",
                    )
                )
        if formula.tag == "Forall":
            sigma, body = formula.args
            for witness, witness_ty in closed_terms:
                if witness_ty != sigma:
                    continue
                instance = subst0(witness, body)
                if instance in universe:
                    rules.append(
                        GroundRule(
                            f"forall_elim_{len(rules)}",
                            (formula,),
                            instance,
                            "forall_elim",
                            witness=witness,
                        )
                    )
        if formula.tag == "Imp":
            antecedent, consequent = formula.args
            if antecedent in universe and consequent in universe:
                rules.append(
                    GroundRule(
                        f"mp_{len(rules)}",
                        (formula, antecedent),
                        consequent,
                        "mp",
                    )
                )
            converse = Imp(consequent, antecedent)
            biconditional = Conj(formula, converse)
            if converse in implication_set and biconditional in universe:
                rules.append(
                    GroundRule(
                        f"conj_intro_{len(rules)}",
                        (formula, converse),
                        biconditional,
                        "conj_intro",
                    )
                )
        negated = Neg(formula)
        if negated in universe:
            rules.append(
                GroundRule(
                    f"contradiction_{len(rules)}",
                    (formula, negated),
                    OBJ_FALSE,
                    "contradiction",
                )
            )

    dedup: dict[
        tuple[tuple[Term, ...], Term, str, str | None], GroundRule
    ] = {}
    for rule in rules:
        key = (rule.premises, rule.conclusion, rule.kind, rule.axiom_id)
        dedup.setdefault(key, rule)
    ordered_rules = tuple(dedup.values())
    ordered_formulas = tuple(sorted(universe, key=_formula_key))
    return GroundGraph(
        ordered_formulas,
        ordered_rules,
        complete=not cap_hit,
        cap_hit=cap_hit,
    )


def emit_ground_tff(
    input_path: Path,
    manifest_path: Path,
    graph: GroundGraph,
) -> None:
    input_path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "% Finite ground Horn encoding of the displayed CEV+ search tranche.",
        "% The positive conjecture is derivability of ObjFalse.",
        "% CounterSatisfiable means bounded non-derivability, not consistency.",
        "",
    ]
    for formula in graph.formulas:
        atom = _atom_name(formula)
        lines.append(f"tff({atom}_type,type,{atom}:$o).")
    lines.append("")
    rule_manifest: list[dict[str, object]] = []
    for index, rule in enumerate(graph.rules):
        name = f"r_{index}_{rule.kind}"
        conclusion = _atom_name(rule.conclusion)
        if not rule.premises:
            body = conclusion
        else:
            premise_text = " & ".join(
                _atom_name(premise) for premise in rule.premises
            )
            body = f"(({premise_text}) => {conclusion})"
        lines.append(f"tff({name},axiom,{body}).")
        rule_manifest.append(
            {
                "tptp_name": name,
                "kind": rule.kind,
                "premise_atoms": [
                    _atom_name(p) for p in rule.premises
                ],
                "conclusion_atom": _atom_name(rule.conclusion),
                "axiom_id": rule.axiom_id,
                "witness": (
                    rule.witness.isabelle()
                    if rule.witness is not None
                    else None
                ),
            }
        )
    lines.extend(
        [
            "",
            "tff(derive_objfalse,conjecture,"
            f"{_atom_name(OBJ_FALSE)}).",
            "",
        ]
    )
    input_path.write_text("\n".join(lines))
    manifest = {
        "complete_rule_graph": graph.complete,
        "cap_hit": graph.cap_hit,
        "formula_count": len(graph.formulas),
        "rule_count": len(graph.rules),
        "target_atom": _atom_name(OBJ_FALSE),
        "formulas": {
            _atom_name(formula): formula.isabelle()
            for formula in graph.formulas
        },
        "rules": rule_manifest,
    }
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")


def run_vampire(
    input_path: Path,
    output_path: Path,
    time_limit: str = "60s",
    cores: int = 1,
) -> VampireResult:
    command = (
        "vampire",
        "--mode",
        "casc",
        "--intent",
        "sat",
        "--cores",
        str(cores),
        "--time_limit",
        time_limit,
        "--input_syntax",
        "tptp",
        "--proof",
        "tptp",
        str(input_path),
    )
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output_path.write_text(completed.stdout)
    match = re.search(r"SZS status ([A-Za-z]+)", completed.stdout)
    szs_status = match.group(1) if match else None
    if szs_status in {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}:
        status = "vampire_refutation"
    elif szs_status in {"CounterSatisfiable", "Satisfiable"}:
        status = "vampire_bounded_countermodel"
    else:
        status = "vampire_unknown"
    return VampireResult(
        status,
        szs_status,
        command,
        completed.returncode,
        output_path,
    )
