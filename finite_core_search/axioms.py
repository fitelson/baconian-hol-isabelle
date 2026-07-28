from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
import json
from pathlib import Path
from typing import Iterable

from .terms import (
    App,
    Conj,
    Const,
    Eq,
    Exists,
    Forall,
    Imp,
    Neg,
    OBJ_TRUE,
    PROP,
    Term,
    Type,
    Var,
    enumerate_closed_logical_terms,
    infer_type,
    obj_box,
    pp_fun,
    pp_pure,
    priority_logical_terms,
    type_priority_key,
    type_universe,
)


class Profile(str, Enum):
    CENTRAL_RECOMBINATION = "central_recombination"
    REPAIRED_ZEROARY_EXHAUSTION = "repaired_zeroary_exhaustion"
    FULL_QLN = "full_qln"
    FRESH_FULL_QLN_MF = "fresh_full_qln_mf"

    @property
    def isabelle(self) -> str:
        return {
            Profile.CENTRAL_RECOMBINATION: "Recombination_Only",
            Profile.REPAIRED_ZEROARY_EXHAUSTION:
                "Repaired_Zeroary_Exhaustion",
            Profile.FULL_QLN: "Full_QLN",
            Profile.FRESH_FULL_QLN_MF:
                "Full_QLN_Modalized_Functionality",
        }[self]


@dataclass(frozen=True)
class Bounds:
    type_depth: int = 1
    type_budget: int = 0
    term_size: int = 2
    term_cell_cap: int = 0
    context_depth: int = 1
    rounds: int = 20
    node_cap: int = 50000
    priority_extensions: bool = False


@dataclass(frozen=True)
class AxiomEntry:
    stable_id: str
    family: str
    formula: Term
    source: str
    source_type: Type | None = None
    priority: int = 100

    def as_json(self) -> dict[str, object]:
        return {
            "id": self.stable_id,
            "family": self.family,
            "formula_isabelle": self.formula.isabelle(),
            "formula_compact": self.formula.compact(),
            "source": self.source,
            "source_type": (
                self.source_type.isabelle()
                if self.source_type is not None
                else None
            ),
            "priority": self.priority,
        }


def _id(family: str, formula: Term, source: str) -> str:
    digest = hashlib.sha256(
        f"{family}\0{formula.isabelle()}\0{source}".encode()
    ).hexdigest()[:14]
    return f"{family}_{digest}"


def entry(
    family: str,
    formula: Term,
    source: str,
    source_type: Type | None = None,
    priority: int = 100,
) -> AxiomEntry:
    if infer_type((), formula) != PROP:
        raise ValueError(f"ill-typed axiom {family}: {formula.compact()}")
    return AxiomEntry(
        _id(family, formula, source),
        family,
        formula,
        source,
        source_type,
        priority,
    )


def pp_target_pp() -> Term:
    unary = Type.arr(PROP, PROP)
    classifier = Type.arr(unary, PROP)
    pure_unary = Const("Pure", classifier)
    return pp_pure(classifier, pure_unary)


def pp_application_closure(sigma: Type, tau: Type) -> Term:
    return Forall(
        Type.arr(sigma, tau),
        Forall(
            sigma,
            Imp(
                Conj(
                    pp_pure(Type.arr(sigma, tau), Var(1)),
                    pp_pure(sigma, Var(0)),
                ),
                pp_pure(tau, App(Var(1), Var(0))),
            ),
        ),
    )


def pp_unique_fundamental_prop() -> Term:
    return Exists(
        PROP,
        Conj(
            pp_fun(PROP, Var(0)),
            Forall(
                PROP,
                Imp(
                    pp_fun(PROP, Var(0)),
                    Eq(PROP, Var(0), Var(1)),
                ),
            ),
        ),
    )


def pp_no_fundamentals(sigma: Type) -> Term:
    return Forall(sigma, Neg(pp_fun(sigma, Var(0))))


def pp_zeroary_recombination() -> Term:
    return Forall(
        PROP,
        Imp(
            pp_pure(PROP, Var(0)),
            Imp(obj_box(Var(0)), Var(0)),
        ),
    )


def pp_zeroary_exhaustion() -> Term:
    return Forall(
        PROP,
        Imp(
            pp_pure(PROP, Var(0)),
            Imp(Var(0), obj_box(Var(0))),
        ),
    )


def pp_unary_recombination() -> Term:
    unary = Type.arr(PROP, PROP)
    return Forall(
        unary,
        Forall(
            PROP,
            Imp(
                Conj(
                    pp_pure(unary, Var(1)),
                    pp_fun(PROP, Var(0)),
                ),
                Imp(
                    obj_box(App(Var(1), Var(0))),
                    Forall(PROP, App(Var(2), Var(0))),
                ),
            ),
        ),
    )


def pp_unary_exhaustion() -> Term:
    unary = Type.arr(PROP, PROP)
    return Forall(
        unary,
        Forall(
            PROP,
            Imp(
                Conj(
                    pp_pure(unary, Var(1)),
                    pp_fun(PROP, Var(0)),
                ),
                Imp(
                    Forall(PROP, App(Var(2), Var(0))),
                    obj_box(App(Var(1), Var(0))),
                ),
            ),
        ),
    )


def modalized_functionality(sigma: Type, tau: Type) -> Term:
    arrow = Type.arr(sigma, tau)
    return Forall(
        arrow,
        Forall(
            arrow,
            Imp(
                obj_box(
                    Forall(
                        sigma,
                        Eq(
                            tau,
                            App(Var(2), Var(0)),
                            App(Var(1), Var(0)),
                        ),
                    )
                ),
                Eq(arrow, Var(1), Var(0)),
            ),
        ),
    )


def fixed_entries(profile: Profile) -> list[AxiomEntry]:
    result = [
        entry("pp", pp_target_pp(), "Purity of Pure", priority=0),
        entry(
            "unique_fundamental",
            pp_unique_fundamental_prop(),
            "unique fundamental proposition",
            priority=1,
        ),
        entry(
            "zeroary_recombination",
            pp_zeroary_recombination(),
            "zeroary Recombination",
            priority=2,
        ),
        entry(
            "unary_recombination",
            pp_unary_recombination(),
            "unary Recombination",
            priority=2,
        ),
    ]
    if profile in {
        Profile.REPAIRED_ZEROARY_EXHAUSTION,
        Profile.FULL_QLN,
        Profile.FRESH_FULL_QLN_MF,
    }:
        result.append(
            entry(
                "zeroary_exhaustion",
                pp_zeroary_exhaustion(),
                "zeroary Exhaustion",
                priority=3,
            )
        )
    if profile in {Profile.FULL_QLN, Profile.FRESH_FULL_QLN_MF}:
        result.append(
            entry(
                "unary_exhaustion",
                pp_unary_exhaustion(),
                "unary Exhaustion",
                priority=3,
            )
        )
    return result


def _priority_types(
    all_types: tuple[Type, ...],
    term_types: Iterable[Type],
    budget: int,
) -> tuple[Type, ...]:
    required: set[Type] = {PROP}
    for ty in term_types:
        required.add(ty)
        cursor = ty
        while cursor.tag == "Arr":
            assert cursor.left is not None and cursor.right is not None
            required.add(cursor.left)
            required.add(cursor.right)
            cursor = cursor.right
    ordered_required = sorted(required, key=type_priority_key)
    ordered_rest = [ty for ty in all_types if ty not in required]
    return tuple((ordered_required + ordered_rest)[: max(budget, len(required))])


def bounded_axiom_pool(
    profile: Profile, bounds: Bounds
) -> tuple[list[AxiomEntry], dict[str, object]]:
    all_types = type_universe(bounds.type_depth)
    prelim_types = (
        all_types
        if bounds.type_budget == 0
        else all_types[: bounds.type_budget]
    )
    logical_terms = list(
        enumerate_closed_logical_terms(
            prelim_types, bounds.term_size, bounds.term_cell_cap
        )
    )
    if bounds.priority_extensions:
        seen_terms = {term for _, term, _ in logical_terms}
        first_diagonal_names = {
            "T4_diagonal_builder",
            "T6_purity_builder",
            "fn59_diagonal_builder",
            "RS_diagonal_builder",
        }
        for name, term in priority_logical_terms():
            if name not in first_diagonal_names:
                continue
            if term in seen_terms:
                continue
            ty = infer_type((), term)
            assert ty is not None
            logical_terms.append((f"priority_{name}", term, ty))
            seen_terms.add(term)
    selected_types = (
        all_types
        if bounds.type_budget == 0
        else _priority_types(
            all_types,
            (ty for _, _, ty in logical_terms),
            bounds.type_budget,
        )
    )
    if selected_types != prelim_types:
        logical_terms = list(
            enumerate_closed_logical_terms(
                selected_types, bounds.term_size, bounds.term_cell_cap
            )
        )

    result = fixed_entries(profile)
    for index, (name, term, ty) in enumerate(logical_terms):
        result.append(
            entry(
                "purity",
                pp_pure(ty, term),
                name,
                source_type=ty,
                priority=10 + index,
            )
        )

    type_pairs = sorted(
        ((sigma, tau) for sigma in selected_types for tau in selected_types),
        key=lambda p: (
            p[0].nodes + p[1].nodes,
            type_priority_key(p[0]),
            type_priority_key(p[1]),
        ),
    )
    for sigma, tau in type_pairs:
        result.append(
            entry(
                "application_closure",
                pp_application_closure(sigma, tau),
                f"{sigma.short()} to {tau.short()}",
                priority=40,
            )
        )
        if profile == Profile.FRESH_FULL_QLN_MF:
            result.append(
                entry(
                    "modalized_functionality",
                    modalized_functionality(sigma, tau),
                    f"{sigma.short()} to {tau.short()}",
                    priority=50,
                )
            )

    for sigma in selected_types:
        if sigma != PROP:
            result.append(
                entry(
                    "no_fundamentals",
                    pp_no_fundamentals(sigma),
                    sigma.short(),
                    source_type=sigma,
                    priority=30,
                )
            )

    dedup: dict[Term, AxiomEntry] = {}
    for axiom in sorted(result, key=lambda x: (x.priority, x.stable_id)):
        dedup.setdefault(axiom.formula, axiom)
    pool = list(dedup.values())
    metadata: dict[str, object] = {
        "profile": profile.value,
        "profile_isabelle": profile.isabelle,
        "bounds": {
            "type_depth": bounds.type_depth,
            "type_budget": bounds.type_budget,
            "term_size": bounds.term_size,
            "term_cell_cap": bounds.term_cell_cap,
            "context_depth": bounds.context_depth,
            "rounds": bounds.rounds,
            "node_cap": bounds.node_cap,
            "priority_extensions": bounds.priority_extensions,
        },
        "complete_type_universe_count": len(all_types),
        "selected_type_count": len(selected_types),
        "selected_types": [ty.isabelle() for ty in selected_types],
        "logical_term_count": len(logical_terms),
        "axiom_count": len(pool),
        "family_counts": {
            family: sum(1 for a in pool if a.family == family)
            for family in sorted({a.family for a in pool})
        },
        "guarantee": (
            "Every listed formula is intended to be an exact instance of the "
            "selected stock. A contradiction is not certified until a "
            "generated Isabelle replay builds."
        ),
        "exhaustive_at_displayed_syntactic_bounds": (
            bounds.type_budget == 0
            and bounds.term_cell_cap == 0
            and not bounds.priority_extensions
        ),
    }
    return pool, metadata


def write_manifest(
    path: Path,
    pool: list[AxiomEntry],
    metadata: dict[str, object],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(metadata)
    payload["axioms"] = [axiom.as_json() for axiom in pool]
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
