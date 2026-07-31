from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

from finite_core_search.terms import (
    App,
    Const,
    PROP,
    Term,
    Type,
    infer_type,
    make_term_enumerator,
    priority_logical_terms,
    subst0,
    type_universe,
)


UNARY = Type.arr(PROP, PROP)
CLASSIFIER = Type.arr(UNARY, PROP)
BUILDER = Type.arr(CLASSIFIER, UNARY)
PURE_CLASSIFIER = Const("Pure", CLASSIFIER)


def beta_normalize(term: Term) -> Term:
    """Return the full beta normal form of a finite object-language term."""
    tag = term.tag
    args = term.args
    if tag in {"Var", "Const"}:
        return term
    if tag == "App":
        left = beta_normalize(args[0])
        right = beta_normalize(args[1])
        if left.tag == "Lam":
            return beta_normalize(subst0(right, left.args[1]))
        return Term("App", (left, right))
    if tag in {"Lam", "Forall", "Exists"}:
        return Term(tag, (args[0], beta_normalize(args[1])))
    if tag == "Eq":
        return Term(
            "Eq",
            (
                args[0],
                beta_normalize(args[1]),
                beta_normalize(args[2]),
            ),
        )
    if tag == "Neg":
        return Term("Neg", (beta_normalize(args[0]),))
    if tag in {"Conj", "Disj", "Imp"}:
        return Term(
            tag,
            (beta_normalize(args[0]), beta_normalize(args[1])),
        )
    raise ValueError(f"unknown term tag: {tag}")


@dataclass(frozen=True)
class ClassifierUse:
    argument: Term | None
    under_negation: bool
    quantifier_depth: int


def classifier_uses(builder: Term) -> tuple[ClassifierUse, ...]:
    """Locate occurrences of the outer classifier variable in a builder."""
    if builder.tag != "Lam" or builder.args[0] != CLASSIFIER:
        raise ValueError("candidate is not a classifier-to-unary abstraction")
    uses: list[ClassifierUse] = []

    def walk(
        term: Term,
        binder_depth: int,
        under_negation: bool,
        quantifier_depth: int,
    ) -> None:
        tag = term.tag
        args = term.args
        if (
            tag == "App"
            and args[0].tag == "Var"
            and int(args[0].args[0]) == binder_depth
        ):
            uses.append(
                ClassifierUse(args[1], under_negation, quantifier_depth)
            )
            walk(
                args[1],
                binder_depth,
                under_negation,
                quantifier_depth,
            )
            return
        if tag == "Var" and int(args[0]) == binder_depth:
            uses.append(
                ClassifierUse(None, under_negation, quantifier_depth)
            )
            return
        if tag == "Neg":
            walk(
                args[0],
                binder_depth,
                not under_negation,
                quantifier_depth,
            )
            return
        if tag == "Lam":
            walk(
                args[1],
                binder_depth + 1,
                under_negation,
                quantifier_depth,
            )
            return
        if tag in {"Forall", "Exists"}:
            walk(
                args[1],
                binder_depth + 1,
                under_negation,
                quantifier_depth + 1,
            )
            return
        for arg in args:
            if isinstance(arg, Term):
                walk(
                    arg,
                    binder_depth,
                    under_negation,
                    quantifier_depth,
                )

    walk(builder.args[1], 0, False, 0)
    return tuple(uses)


@dataclass(frozen=True)
class Candidate:
    name: str
    builder: Term
    source: str
    enumeration_size: int
    uses: tuple[ClassifierUse, ...]

    @property
    def diagonal(self) -> Term:
        return App(self.builder, PURE_CLASSIFIER)

    @property
    def normal_form(self) -> Term:
        return beta_normalize(self.diagonal)

    def as_json(self) -> dict[str, object]:
        return {
            "name": self.name,
            "source": self.source,
            "enumeration_size": self.enumeration_size,
            "normalized_builder_size": self.builder.nodes,
            "builder_isabelle": self.builder.isabelle(),
            "builder_compact": self.builder.compact(),
            "diagonal_isabelle": self.diagonal.isabelle(),
            "diagonal_compact": self.diagonal.compact(),
            "normal_form_isabelle": self.normal_form.isabelle(),
            "normal_form_compact": self.normal_form.compact(),
            "classifier_occurrences": len(self.uses),
            "negative_classifier_occurrences": sum(
                use.under_negation for use in self.uses
            ),
            "maximum_classifier_quantifier_depth": max(
                (use.quantifier_depth for use in self.uses),
                default=0,
            ),
            "classifier_arguments": [
                (
                    use.argument.compact()
                    if use.argument is not None
                    else None
                )
                for use in self.uses
            ],
        }


def _selected_types(type_depth: int, type_budget: int) -> tuple[Type, ...]:
    types = type_universe(type_depth)
    if type_budget > 0:
        types = types[:type_budget]
    required = (PROP, UNARY)
    missing = [ty for ty in required if ty not in types]
    if missing:
        types = tuple(dict.fromkeys((*required, *types)))
    return types


def enumerate_candidates(
    *,
    max_builder_size: int,
    min_builder_size: int = 1,
    quantifier_type_depth: int = 1,
    type_budget: int = 0,
    per_cell_cap: int = 0,
    classifier_occurrences: int = 1,
    maximum_classifier_quantifier_depth: int = 0,
    include_priority: bool = True,
) -> Iterator[Candidate]:
    """Enumerate raw-syntax builders, with known builders as a named tranche.

    ``classifier_occurrences=0`` removes the exact-occurrence filter.
    ``maximum_classifier_quantifier_depth=-1`` removes the scope filter.
    Priority builders are included independently of the displayed size and
    structural filters, and are labelled accordingly in the manifest.
    """
    seen: set[Term] = set()
    if include_priority:
        for name, builder in priority_logical_terms():
            if infer_type((), builder) != BUILDER:
                continue
            uses = classifier_uses(builder)
            if not uses or builder in seen:
                continue
            seen.add(builder)
            yield Candidate(
                name=name,
                builder=builder,
                source="priority",
                enumeration_size=builder.nodes,
                uses=uses,
            )

    types = _selected_types(quantifier_type_depth, type_budget)
    exact = make_term_enumerator(types, per_cell_cap)
    generated_index = 0
    for size in range(min_builder_size, max_builder_size + 1):
        for raw_builder in exact((), BUILDER, size):
            builder = beta_normalize(raw_builder)
            if infer_type((), builder) != BUILDER or builder.tag != "Lam":
                continue
            if builder in seen:
                continue
            uses = classifier_uses(builder)
            if not uses:
                continue
            if (
                classifier_occurrences > 0
                and len(uses) != classifier_occurrences
            ):
                continue
            if (
                maximum_classifier_quantifier_depth >= 0
                and max(use.quantifier_depth for use in uses)
                > maximum_classifier_quantifier_depth
            ):
                continue
            seen.add(builder)
            generated_index += 1
            yield Candidate(
                name=f"generated_s{size}_{generated_index}",
                builder=builder,
                source="generated",
                enumeration_size=size,
                uses=uses,
            )
