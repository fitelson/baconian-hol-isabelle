from __future__ import annotations

from itertools import product
from typing import Iterable

from .terms import (
    App,
    Conj,
    Disj,
    Eq,
    Exists,
    Forall,
    Imp,
    Lam,
    Neg,
    PROP,
    Term,
    Type,
    Var,
    iff,
    infer_type,
    shift,
    subst0,
)


Context = tuple[Type, ...]


def terms_upto(
    exact,
    context: Context,
    types: tuple[Type, ...],
    size: int,
) -> set[tuple[Term, Type]]:
    return {
        (term, ty)
        for nodes in range(1, size + 1)
        for ty in types
        for term in exact(context, ty, nodes)
    }


def collect_typed_subterms(
    context: Context,
    term: Term,
    maximum_context_depth: int,
) -> dict[Context, set[tuple[Term, Type]]]:
    result: dict[Context, set[tuple[Term, Type]]] = {}

    def walk(current_context: Context, current: Term) -> None:
        ty = infer_type(current_context, current)
        if ty is not None and len(current_context) <= maximum_context_depth:
            result.setdefault(current_context, set()).add((current, ty))
        tag = current.tag
        args = current.args
        if tag in {"Lam", "Forall", "Exists"}:
            extended = (args[0],) + current_context
            if len(extended) <= maximum_context_depth:
                walk(extended, args[1])
            return
        for arg in args:
            if isinstance(arg, Term):
                walk(current_context, arg)

    walk(context, term)
    return result


def propositional_atoms(term: Term) -> tuple[Term, ...]:
    atoms: set[Term] = set()

    def walk(current: Term) -> None:
        if current.tag == "Neg":
            walk(current.args[0])
        elif current.tag in {"Conj", "Disj", "Imp"}:
            walk(current.args[0])
            walk(current.args[1])
        else:
            atoms.add(current)

    walk(term)
    return tuple(sorted(atoms, key=lambda value: value.compact()))


def is_prop_tautology(context: Context, term: Term) -> bool:
    if infer_type(context, term) != PROP:
        return False
    atoms = propositional_atoms(term)

    def evaluate(current: Term, valuation: dict[Term, bool]) -> bool:
        if current.tag == "Neg":
            return not evaluate(current.args[0], valuation)
        if current.tag == "Conj":
            return evaluate(current.args[0], valuation) and evaluate(
                current.args[1], valuation
            )
        if current.tag == "Disj":
            return evaluate(current.args[0], valuation) or evaluate(
                current.args[1], valuation
            )
        if current.tag == "Imp":
            return (not evaluate(current.args[0], valuation)) or evaluate(
                current.args[1], valuation
            )
        return valuation[current]

    for bits in product((False, True), repeat=len(atoms)):
        valuation = dict(zip(atoms, bits, strict=True))
        if not evaluate(term, valuation):
            return False
    return True


def _rebuild_one_step(term: Term, replace) -> set[Term]:
    result: set[Term] = set()
    tag = term.tag
    args = term.args
    if tag in {"Var", "Const"}:
        return result
    if tag == "App":
        result.update(App(changed, args[1]) for changed in replace(args[0]))
        result.update(App(args[0], changed) for changed in replace(args[1]))
    elif tag == "Lam":
        result.update(Lam(args[0], changed) for changed in replace(args[1]))
    elif tag == "Eq":
        result.update(
            Eq(args[0], changed, args[2]) for changed in replace(args[1])
        )
        result.update(
            Eq(args[0], args[1], changed) for changed in replace(args[2])
        )
    elif tag == "Neg":
        result.update(Neg(changed) for changed in replace(args[0]))
    elif tag in {"Conj", "Disj", "Imp"}:
        constructor = {"Conj": Conj, "Disj": Disj, "Imp": Imp}[tag]
        result.update(
            constructor(changed, args[1]) for changed in replace(args[0])
        )
        result.update(
            constructor(args[0], changed) for changed in replace(args[1])
        )
    elif tag in {"Forall", "Exists"}:
        constructor = Forall if tag == "Forall" else Exists
        result.update(
            constructor(args[0], changed) for changed in replace(args[1])
        )
    return result


def compatible_beta_contracts(term: Term) -> set[Term]:
    result: set[Term] = set()
    if term.tag == "App" and term.args[0].tag == "Lam":
        abstraction, argument = term.args
        result.add(subst0(argument, abstraction.args[1]))
    result.update(
        _rebuild_one_step(term, compatible_beta_contracts)
    )
    return result


def unshift(term: Term, cutoff: int = 0) -> Term | None:
    tag = term.tag
    args = term.args
    if tag == "Var":
        index = int(args[0])
        if index < cutoff:
            return term
        if index == cutoff:
            return None
        return Var(index - 1)
    if tag == "Const":
        return term
    if tag == "App":
        left = unshift(args[0], cutoff)
        right = unshift(args[1], cutoff)
        return None if left is None or right is None else App(left, right)
    if tag == "Lam":
        body = unshift(args[1], cutoff + 1)
        return None if body is None else Lam(args[0], body)
    if tag == "Eq":
        left = unshift(args[1], cutoff)
        right = unshift(args[2], cutoff)
        return (
            None
            if left is None or right is None
            else Eq(args[0], left, right)
        )
    if tag == "Neg":
        body = unshift(args[0], cutoff)
        return None if body is None else Neg(body)
    if tag in {"Conj", "Disj", "Imp"}:
        left = unshift(args[0], cutoff)
        right = unshift(args[1], cutoff)
        if left is None or right is None:
            return None
        constructor = {"Conj": Conj, "Disj": Disj, "Imp": Imp}[tag]
        return constructor(left, right)
    if tag in {"Forall", "Exists"}:
        body = unshift(args[1], cutoff + 1)
        if body is None:
            return None
        constructor = Forall if tag == "Forall" else Exists
        return constructor(args[0], body)
    raise ValueError(tag)


def compatible_eta_contracts(term: Term) -> set[Term]:
    result: set[Term] = set()
    if (
        term.tag == "Lam"
        and term.args[1].tag == "App"
        and term.args[1].args[1] == Var(0)
    ):
        candidate = unshift(term.args[1].args[0])
        if candidate is not None and shift(candidate) == term.args[1].args[0]:
            result.add(candidate)
    result.update(_rebuild_one_step(term, compatible_eta_contracts))
    return result


def boolean_identities() -> tuple[Term, ...]:
    binary = Type.arr(PROP, Type.arr(PROP, PROP))
    ternary = Type.arr(PROP, Type.arr(PROP, Type.arr(PROP, PROP)))
    return (
        Eq(
            binary,
            Lam(PROP, Lam(PROP, Conj(Var(1), Var(0)))),
            Lam(PROP, Lam(PROP, Conj(Var(0), Var(1)))),
        ),
        Eq(
            binary,
            Lam(PROP, Lam(PROP, Disj(Var(1), Var(0)))),
            Lam(PROP, Lam(PROP, Disj(Var(0), Var(1)))),
        ),
        Eq(
            ternary,
            Lam(
                PROP,
                Lam(PROP, Lam(PROP, Conj(Var(2), Disj(Var(1), Var(0))))),
            ),
            Lam(
                PROP,
                Lam(
                    PROP,
                    Lam(
                        PROP,
                        Disj(Conj(Var(2), Var(1)), Conj(Var(2), Var(0))),
                    ),
                ),
            ),
        ),
        Eq(
            ternary,
            Lam(
                PROP,
                Lam(PROP, Lam(PROP, Disj(Var(2), Conj(Var(1), Var(0))))),
            ),
            Lam(
                PROP,
                Lam(
                    PROP,
                    Lam(
                        PROP,
                        Conj(Disj(Var(2), Var(1)), Disj(Var(2), Var(0))),
                    ),
                ),
            ),
        ),
        Eq(
            binary,
            Lam(
                PROP,
                Lam(PROP, Conj(Var(1), Disj(Var(0), Neg(Var(0))))),
            ),
            Lam(PROP, Lam(PROP, Var(1))),
        ),
        Eq(
            binary,
            Lam(
                PROP,
                Lam(PROP, Disj(Var(1), Conj(Var(0), Neg(Var(0))))),
            ),
            Lam(PROP, Lam(PROP, Var(1))),
        ),
    )


def classicist_identities(sigma: Type) -> tuple[Term, ...]:
    predicate = Type.arr(sigma, PROP)
    identity = Type.arr(sigma, Type.arr(sigma, PROP))
    return (
        Eq(
            identity,
            Lam(sigma, Lam(sigma, Eq(sigma, Var(1), Var(0)))),
            Lam(
                sigma,
                Lam(
                    sigma,
                    Forall(
                        predicate,
                        iff(App(Var(0), Var(2)), App(Var(0), Var(1))),
                    ),
                ),
            ),
        ),
        Eq(
            Type.arr(predicate, Type.arr(sigma, PROP)),
            Lam(
                predicate,
                Lam(
                    sigma,
                    Disj(
                        App(Var(1), Var(0)),
                        Forall(sigma, App(Var(2), Var(0))),
                    ),
                ),
            ),
            Lam(predicate, Lam(sigma, App(Var(1), Var(0)))),
        ),
        Eq(
            Type.arr(predicate, Type.arr(PROP, PROP)),
            Lam(
                predicate,
                Lam(
                    PROP,
                    Disj(Var(0), Forall(sigma, App(Var(2), Var(0)))),
                ),
            ),
            Lam(
                predicate,
                Lam(
                    PROP,
                    Forall(sigma, Disj(Var(1), App(Var(2), Var(0)))),
                ),
            ),
        ),
        Eq(
            Type.arr(predicate, Type.arr(sigma, PROP)),
            Lam(
                predicate,
                Lam(
                    sigma,
                    Conj(
                        App(Var(1), Var(0)),
                        Exists(sigma, App(Var(2), Var(0))),
                    ),
                ),
            ),
            Lam(predicate, Lam(sigma, App(Var(1), Var(0)))),
        ),
        Eq(
            Type.arr(predicate, Type.arr(PROP, PROP)),
            Lam(
                predicate,
                Lam(
                    PROP,
                    Conj(Var(0), Exists(sigma, App(Var(2), Var(0)))),
                ),
            ),
            Lam(
                predicate,
                Lam(
                    PROP,
                    Exists(sigma, Conj(Var(1), App(Var(2), Var(0)))),
                ),
            ),
        ),
    )


def leibniz_formula(sigma: Type, left: Term, right: Term, predicate: Term) -> Term:
    return Imp(
        Eq(sigma, left, right),
        Imp(App(predicate, left), App(predicate, right)),
    )
