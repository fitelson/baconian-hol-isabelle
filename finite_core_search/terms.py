from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Iterable, Iterator


@dataclass(frozen=True, order=True)
class Type:
    tag: str
    left: "Type | None" = None
    right: "Type | None" = None

    @staticmethod
    def arr(left: "Type", right: "Type") -> "Type":
        return Type("Arr", left, right)

    @property
    def depth(self) -> int:
        if self.tag != "Arr":
            return 0
        assert self.left is not None and self.right is not None
        return 1 + max(self.left.depth, self.right.depth)

    @property
    def order(self) -> int:
        if self.tag != "Arr":
            return 0
        assert self.left is not None and self.right is not None
        return max(1 + self.left.order, self.right.order)

    @property
    def nodes(self) -> int:
        if self.tag != "Arr":
            return 1
        assert self.left is not None and self.right is not None
        return 1 + self.left.nodes + self.right.nodes

    def isabelle(self) -> str:
        if self.tag in {"Ind", "Prop"}:
            return self.tag
        assert self.left is not None and self.right is not None
        return f"Arr ({self.left.isabelle()}) ({self.right.isabelle()})"

    def short(self) -> str:
        if self.tag in {"Ind", "Prop"}:
            return self.tag
        assert self.left is not None and self.right is not None
        return f"({self.left.short()}->{self.right.short()})"


IND = Type("Ind")
PROP = Type("Prop")


@dataclass(frozen=True, order=True)
class Term:
    tag: str
    args: tuple[object, ...] = ()

    @property
    def nodes(self) -> int:
        return 1 + sum(a.nodes for a in self.args if isinstance(a, Term))

    def isabelle(self) -> str:
        tag = self.tag
        a = self.args
        if tag == "Var":
            return f"Var {a[0]}"
        if tag == "Const":
            name, ty = a
            assert isinstance(ty, Type)
            escaped = str(name).replace("\\", "\\\\").replace("'", "''")
            return f"Const ''{escaped}'' ({ty.isabelle()})"
        if tag == "App":
            return f"App ({a[0].isabelle()}) ({a[1].isabelle()})"
        if tag in {"Lam", "Forall", "Exists"}:
            ty, body = a
            assert isinstance(ty, Type) and isinstance(body, Term)
            return f"{tag} ({ty.isabelle()}) ({body.isabelle()})"
        if tag == "Eq":
            ty, left, right = a
            assert isinstance(ty, Type)
            return (
                f"Eq ({ty.isabelle()}) ({left.isabelle()}) "
                f"({right.isabelle()})"
            )
        if tag == "Neg":
            return f"Neg ({a[0].isabelle()})"
        if tag in {"Conj", "Disj", "Imp"}:
            return f"{tag} ({a[0].isabelle()}) ({a[1].isabelle()})"
        raise ValueError(f"unknown term tag: {tag}")

    def compact(self) -> str:
        if self.tag == "Var":
            return f"v{self.args[0]}"
        if self.tag == "Const":
            return f"{self.args[0]}:{self.args[1].short()}"
        if self.tag == "App":
            return f"({self.args[0].compact()} {self.args[1].compact()})"
        if self.tag == "Lam":
            return f"(lambda:{self.args[0].short()}. {self.args[1].compact()})"
        if self.tag == "Forall":
            return f"(forall:{self.args[0].short()}. {self.args[1].compact()})"
        if self.tag == "Exists":
            return f"(exists:{self.args[0].short()}. {self.args[1].compact()})"
        if self.tag == "Eq":
            return (
                f"({self.args[1].compact()} =:{self.args[0].short()} "
                f"{self.args[2].compact()})"
            )
        if self.tag == "Neg":
            return f"(not {self.args[0].compact()})"
        op = {"Conj": "and", "Disj": "or", "Imp": "->"}.get(self.tag)
        if op:
            return f"({self.args[0].compact()} {op} {self.args[1].compact()})"
        return self.tag


def Var(n: int) -> Term:
    return Term("Var", (n,))


def Const(name: str, ty: Type) -> Term:
    return Term("Const", (name, ty))


def App(f: Term, x: Term) -> Term:
    return Term("App", (f, x))


def Lam(ty: Type, body: Term) -> Term:
    return Term("Lam", (ty, body))


def Eq(ty: Type, left: Term, right: Term) -> Term:
    return Term("Eq", (ty, left, right))


def Neg(a: Term) -> Term:
    return Term("Neg", (a,))


def Conj(a: Term, b: Term) -> Term:
    return Term("Conj", (a, b))


def Disj(a: Term, b: Term) -> Term:
    return Term("Disj", (a, b))


def Imp(a: Term, b: Term) -> Term:
    return Term("Imp", (a, b))


def Forall(ty: Type, body: Term) -> Term:
    return Term("Forall", (ty, body))


def Exists(ty: Type, body: Term) -> Term:
    return Term("Exists", (ty, body))


def iff(a: Term, b: Term) -> Term:
    return Conj(Imp(a, b), Imp(b, a))


OBJ_TRUE = Forall(PROP, Imp(Var(0), Var(0)))
OBJ_FALSE = Neg(OBJ_TRUE)


def obj_box(a: Term) -> Term:
    return Eq(PROP, a, OBJ_TRUE)


def obj_diamond(a: Term) -> Term:
    return Neg(obj_box(Neg(a)))


def pp_pure(ty: Type, term: Term) -> Term:
    return App(Const("Pure", Type.arr(ty, PROP)), term)


def pp_fun(ty: Type, term: Term) -> Term:
    return App(Const("Fun", Type.arr(ty, PROP)), term)


def infer_type(ctx: tuple[Type, ...], term: Term) -> Type | None:
    tag = term.tag
    a = term.args
    if tag == "Var":
        n = int(a[0])
        return ctx[n] if n < len(ctx) else None
    if tag == "Const":
        return a[1] if isinstance(a[1], Type) else None
    if tag == "App":
        f_ty = infer_type(ctx, a[0])
        x_ty = infer_type(ctx, a[1])
        if f_ty is None or f_ty.tag != "Arr" or x_ty is None:
            return None
        return f_ty.right if f_ty.left == x_ty else None
    if tag == "Lam":
        ty, body = a
        body_ty = infer_type((ty,) + ctx, body)
        return None if body_ty is None else Type.arr(ty, body_ty)
    if tag == "Eq":
        ty, left, right = a
        return (
            PROP
            if infer_type(ctx, left) == ty and infer_type(ctx, right) == ty
            else None
        )
    if tag == "Neg":
        return PROP if infer_type(ctx, a[0]) == PROP else None
    if tag in {"Conj", "Disj", "Imp"}:
        return (
            PROP
            if infer_type(ctx, a[0]) == PROP
            and infer_type(ctx, a[1]) == PROP
            else None
        )
    if tag in {"Forall", "Exists"}:
        ty, body = a
        return PROP if infer_type((ty,) + ctx, body) == PROP else None
    raise ValueError(f"unknown term tag: {tag}")


def const_names(term: Term) -> frozenset[str]:
    if term.tag == "Const":
        return frozenset({str(term.args[0])})
    result: set[str] = set()
    for arg in term.args:
        if isinstance(arg, Term):
            result.update(const_names(arg))
    return frozenset(result)


def rename(term: Term, rho, cutoff: int = 0) -> Term:
    tag = term.tag
    a = term.args
    if tag == "Var":
        n = int(a[0])
        return Var(n if n < cutoff else cutoff + rho(n - cutoff))
    if tag == "Const":
        return term
    if tag == "App":
        return App(rename(a[0], rho, cutoff), rename(a[1], rho, cutoff))
    if tag == "Lam":
        return Lam(a[0], rename(a[1], rho, cutoff + 1))
    if tag == "Eq":
        return Eq(
            a[0], rename(a[1], rho, cutoff), rename(a[2], rho, cutoff)
        )
    if tag == "Neg":
        return Neg(rename(a[0], rho, cutoff))
    if tag in {"Conj", "Disj", "Imp"}:
        constructor = {"Conj": Conj, "Disj": Disj, "Imp": Imp}[tag]
        return constructor(
            rename(a[0], rho, cutoff), rename(a[1], rho, cutoff)
        )
    if tag in {"Forall", "Exists"}:
        constructor = Forall if tag == "Forall" else Exists
        return constructor(a[0], rename(a[1], rho, cutoff + 1))
    raise ValueError(tag)


def shift(term: Term) -> Term:
    return rename(term, lambda n: n + 1)


def subst0(argument: Term, body: Term, cutoff: int = 0) -> Term:
    tag = body.tag
    a = body.args
    if tag == "Var":
        n = int(a[0])
        if n < cutoff:
            return body
        if n == cutoff:
            return rename(argument, lambda k: k + cutoff)
        return Var(n - 1)
    if tag == "Const":
        return body
    if tag == "App":
        return App(
            subst0(argument, a[0], cutoff), subst0(argument, a[1], cutoff)
        )
    if tag == "Lam":
        return Lam(a[0], subst0(argument, a[1], cutoff + 1))
    if tag == "Eq":
        return Eq(
            a[0],
            subst0(argument, a[1], cutoff),
            subst0(argument, a[2], cutoff),
        )
    if tag == "Neg":
        return Neg(subst0(argument, a[0], cutoff))
    if tag in {"Conj", "Disj", "Imp"}:
        constructor = {"Conj": Conj, "Disj": Disj, "Imp": Imp}[tag]
        return constructor(
            subst0(argument, a[0], cutoff),
            subst0(argument, a[1], cutoff),
        )
    if tag in {"Forall", "Exists"}:
        constructor = Forall if tag == "Forall" else Exists
        return constructor(a[0], subst0(argument, a[1], cutoff + 1))
    raise ValueError(tag)


def type_universe(max_depth: int) -> tuple[Type, ...]:
    current: set[Type] = {IND, PROP}
    for _ in range(max_depth):
        old = tuple(current)
        current.update(Type.arr(a, b) for a, b in product(old, old))
    return tuple(sorted(current, key=type_priority_key))


def type_priority_key(ty: Type) -> tuple[int, int, int, str]:
    special = {
        PROP: 0,
        IND: 1,
        Type.arr(PROP, PROP): 2,
        Type.arr(Type.arr(PROP, PROP), PROP): 3,
        Type.arr(PROP, Type.arr(PROP, PROP)): 4,
        Type.arr(IND, Type.arr(PROP, PROP)): 5,
    }
    return (special.get(ty, 100), ty.nodes, ty.order, ty.short())


def _dedup_cap(values: Iterable[Term], cap: int) -> tuple[Term, ...]:
    result: list[Term] = []
    seen: set[Term] = set()
    for value in values:
        if value in seen:
            continue
        seen.add(value)
        result.append(value)
        if cap > 0 and len(result) >= cap:
            break
    return tuple(result)


def make_term_enumerator(
    types: tuple[Type, ...], per_cell_cap: int
):
    @lru_cache(maxsize=None)
    def exact(ctx: tuple[Type, ...], target: Type, size: int) -> tuple[Term, ...]:
        if size <= 0:
            return ()
        out: list[Term] = []
        if size == 1:
            out.extend(Var(i) for i, ty in enumerate(ctx) if ty == target)
            return _dedup_cap(out, per_cell_cap)

        if target.tag == "Arr":
            assert target.left is not None and target.right is not None
            out.extend(
                Lam(target.left, body)
                for body in exact(
                    (target.left,) + ctx, target.right, size - 1
                )
            )

        if target == PROP:
            out.extend(Neg(a) for a in exact(ctx, PROP, size - 1))
            for binder in types:
                out.extend(
                    Forall(binder, body)
                    for body in exact((binder,) + ctx, PROP, size - 1)
                )
                out.extend(
                    Exists(binder, body)
                    for body in exact((binder,) + ctx, PROP, size - 1)
                )

        for left_size in range(1, size - 1):
            right_size = size - 1 - left_size
            for arg_ty in types:
                fs = exact(ctx, Type.arr(arg_ty, target), left_size)
                xs = exact(ctx, arg_ty, right_size)
                out.extend(App(f, x) for f, x in product(fs, xs))

            if target == PROP:
                left_props = exact(ctx, PROP, left_size)
                right_props = exact(ctx, PROP, right_size)
                for left, right in product(left_props, right_props):
                    out.extend(
                        (Conj(left, right), Disj(left, right), Imp(left, right))
                    )
                for eq_ty in types:
                    lefts = exact(ctx, eq_ty, left_size)
                    rights = exact(ctx, eq_ty, right_size)
                    out.extend(Eq(eq_ty, x, y) for x, y in product(lefts, rights))

        return _dedup_cap(out, per_cell_cap)

    return exact


def priority_logical_terms() -> tuple[tuple[str, Term], ...]:
    unary = Type.arr(PROP, PROP)
    classifier = Type.arr(unary, PROP)
    constant_builder = Lam(PROP, Lam(PROP, Var(1)))
    identity = Lam(PROP, Var(0))
    negation = Lam(PROP, Neg(Var(0)))
    constant_truth = Lam(PROP, OBJ_TRUE)
    constant_false = Lam(PROP, OBJ_FALSE)
    box = Lam(PROP, obj_box(Var(0)))
    diamond = Lam(PROP, obj_diamond(Var(0)))
    biconditional_builder = Lam(PROP, Lam(PROP, iff(Var(0), Var(1))))
    inequality_builder = Lam(
        PROP, Lam(PROP, Neg(Eq(PROP, Var(0), Var(1))))
    )
    composition_builder = Lam(
        unary,
        Lam(
            unary,
            Lam(PROP, App(Var(2), App(Var(1), Var(0)))),
        ),
    )
    diagonal_builder = Lam(
        classifier,
        Lam(
            PROP,
            Neg(App(Var(1), App(constant_builder, Var(0)))),
        ),
    )
    positive_builder = Lam(
        classifier,
        Lam(PROP, App(Var(1), App(constant_builder, Var(0)))),
    )
    t4_c_ty = Type.arr(PROP, unary)
    t4_diagonal_builder = Lam(
        t4_c_ty,
        Lam(PROP, Neg(App(App(Var(1), Var(0)), Var(0)))),
    )
    t6_abstract_body = Lam(
        PROP,
        Forall(
            unary,
            Forall(
                PROP,
                Imp(
                    Conj(
                        App(Var(3), Var(1)),
                        Conj(
                            Forall(
                                unary,
                                Forall(
                                    unary,
                                    Imp(
                                        Conj(
                                            App(Var(5), Var(1)),
                                            App(Var(5), Var(0)),
                                        ),
                                        Imp(
                                            Eq(
                                                PROP,
                                                App(Var(1), Var(2)),
                                                App(Var(0), Var(2)),
                                            ),
                                            Eq(
                                                unary,
                                                Var(1),
                                                Var(0),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                            Eq(
                                PROP,
                                Var(2),
                                App(Var(1), Var(0)),
                            ),
                        ),
                    ),
                    Neg(App(Var(1), Var(2))),
                ),
            ),
        ),
    )
    t6_purity_builder = Lam(classifier, t6_abstract_body)
    fn59_builder = Lam(
        classifier,
        Lam(
            unary,
            Lam(
                PROP,
                Forall(
                    unary,
                    Forall(
                        PROP,
                        Imp(
                            Conj(
                                App(Var(4), Var(1)),
                                Conj(
                                    App(Var(3), Var(0)),
                                    Eq(
                                        PROP,
                                        Var(2),
                                        App(Var(1), Var(0)),
                                    ),
                                ),
                            ),
                            Neg(App(Var(1), Var(2))),
                        ),
                    ),
                ),
            ),
        ),
    )
    rs_diagonal_builder = Lam(
        classifier,
        Lam(
            unary,
            Lam(
                PROP,
                Exists(
                    unary,
                    Exists(
                        PROP,
                        Conj(
                            App(Var(4), Var(1)),
                            Conj(
                                App(Var(3), Var(0)),
                                Conj(
                                    Eq(
                                        PROP,
                                        Var(2),
                                        App(Var(1), Var(0)),
                                    ),
                                    Neg(App(Var(1), Var(2))),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    ho_leibniz_truth = Lam(
        PROP,
        Forall(
            unary,
            Imp(App(Var(0), OBJ_TRUE), App(Var(0), Var(1))),
        ),
    )
    ho_leibniz_false = Lam(
        PROP,
        Forall(
            unary,
            Imp(App(Var(0), OBJ_FALSE), App(Var(0), Var(1))),
        ),
    )
    ho_not_leibniz_truth = Lam(PROP, Neg(ho_leibniz_truth.args[1]))
    ho_not_leibniz_false = Lam(PROP, Neg(ho_leibniz_false.args[1]))
    ho_forall_application = Lam(
        PROP, Forall(unary, App(Var(0), Var(1)))
    )
    ho_exists_application = Lam(
        PROP, Exists(unary, App(Var(0), Var(1)))
    )

    atom = Lam(
        PROP,
        Conj(
            Neg(Eq(PROP, Var(0), OBJ_FALSE)),
            Forall(
                PROP,
                Imp(
                    Eq(PROP, Var(0), Conj(Var(0), Var(1))),
                    Disj(
                        Eq(PROP, Var(0), OBJ_FALSE),
                        Eq(PROP, Var(0), Var(1)),
                    ),
                ),
            ),
        ),
    )
    immediate = Lam(
        PROP,
        Lam(
            PROP,
            Conj(
                App(atom, Var(0)),
                Conj(
                    Neg(Var(0)),
                    Eq(
                        PROP,
                        obj_diamond(Var(0)),
                        Disj(Var(1), Var(0)),
                    ),
                ),
            ),
        ),
    )
    child_xor = Lam(
        PROP,
        Exists(
            PROP,
            Conj(
                App(atom, Var(0)),
                Conj(
                    Var(0),
                    Conj(
                        Exists(
                            PROP,
                            Conj(
                                App(App(immediate, Var(1)), Var(0)),
                                Eq(
                                    PROP,
                                    Var(0),
                                    Conj(Var(0), Var(2)),
                                ),
                            ),
                        ),
                        Exists(
                            PROP,
                            Conj(
                                App(App(immediate, Var(1)), Var(0)),
                                Eq(
                                    PROP,
                                    Var(0),
                                    Conj(Var(0), Neg(Var(2))),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    result = (
        ("truth", OBJ_TRUE),
        ("falsity", OBJ_FALSE),
        ("identity", identity),
        ("negation", negation),
        ("constant_builder", constant_builder),
        ("constant_truth", constant_truth),
        ("constant_falsity", constant_false),
        ("necessity", box),
        ("possibility", diamond),
        ("biconditional_builder", biconditional_builder),
        ("inequality_builder", inequality_builder),
        ("composition_builder", composition_builder),
        ("diagonal_builder", diagonal_builder),
        ("positive_diagonal_builder", positive_builder),
        ("T4_diagonal_builder", t4_diagonal_builder),
        ("T6_purity_builder", t6_purity_builder),
        ("fn59_diagonal_builder", fn59_builder),
        ("RS_diagonal_builder", rs_diagonal_builder),
        ("HO_leibniz_truth", ho_leibniz_truth),
        ("HO_leibniz_falsity", ho_leibniz_false),
        ("HO_not_leibniz_truth", ho_not_leibniz_truth),
        ("HO_not_leibniz_falsity", ho_not_leibniz_false),
        ("HO_forall_application", ho_forall_application),
        ("HO_exists_application", ho_exists_application),
        ("HO_atom", atom),
        ("HO_immediate", immediate),
        ("HO_child_xor", child_xor),
    )
    for name, term in result:
        if infer_type((), term) is None or const_names(term):
            raise AssertionError(f"bad priority logical term: {name}")
    return result


def enumerate_closed_logical_terms(
    types: tuple[Type, ...],
    max_size: int,
    per_cell_cap: int,
) -> Iterator[tuple[str, Term, Type]]:
    seen: set[Term] = set()
    for name, term in priority_logical_terms():
        ty = infer_type((), term)
        assert ty is not None
        if ty in types and term.nodes <= max_size and term not in seen:
            seen.add(term)
            yield name, term, ty
    exact = make_term_enumerator(types, per_cell_cap)
    for size in range(1, max_size + 1):
        for ty in types:
            for term in exact((), ty, size):
                if term in seen:
                    continue
                seen.add(term)
                yield f"generated_s{size}_{len(seen)}", term, ty
