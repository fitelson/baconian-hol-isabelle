from __future__ import annotations

import argparse
import json
from pathlib import Path
import struct

from .axioms import Bounds, Profile, bounded_axiom_pool
from .coverage import (
    boolean_identities,
    classicist_identities,
    collect_typed_subterms,
    compatible_beta_contracts,
    compatible_eta_contracts,
    is_prop_tautology,
    terms_upto,
)
from .terms import (
    OBJ_FALSE,
    OBJ_TRUE,
    PROP,
    Term,
    Type,
    iff,
    infer_type,
    make_term_enumerator,
    priority_logical_terms,
    subst0,
    type_universe,
)


MAGIC = b"FCSEV2\0\0"
HEADER = struct.Struct("<8sIIIIIIIII")
TYPE_RECORD = struct.Struct("<B3xII")
TERM_RECORD = struct.Struct("<B3xIII")
SEED_RECORD = struct.Struct("<IIII")
TYPED_RECORD = struct.Struct("<III")
EG_EDGE = struct.Struct("<III")
UINT32_MAX = 2**32 - 1

TYPE_TAG = {"Ind": 0, "Prop": 1, "Arr": 2}
TERM_TAG = {
    "Var": 0,
    "Const": 1,
    "App": 2,
    "Lam": 3,
    "Eq": 4,
    "Neg": 5,
    "Conj": 6,
    "Disj": 7,
    "Imp": 8,
    "Forall": 9,
    "Exists": 10,
}
CONST_CODE = {"Pure": 0, "Fun": 1}

SEED_AXIOM = 1
SEED_TRUE = 2
SEED_PC = 3
SEED_BOOLEAN = 4
SEED_CLASSIC = 5
SEED_BETA = 6
SEED_ETA = 7


def _merge(
    target: dict[tuple[Type, ...], set[tuple[Term, Type]]],
    source: dict[tuple[Type, ...], set[tuple[Term, Type]]],
) -> None:
    for context, entries in source.items():
        target.setdefault(context, set()).update(entries)


def emit_context_c_input(
    binary_path: Path,
    metadata_path: Path,
    profile: Profile,
    bounds: Bounds,
) -> dict[str, object]:
    if bounds.context_depth != 1:
        raise ValueError("the FCSEV2 engine implements context depth one")
    selected_types = type_universe(bounds.type_depth)
    contexts = ((),) + tuple((ty,) for ty in selected_types)
    context_ids = {context: index for index, context in enumerate(contexts)}
    exact = make_term_enumerator(selected_types, bounds.term_cell_cap)
    bounded = {
        context: terms_upto(
            exact, context, selected_types, bounds.term_size
        )
        for context in contexts
    }
    typed = {context: set(entries) for context, entries in bounded.items()}
    eg_root_typed = {context: set() for context in contexts}
    pool, pool_metadata = bounded_axiom_pool(profile, bounds)

    boolean = list(boolean_identities())
    classic = [
        identity
        for ty in selected_types
        for identity in classicist_identities(ty)
    ]
    roots = [axiom.formula for axiom in pool]
    roots.extend(term for _, term in priority_logical_terms())
    roots.extend(boolean)
    roots.extend(classic)
    roots.extend((OBJ_TRUE, OBJ_FALSE))
    eg_roots = [
        axiom.formula for axiom in pool if axiom.family != "purity"
    ]
    eg_roots.extend(term for _, term in priority_logical_terms())
    eg_roots.extend(boolean)
    eg_roots.extend(classic)
    eg_roots.extend((OBJ_TRUE, OBJ_FALSE))
    for context in contexts:
        for root in roots:
            if infer_type(context, root) is None:
                continue
            subterms = collect_typed_subterms(context, root, 1)
            _merge(typed, subterms)
        for root in eg_roots:
            if infer_type(context, root) is None:
                continue
            _merge(
                eg_root_typed,
                collect_typed_subterms(context, root, 1),
            )

    seed_specs: set[tuple[int, Term, int, int]] = set()
    for context in contexts:
        context_id = context_ids[context]
        for axiom_index, axiom in enumerate(pool):
            seed_specs.add(
                (context_id, axiom.formula, SEED_AXIOM, axiom_index)
            )
        seed_specs.add((context_id, OBJ_TRUE, SEED_TRUE, 0))
        for identity in boolean:
            seed_specs.add((context_id, identity, SEED_BOOLEAN, 0))
        for identity in classic:
            seed_specs.add((context_id, identity, SEED_CLASSIC, 0))
        bounded_props = {
            term for term, ty in bounded[context] if ty == PROP
        }
        for formula in bounded_props:
            if is_prop_tautology(context, formula):
                seed_specs.add((context_id, formula, SEED_PC, 0))
        all_props = {
            term for term, ty in typed[context] if ty == PROP
        }
        for formula in all_props:
            for reduct in compatible_beta_contracts(formula):
                if infer_type(context, reduct) == PROP:
                    seed_specs.add(
                        (context_id, iff(formula, reduct), SEED_BETA, 0)
                    )
            for reduct in compatible_eta_contracts(formula):
                if infer_type(context, reduct) == PROP:
                    seed_specs.add(
                        (context_id, iff(formula, reduct), SEED_ETA, 0)
                    )

    # EG is kept finite and trigger-based.  We include exactly existential
    # templates occurring in the selected Goodman axioms, priority terms, or
    # fixed CEV base identities; all witnesses remain exhaustive at the
    # displayed term bound.
    eg_specs: set[tuple[int, Term, Term]] = set()
    targeted_exists: dict[
        tuple[Type, ...], set[tuple[Type, Term]]
    ] = {}
    for context in contexts:
        targeted_exists[context] = {
            (term.args[0], term.args[1])
            for term, ty in eg_root_typed[context]
            if ty == PROP and term.tag == "Exists"
        }
        by_type: dict[Type, list[Term]] = {}
        for term, ty in typed[context]:
            by_type.setdefault(ty, []).append(term)
        for binder, body in targeted_exists[context]:
            conclusion = Term("Exists", (binder, body))
            for witness in by_type.get(binder, []):
                premise = subst0(witness, body)
                if infer_type(context, premise) == PROP:
                    eg_specs.add(
                        (context_ids[context], premise, conclusion)
                    )

    type_ids: dict[Type, int] = {}
    type_records: list[tuple[int, int, int]] = []

    def add_type(ty: Type) -> int:
        known = type_ids.get(ty)
        if known is not None:
            return known
        left = right = 0
        if ty.tag == "Arr":
            assert ty.left is not None and ty.right is not None
            left = add_type(ty.left)
            right = add_type(ty.right)
        index = len(type_records)
        type_ids[ty] = index
        type_records.append((TYPE_TAG[ty.tag], left, right))
        return index

    term_ids: dict[Term, int] = {}
    term_records: list[tuple[int, int, int, int]] = []

    def add_term(term: Term) -> int:
        known = term_ids.get(term)
        if known is not None:
            return known
        args = term.args
        a = b = c = 0
        if term.tag == "Var":
            a = int(args[0])
        elif term.tag == "Const":
            a = CONST_CODE[str(args[0])]
            b = add_type(args[1])
        elif term.tag in {"App", "Conj", "Disj", "Imp"}:
            a = add_term(args[0])
            b = add_term(args[1])
        elif term.tag in {"Lam", "Forall", "Exists"}:
            a = add_type(args[0])
            b = add_term(args[1])
        elif term.tag == "Eq":
            a = add_type(args[0])
            b = add_term(args[1])
            c = add_term(args[2])
        elif term.tag == "Neg":
            a = add_term(args[0])
        else:
            raise ValueError(term.tag)
        index = len(term_records)
        term_ids[term] = index
        term_records.append((TERM_TAG[term.tag], a, b, c))
        return index

    typed_records = [
        (context_ids[context], add_term(term), add_type(ty))
        for context in contexts
        for term, ty in sorted(
            typed[context],
            key=lambda pair: (
                pair[0].nodes,
                pair[1].nodes,
                pair[0].compact(),
            ),
        )
    ]
    seed_records = [
        (context_id, add_term(term), kind, axiom)
        for context_id, term, kind, axiom in sorted(
            seed_specs,
            key=lambda item: (
                item[0],
                item[2],
                item[1].nodes,
                item[1].compact(),
            ),
        )
    ]
    eg_records = [
        (context_id, add_term(premise), add_term(conclusion))
        for context_id, premise, conclusion in sorted(
            eg_specs,
            key=lambda item: (
                item[0],
                item[1].nodes,
                item[1].compact(),
                item[2].compact(),
            ),
        )
    ]
    context_binders = [
        UINT32_MAX if not context else add_type(context[0])
        for context in contexts
    ]
    true_id = add_term(OBJ_TRUE)
    false_id = add_term(OBJ_FALSE)
    prop_type = add_type(PROP)

    binary_path.parent.mkdir(parents=True, exist_ok=True)
    with binary_path.open("wb") as stream:
        stream.write(
            HEADER.pack(
                MAGIC,
                len(type_records),
                len(term_records),
                len(contexts),
                len(seed_records),
                len(typed_records),
                len(eg_records),
                true_id,
                false_id,
                prop_type,
            )
        )
        for record in type_records:
            stream.write(TYPE_RECORD.pack(*record))
        for record in term_records:
            stream.write(TERM_RECORD.pack(*record))
        for binder in context_binders:
            stream.write(struct.pack("<I", binder))
        for record in seed_records:
            stream.write(SEED_RECORD.pack(*record))
        for record in typed_records:
            stream.write(TYPED_RECORD.pack(*record))
        for record in eg_records:
            stream.write(EG_EDGE.pack(*record))

    metadata = {
        "profile": profile.value,
        "bounds": vars(bounds),
        "selected_types": [ty.short() for ty in selected_types],
        "contexts": [
            [] if not context else [context[0].short()]
            for context in contexts
        ],
        "type_records": len(type_records),
        "term_records": len(term_records),
        "seed_records": len(seed_records),
        "typed_records": len(typed_records),
        "eg_edges": len(eg_records),
        "targeted_exists_templates": {
            str(context_ids[context]): len(targeted_exists[context])
            for context in contexts
        },
        "pool_axioms": len(pool),
        "pool_metadata": pool_metadata,
        "coverage": [
            "context-indexed Axiom and Base seeds",
            "bounded propositional tautologies",
            "UI and targeted EG",
            "typed reflexivity",
            "lazy Leibniz elimination",
            "compatible one-step beta and eta",
            "MP, Generalization, and Instantiation",
            "zeroary and unary Vector Equivalence",
            "Boolean and Classicist identities",
        ],
        "limitations": [
            "contexts longer than one",
            "vector Equivalence of arity greater than one",
            "EG templates absent from the selected root vocabulary",
            "propositional tautologies larger than the displayed term bound",
        ],
    }
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    return metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile",
        choices=[profile.value for profile in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument("--term-size", type=int, default=4)
    parser.add_argument("--priority-extensions", action="store_true")
    parser.add_argument("--max-term-nodes", type=int, default=50_000_000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=0,
        term_size=args.term_size,
        term_cell_cap=0,
        context_depth=1,
        node_cap=args.max_term_nodes,
        priority_extensions=args.priority_extensions,
    )
    emit_context_c_input(
        args.output,
        args.output.with_suffix(".json"),
        Profile(args.profile),
        bounds,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
