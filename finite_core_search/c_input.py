from __future__ import annotations

import argparse
import json
from pathlib import Path
import struct

from .axioms import Bounds, Profile, bounded_axiom_pool
from .prover import _closed_subterms
from .terms import (
    OBJ_FALSE,
    OBJ_TRUE,
    Term,
    Type,
    infer_type,
    priority_logical_terms,
)


MAGIC = b"FCSEV1\0\0"
TYPE_RECORD = struct.Struct("<B3xII")
TERM_RECORD = struct.Struct("<B3xIII")
PAIR_RECORD = struct.Struct("<II")
HEADER = struct.Struct("<8sIIIIIII")

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


def emit_c_input(
    binary_path: Path,
    metadata_path: Path,
    profile: Profile,
    bounds: Bounds,
) -> None:
    pool, pool_metadata = bounded_axiom_pool(profile, bounds)
    closed_terms: set[tuple[Term, Type]] = set()
    for _, term in priority_logical_terms():
        ty = infer_type((), term)
        assert ty is not None
        closed_terms.add((term, ty))
    for axiom in pool:
        closed_terms.update(_closed_subterms(axiom.formula))
    witnesses = sorted(
        closed_terms,
        key=lambda pair: (
            pair[0].nodes,
            pair[1].nodes,
            pair[0].compact(),
        ),
    )
    ref_count = min(bounds.node_cap // 4, 5000, len(witnesses))

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
        tag = term.tag
        args = term.args
        a = b = c = 0
        if tag == "Var":
            a = int(args[0])
        elif tag == "Const":
            name, ty = args
            a = CONST_CODE[str(name)]
            b = add_type(ty)
        elif tag in {"App", "Conj", "Disj", "Imp"}:
            a = add_term(args[0])
            b = add_term(args[1])
        elif tag in {"Lam", "Forall", "Exists"}:
            a = add_type(args[0])
            b = add_term(args[1])
        elif tag == "Eq":
            a = add_type(args[0])
            b = add_term(args[1])
            c = add_term(args[2])
        elif tag == "Neg":
            a = add_term(args[0])
        else:
            raise ValueError(tag)
        index = len(term_records)
        term_ids[term] = index
        term_records.append((TERM_TAG[tag], a, b, c))
        return index

    axiom_records = [
        (add_term(axiom.formula), index)
        for index, axiom in enumerate(pool)
    ]
    witness_records = [
        (add_term(term), add_type(ty)) for term, ty in witnesses
    ]
    true_id = add_term(OBJ_TRUE)
    false_id = add_term(OBJ_FALSE)

    binary_path.parent.mkdir(parents=True, exist_ok=True)
    with binary_path.open("wb") as stream:
        stream.write(
            HEADER.pack(
                MAGIC,
                len(type_records),
                len(term_records),
                len(axiom_records),
                len(witness_records),
                ref_count,
                true_id,
                false_id,
            )
        )
        for record in type_records:
            stream.write(TYPE_RECORD.pack(*record))
        for record in term_records:
            stream.write(TERM_RECORD.pack(*record))
        for record in axiom_records:
            stream.write(PAIR_RECORD.pack(*record))
        for record in witness_records:
            stream.write(PAIR_RECORD.pack(*record))

    metadata = {
        "profile": profile.value,
        "bounds": vars(bounds),
        "type_records": len(type_records),
        "initial_term_records": len(term_records),
        "axiom_records": len(axiom_records),
        "witness_records": len(witness_records),
        "reflexivity_records": ref_count,
        "obj_true_id": true_id,
        "obj_false_id": false_id,
        "axioms": [
            {"index": index, **axiom.as_json()}
            for index, axiom in enumerate(pool)
        ],
        "pool_metadata": pool_metadata,
    }
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=[p.value for p in Profile],
                        default=Profile.CENTRAL_RECOMBINATION.value)
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument("--term-size", type=int, default=4)
    parser.add_argument("--priority-extensions", action="store_true")
    parser.add_argument("--node-cap", type=int, default=10_000_000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=0,
        term_size=args.term_size,
        term_cell_cap=0,
        node_cap=args.node_cap,
        priority_extensions=args.priority_extensions,
    )
    emit_c_input(
        args.output,
        args.output.with_suffix(".json"),
        Profile(args.profile),
        bounds,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
