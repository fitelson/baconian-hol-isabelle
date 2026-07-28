from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from finite_core_search.axioms import (  # type: ignore
        Bounds,
        Profile,
        bounded_axiom_pool,
    )
    from finite_core_search.prover import _closed_subterms  # type: ignore
    from finite_core_search.terms import (  # type: ignore
        OBJ_FALSE,
        OBJ_TRUE,
        PROP,
        Term,
        Type,
        infer_type,
        priority_logical_terms,
    )
else:
    from .axioms import Bounds, Profile, bounded_axiom_pool
    from .prover import _closed_subterms
    from .terms import (
        OBJ_FALSE,
        OBJ_TRUE,
        PROP,
        Term,
        Type,
        infer_type,
        priority_logical_terms,
    )


PROJECT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Sym:
    tag: str
    args: tuple[object, ...] = ()


def sym(term: Term) -> Sym:
    args: list[object] = []
    for arg in term.args:
        args.append(sym(arg) if isinstance(arg, Term) else arg)
    return Sym(term.tag, tuple(args))


def meta(name: str) -> Sym:
    return Sym("Meta", (name,))


def subst0(argument: Sym, body: Sym, cutoff: int = 0) -> Sym:
    tag = body.tag
    args = body.args
    if tag == "Meta":
        return body
    if tag == "Var":
        index = int(args[0])
        if index < cutoff:
            return body
        if index == cutoff:
            return argument
        return Sym("Var", (index - 1,))
    if tag == "Const":
        return body
    if tag in {"App", "Conj", "Disj", "Imp"}:
        return Sym(
            tag,
            (
                subst0(argument, args[0], cutoff),
                subst0(argument, args[1], cutoff),
            ),
        )
    if tag in {"Lam", "Forall", "Exists"}:
        return Sym(
            tag,
            (args[0], subst0(argument, args[1], cutoff + 1)),
        )
    if tag == "Eq":
        return Sym(
            tag,
            (
                args[0],
                subst0(argument, args[1], cutoff),
                subst0(argument, args[2], cutoff),
            ),
        )
    if tag == "Neg":
        return Sym(tag, (subst0(argument, args[0], cutoff),))
    raise ValueError(tag)


def type_tff(ty: Type) -> str:
    if ty.tag == "Ind":
        return "ind_ty"
    if ty.tag == "Prop":
        return "prop_ty"
    assert ty.left is not None and ty.right is not None
    return f"arr_ty({type_tff(ty.left)},{type_tff(ty.right)})"


def nat_tff(index: int) -> str:
    return "s(" * index + "z" + ")" * index


def term_tff(term: Sym) -> str:
    tag = term.tag
    args = term.args
    if tag == "Meta":
        return str(args[0])
    if tag == "Var":
        return f"v({nat_tff(int(args[0]))})"
    if tag == "Const":
        name, ty = args
        constructor = {"Pure": "pure_const", "Fun": "fun_const"}[str(name)]
        return f"{constructor}({type_tff(ty)})"
    if tag == "App":
        return f"app_t({term_tff(args[0])},{term_tff(args[1])})"
    if tag == "Lam":
        return f"lam_t({type_tff(args[0])},{term_tff(args[1])})"
    if tag == "Eq":
        return (
            f"eq_t({type_tff(args[0])},{term_tff(args[1])},"
            f"{term_tff(args[2])})"
        )
    if tag == "Neg":
        return f"neg_t({term_tff(args[0])})"
    if tag in {"Conj", "Disj", "Imp"}:
        constructor = {
            "Conj": "conj_t",
            "Disj": "disj_t",
            "Imp": "imp_t",
        }[tag]
        return (
            f"{constructor}({term_tff(args[0])},{term_tff(args[1])})"
        )
    if tag in {"Forall", "Exists"}:
        constructor = "all_t" if tag == "Forall" else "exists_t"
        return f"{constructor}({type_tff(args[0])},{term_tff(args[1])})"
    raise ValueError(tag)


def metas_in(term: Sym) -> tuple[str, ...]:
    result: set[str] = set()

    def walk(current: Sym) -> None:
        if current.tag == "Meta":
            result.add(str(current.args[0]))
            return
        for arg in current.args:
            if isinstance(arg, Sym):
                walk(arg)

    walk(term)
    return tuple(sorted(result, key=lambda name: int(name[1:])))


def ui_templates(seeds: list[Term]) -> list[tuple[Sym, Type, Sym]]:
    templates: dict[tuple[Sym, Type, Sym], None] = {}

    def walk(formula: Sym, next_meta: int) -> None:
        tag = formula.tag
        args = formula.args
        if tag == "Forall":
            binder = args[0]
            witness = meta(f"M{next_meta}")
            instance = subst0(witness, args[1])
            templates.setdefault((formula, binder, instance), None)
            walk(instance, next_meta + 1)
        elif tag in {"Conj", "Imp"}:
            walk(args[0], next_meta)
            walk(args[1], next_meta)
        elif tag == "Neg":
            walk(args[0], next_meta)

    for seed in seeds:
        walk(sym(seed), 0)
    return list(templates)


def emit_schematic_problem(
    output_path: Path,
    metadata_path: Path,
    profile: Profile,
    bounds: Bounds,
) -> dict[str, object]:
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
    ref_terms = witnesses[: min(bounds.node_cap // 4, 5000)]
    templates = ui_templates(
        [axiom.formula for axiom in pool] + [OBJ_TRUE]
    )

    lines = [
        "% Lazy schematic Horn search for the displayed finite CEV+ tranche.",
        "% CounterSatisfiable means bounded non-derivability, not consistency.",
        "tff(ty_type,type,ty:$tType).",
        "tff(tm_type,type,tm:$tType).",
        "tff(nat_type,type,nat:$tType).",
        "tff(ind_ty_type,type,ind_ty:ty).",
        "tff(prop_ty_type,type,prop_ty:ty).",
        "tff(arr_ty_type,type,arr_ty:(ty*ty)>ty).",
        "tff(z_type,type,z:nat).",
        "tff(s_type,type,s:nat>nat).",
        "tff(v_type,type,v:nat>tm).",
        "tff(pure_const_type,type,pure_const:ty>tm).",
        "tff(fun_const_type,type,fun_const:ty>tm).",
        "tff(app_t_type,type,app_t:(tm*tm)>tm).",
        "tff(lam_t_type,type,lam_t:(ty*tm)>tm).",
        "tff(eq_t_type,type,eq_t:(ty*tm*tm)>tm).",
        "tff(neg_t_type,type,neg_t:tm>tm).",
        "tff(conj_t_type,type,conj_t:(tm*tm)>tm).",
        "tff(disj_t_type,type,disj_t:(tm*tm)>tm).",
        "tff(imp_t_type,type,imp_t:(tm*tm)>tm).",
        "tff(all_t_type,type,all_t:(ty*tm)>tm).",
        "tff(exists_t_type,type,exists_t:(ty*tm)>tm).",
        "tff(derived_type,type,derived:tm>$o).",
        "tff(witness_type,type,witness:(ty*tm)>$o).",
        "",
        "tff(rule_conj_left,axiom,! [A:tm,B:tm] :",
        "  (derived(conj_t(A,B)) => derived(A))).",
        "tff(rule_conj_right,axiom,! [A:tm,B:tm] :",
        "  (derived(conj_t(A,B)) => derived(B))).",
        "tff(rule_double_negation,axiom,! [A:tm] :",
        "  (derived(neg_t(neg_t(A))) => derived(A))).",
        "tff(rule_mp,axiom,! [A:tm,B:tm] :",
        "  ((derived(imp_t(A,B)) & derived(A)) => derived(B))).",
        "tff(rule_conj_intro,axiom,! [A:tm,B:tm] :",
        "  ((derived(imp_t(A,B)) & derived(imp_t(B,A)))",
        "    => derived(conj_t(imp_t(A,B),imp_t(B,A))))).",
        "tff(rule_equivalence,axiom,! [A:tm,B:tm] :",
        "  (derived(conj_t(imp_t(A,B),imp_t(B,A)))",
        "    => derived(eq_t(prop_ty,A,B)))).",
        "tff(rule_contradiction,axiom,! [A:tm] :",
        f"  ((derived(A) & derived(neg_t(A))) => "
        f"derived({term_tff(sym(OBJ_FALSE))}))).",
        "",
    ]
    for index, axiom in enumerate(pool):
        lines.append(
            f"tff(seed_axiom_{index},axiom,"
            f"derived({term_tff(sym(axiom.formula))}))."
        )
    lines.append(
        f"tff(seed_obj_true,axiom,derived({term_tff(sym(OBJ_TRUE))}))."
    )
    for index, (term, ty) in enumerate(ref_terms):
        lines.append(
            f"tff(seed_ref_{index},axiom,derived("
            f"eq_t({type_tff(ty)},{term_tff(sym(term))},"
            f"{term_tff(sym(term))})))."
        )
    lines.append("")
    for index, (term, ty) in enumerate(witnesses):
        lines.append(
            f"tff(witness_{index},axiom,"
            f"witness({type_tff(ty)},{term_tff(sym(term))}))."
        )
    lines.append("")
    for index, (universal, binder, instance) in enumerate(templates):
        names = sorted(
            set(metas_in(universal)) | set(metas_in(instance)),
            key=lambda name: int(name[1:]),
        )
        witness_name = (
            f"M{max([int(name[1:]) for name in names], default=-1) + 1}"
        )
        quantified = names + [witness_name]
        quantifier = ",".join(f"{name}:tm" for name in quantified)
        instantiated = subst0(meta(witness_name), universal.args[1])
        lines.extend(
            [
                f"tff(ui_{index},axiom,! [{quantifier}] :",
                f"  ((derived({term_tff(universal)}) &",
                f"    witness({type_tff(binder)},{witness_name}))",
                f"   => derived({term_tff(instantiated)}))).",
            ]
        )
    lines.extend(
        [
            "",
            f"tff(derive_objfalse,conjecture,"
            f"derived({term_tff(sym(OBJ_FALSE))})).",
            "",
        ]
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(lines))
    metadata = {
        "profile": profile.value,
        "bounds": vars(bounds),
        "pool_axioms": len(pool),
        "witnesses": len(witnesses),
        "reflexivity_seeds": len(ref_terms),
        "ui_templates": len(templates),
        "pool_metadata": pool_metadata,
        "guarantee": (
            "The schematic rules compact the same finite witness stock used "
            "by the C and Python engines. A countermodel is bounded "
            "non-derivability only; a refutation requires Isabelle replay."
        ),
    }
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    return metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile",
        choices=[p.value for p in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument("--term-size", type=int, default=5)
    parser.add_argument("--priority-extensions", action="store_true")
    parser.add_argument("--node-cap", type=int, default=50_000_000)
    parser.add_argument("--time-limit", default="5m")
    parser.add_argument("--cores", type=int, default=4)
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
    args.output.mkdir(parents=True, exist_ok=True)
    problem = args.output / "schematic_derivability.tff.in"
    metadata = emit_schematic_problem(
        problem,
        args.output / "schematic_manifest.json",
        Profile(args.profile),
        bounds,
    )
    command = [
        "vampire",
        "--mode",
        "casc",
        "--intent",
        "sat",
        "--cores",
        str(args.cores),
        "--time_limit",
        args.time_limit,
        "--input_syntax",
        "tptp",
        "--proof",
        "off",
        str(problem),
    ]
    completed = subprocess.run(
        command,
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (args.output / "vampire.out").write_text(completed.stdout)
    match = re.search(r"SZS status ([A-Za-z]+)", completed.stdout)
    szs_status = match.group(1) if match else None
    if szs_status in {"CounterSatisfiable", "Satisfiable"}:
        status = "schematic_bounded_fixed_point_no_refutation"
    elif szs_status in {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}:
        status = "schematic_candidate_refutation"
    else:
        status = "schematic_unknown"
    proof_command = None
    if status == "schematic_candidate_refutation":
        proof_command = command[:-2] + ["tptp", str(problem)]
        proof_run = subprocess.run(
            proof_command,
            cwd=PROJECT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        (args.output / "vampire_proof.out").write_text(proof_run.stdout)

    result = {
        "status": status,
        "szs_status": szs_status,
        "profile": args.profile,
        "bounds": vars(bounds),
        "pool_axioms": metadata["pool_axioms"],
        "witnesses": metadata["witnesses"],
        "reflexivity_seeds": metadata["reflexivity_seeds"],
        "ui_templates": metadata["ui_templates"],
        "command": command,
        "proof_command": proof_command,
        "returncode": completed.returncode,
        "certification": {
            "countermodel": (
                "A countermodel to this Horn problem proves non-derivability "
                "in the displayed finite witness closure. It is not a model "
                "of Goodman's object theory and is not a consistency proof."
            ),
            "refutation": (
                "A refutation is a candidate only until its instantiated "
                "proof trace replays in Isabelle."
            ),
        },
    }
    (args.output / "result.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
