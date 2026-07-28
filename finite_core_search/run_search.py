from __future__ import annotations

import argparse
from dataclasses import replace
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from finite_core_search.axioms import (  # type: ignore
        Bounds,
        Profile,
        bounded_axiom_pool,
        write_manifest,
    )
    from finite_core_search.prover import (  # type: ignore
        minimize_support,
        saturate,
        validate_result,
    )
    from finite_core_search.replay import emit_replay  # type: ignore
    from finite_core_search.vampire import (  # type: ignore
        build_ground_graph,
        emit_ground_tff,
        run_vampire,
    )
else:
    from .axioms import (
        Bounds,
        Profile,
        bounded_axiom_pool,
        write_manifest,
    )
    from .prover import minimize_support, saturate, validate_result
    from .replay import emit_replay
    from .vampire import build_ground_graph, emit_ground_tff, run_vampire


PROJECT = Path(__file__).resolve().parent.parent


def _write_result(
    path: Path,
    profile: Profile,
    bounds: Bounds,
    pool_count: int,
    result,
    status: str,
    core_ids: list[str] | None = None,
    replay_build_exit: int | None = None,
    graph=None,
    vampire_result=None,
) -> None:
    payload = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "status": status,
        "profile": profile.value,
        "bounds": vars(bounds),
        "pool_axioms": pool_count,
        "derived_formulas": (
            len(result.proofs) if result is not None else None
        ),
        "rounds_completed": (
            result.rounds_completed if result is not None else None
        ),
        "fixed_point_reached": (
            result.saturated if result is not None else None
        ),
        "node_cap_hit": (
            result.node_cap_hit if result is not None else None
        ),
        "search_hit": result.found if result is not None else None,
        "candidate_core_ids": core_ids or [],
        "isabelle_replay_exit": replay_build_exit,
        "ground_graph": (
            {
                "formula_count": len(graph.formulas),
                "rule_count": len(graph.rules),
                "complete": graph.complete,
                "cap_hit": graph.cap_hit,
            }
            if graph is not None
            else None
        ),
        "vampire": (
            {
                "status": vampire_result.status,
                "szs_status": vampire_result.szs_status,
                "command": list(vampire_result.command),
                "returncode": vampire_result.returncode,
                "output": str(vampire_result.output_path),
            }
            if vampire_result is not None
            else None
        ),
        "terminology": {
            "bounded_no_refutation": (
                "No derivation was found in this bounded sound search. "
                "This is not a consistency result."
            ),
            "candidate_core": (
                "The search derived falsity, but Isabelle replay has not "
                "yet certified the derivation and stock membership."
            ),
            "vampire_bounded_countermodel": (
                "Vampire found a model of the finite ground Horn "
                "derivability problem with ObjFalse underivable. This is "
                "not a model of Goodman's object theory and is not a "
                "consistency result."
            ),
            "vampire_truncated_countermodel": (
                "Vampire found a model only after the finite rule graph hit "
                "its construction cap. This is neither exhaustive at the "
                "displayed bounds nor a consistency result."
            ),
            "certified_inconsistent_core": (
                "Isabelle built the replay and audited its final theorem "
                "object as oracle-free, hypothesis-free, and flex-flex-free."
            ),
        },
    }
    if result is not None and result.found:
        payload["proof_dag"] = [node.as_json() for node in result.proof_dag()]
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _run_one(
    profile: Profile,
    bounds: Bounds,
    output_root: Path,
    build_replay: bool,
    use_vampire: bool,
    vampire_time_limit: str,
    vampire_cores: int,
) -> tuple[str, Path]:
    label = (
        f"{profile.value}_d{bounds.type_depth}_tb{bounds.type_budget}"
        f"_s{bounds.term_size}"
        f"_{'diagonals' if bounds.priority_extensions else 'exhaustive'}"
    )
    run_dir = output_root / label
    run_dir.mkdir(parents=True, exist_ok=True)
    pool, metadata = bounded_axiom_pool(profile, bounds)
    write_manifest(run_dir / "manifest.json", pool, metadata)
    graph = None
    vampire_result = None
    if use_vampire:
        graph = build_ground_graph(pool, bounds)
        emit_ground_tff(
            run_dir / "bounded_derivability.tff.in",
            run_dir / "bounded_derivability_manifest.json",
            graph,
        )
        vampire_result = run_vampire(
            run_dir / "bounded_derivability.tff.in",
            run_dir / "vampire.out",
            vampire_time_limit,
            vampire_cores,
        )
        if vampire_result.status == "vampire_bounded_countermodel":
            status = (
                "vampire_bounded_countermodel"
                if graph.complete
                else "vampire_truncated_countermodel"
            )
            _write_result(
                run_dir / "result.json",
                profile,
                bounds,
                len(pool),
                None,
                status,
                graph=graph,
                vampire_result=vampire_result,
            )
            return status, run_dir

    result = saturate(pool, bounds)
    validate_result(pool, result)
    if not result.found:
        status = (
            "vampire_refutation_reconstruction_failed"
            if vampire_result is not None
            and vampire_result.status == "vampire_refutation"
            else "bounded_no_refutation"
        )
        _write_result(
            run_dir / "result.json",
            profile,
            bounds,
            len(pool),
            result,
            status,
            graph=graph,
            vampire_result=vampire_result,
        )
        return status, run_dir

    core, minimized_result = minimize_support(pool, result, bounds)
    validate_result(core, minimized_result)
    core_ids = [axiom.stable_id for axiom in core]
    replay_dir = run_dir / "replay"
    emit_replay(replay_dir, profile, core, minimized_result)
    if not build_replay:
        _write_result(
            run_dir / "result.json",
            profile,
            bounds,
            len(pool),
            minimized_result,
            "candidate_core",
            core_ids,
            graph=graph,
            vampire_result=vampire_result,
        )
        return "candidate_core", run_dir

    command = [
        "isabelle",
        "build",
        "-d",
        str(PROJECT),
        "-D",
        str(replay_dir),
    ]
    completed = subprocess.run(
        command,
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (replay_dir / "build.log").write_text(completed.stdout)
    status = (
        "certified_inconsistent_core"
        if completed.returncode == 0
        else "candidate_core_replay_failed"
    )
    _write_result(
        run_dir / "result.json",
        profile,
        bounds,
        len(pool),
        minimized_result,
        status,
        core_ids,
        completed.returncode,
        graph,
        vampire_result,
    )
    return status, run_dir


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run a bounded, certificate-first search for a finite Goodman "
            "inconsistent core."
        )
    )
    parser.add_argument(
        "--profile",
        choices=[profile.value for profile in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--all-profiles", action="store_true")
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument(
        "--type-budget",
        type=int,
        default=0,
        help="Number of priority types; 0 means every type at this depth.",
    )
    parser.add_argument("--max-term-size", type=int, default=2)
    parser.add_argument(
        "--term-cell-cap",
        type=int,
        default=0,
        help="Per-context/type/size cap; 0 means exhaustive.",
    )
    parser.add_argument("--context-depth", type=int, default=1)
    parser.add_argument("--rounds", type=int, default=20)
    parser.add_argument("--node-cap", type=int, default=50000)
    parser.add_argument(
        "--output",
        type=Path,
        default=PROJECT / "finite_core_search" / "runs",
    )
    parser.add_argument(
        "--no-build-replay",
        action="store_true",
        help="Generate but do not build a replay after a search hit.",
    )
    parser.add_argument(
        "--single-size",
        action="store_true",
        help="Run only max-term-size instead of dovetailing sizes 1..N.",
    )
    parser.add_argument(
        "--priority-extensions",
        action="store_true",
        help=(
            "Add the T4, T6, RS, and footnote-59 diagonal builders outside "
            "the strict displayed depth/size tranche."
        ),
    )
    parser.add_argument(
        "--no-vampire",
        action="store_true",
        help="Use only the small Python reference saturator.",
    )
    parser.add_argument("--vampire-time-limit", default="60s")
    parser.add_argument("--vampire-cores", type=int, default=1)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.type_depth < 0 or args.type_budget < 0:
        raise SystemExit("type bounds must be nonnegative")
    if args.max_term_size < 1:
        raise SystemExit("max-term-size must be positive")
    profiles = (
        list(Profile)
        if args.all_profiles
        else [Profile(args.profile)]
    )
    base_bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=args.type_budget,
        term_size=args.max_term_size,
        term_cell_cap=args.term_cell_cap,
        context_depth=args.context_depth,
        rounds=args.rounds,
        node_cap=args.node_cap,
        priority_extensions=args.priority_extensions,
    )
    sizes = (
        [args.max_term_size]
        if args.single_size
        else list(range(1, args.max_term_size + 1))
    )
    args.output.mkdir(parents=True, exist_ok=True)
    summary: list[dict[str, str]] = []
    for size in sizes:
        for profile in profiles:
            bounds = replace(base_bounds, term_size=size)
            status, run_dir = _run_one(
                profile,
                bounds,
                args.output,
                not args.no_build_replay,
                not args.no_vampire,
                args.vampire_time_limit,
                args.vampire_cores,
            )
            summary.append(
                {
                    "profile": profile.value,
                    "term_size": str(size),
                    "status": status,
                    "run_dir": str(run_dir),
                }
            )
            print(
                f"{profile.value} size={size}: {status} "
                f"({run_dir})",
                flush=True,
            )
            if status == "certified_inconsistent_core":
                (args.output / "summary.json").write_text(
                    json.dumps(summary, indent=2) + "\n"
                )
                return 0
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
