from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
from datetime import datetime, timezone
from itertools import repeat
import json
from pathlib import Path
import subprocess

from finite_core_search.axioms import (
    Bounds,
    Profile,
    entry,
    fixed_entries,
    modalized_functionality,
    pp_application_closure,
    pp_no_fundamentals,
)
from finite_core_search.prover import (
    minimize_support,
    saturate,
    validate_result,
)
from finite_core_search.replay import emit_replay
from finite_core_search.terms import (
    PROP,
    enumerate_closed_logical_terms,
    infer_type,
    pp_pure,
)

from .candidates import (
    BUILDER,
    CLASSIFIER,
    PURE_CLASSIFIER,
    UNARY,
    Candidate,
    enumerate_candidates,
)
from .replay import emit_purity_audit


PROJECT = Path(__file__).resolve().parent.parent


def candidate_pool(
    profile: Profile,
    bounds: Bounds,
    candidate: Candidate,
):
    pool = fixed_entries(profile)
    logical_terms = list(
        enumerate_closed_logical_terms(
            (PROP, UNARY),
            bounds.term_size,
            bounds.term_cell_cap,
        )
    )
    for index, (name, term, ty) in enumerate(logical_terms):
        pool.append(
            entry(
                "purity",
                pp_pure(ty, term),
                name,
                source_type=ty,
                priority=10 + index,
            )
        )
    pool.append(
        entry(
            "purity",
            pp_pure(BUILDER, candidate.builder),
            f"pure_diagonal:{candidate.name}",
            source_type=BUILDER,
            priority=5,
        )
    )
    relevant_types = (PROP, UNARY, CLASSIFIER)
    for sigma in relevant_types:
        for tau in relevant_types:
            pool.append(
                entry(
                    "application_closure",
                    pp_application_closure(sigma, tau),
                    f"{sigma.short()} to {tau.short()}",
                    priority=40,
                )
            )
            if profile == Profile.FRESH_FULL_QLN_MF:
                pool.append(
                    entry(
                        "modalized_functionality",
                        modalized_functionality(sigma, tau),
                        f"{sigma.short()} to {tau.short()}",
                        priority=50,
                    )
                )
    for sigma in (UNARY, CLASSIFIER, BUILDER):
        pool.append(
            entry(
                "no_fundamentals",
                pp_no_fundamentals(sigma),
                sigma.short(),
                source_type=sigma,
                priority=30,
            )
        )
    dedup = {}
    for axiom in pool:
        dedup.setdefault(axiom.formula, axiom)
    metadata = {
        "selected_type_count": len(relevant_types),
        "logical_term_count": len(logical_terms),
        "focused_stock": (
            "fixed profile formulas plus the candidate, small Prop/unary "
            "logical terms, and application closure over Prop, unary "
            "operators, and unary classifiers"
        ),
    }
    return list(dedup.values()), metadata


def candidate_seed_terms(candidate: Candidate):
    seeds = [
        (candidate.builder, BUILDER),
        (PURE_CLASSIFIER, CLASSIFIER),
        (candidate.diagonal, UNARY),
        (candidate.normal_form, UNARY),
    ]
    dedup = {}
    for term, ty in seeds:
        if infer_type((), term) != ty:
            raise AssertionError(
                f"ill-typed candidate seed: {term.compact()} at {ty.short()}"
            )
        dedup.setdefault((term, ty), None)
    return tuple(dedup)


def screen_candidate(
    profile: Profile,
    bounds: Bounds,
    candidate: Candidate,
) -> dict[str, object]:
    """Run the sound reference saturation for one candidate."""
    pool, pool_metadata = candidate_pool(profile, bounds, candidate)
    seeds = candidate_seed_terms(candidate)
    result = saturate(pool, bounds, seeds)
    validate_result(pool, result)
    pure_formula = pp_pure(UNARY, candidate.diagonal)
    record = candidate.as_json()
    record.update(
        {
            "pool_axioms": len(pool),
            "selected_type_count": pool_metadata["selected_type_count"],
            "derived_formulas": len(result.proofs),
            "rounds_completed": result.rounds_completed,
            "fixed_point_reached": result.saturated,
            "node_cap_hit": result.node_cap_hit,
            "purity_derived_by_reference_saturator": (
                pure_formula in result.proofs
            ),
            "contradiction_found_by_reference_saturator": result.found,
        }
    )
    return record


def _build_session(directory: Path, session_name: str) -> tuple[int, str]:
    command = [
        "isabelle",
        "build",
        "-j",
        "1",
        "-d",
        str(PROJECT),
        "-D",
        str(directory),
        session_name,
    ]
    completed = subprocess.run(
        command,
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.returncode, completed.stdout


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Enumerate closed logical builders B, form D = B(Pure), and "
            "screen the selected CEV+ profile for a replayable contradiction."
        )
    )
    parser.add_argument(
        "--profile",
        choices=[profile.value for profile in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--min-builder-size", type=int, default=1)
    parser.add_argument("--max-builder-size", type=int, default=7)
    parser.add_argument("--quantifier-type-depth", type=int, default=1)
    parser.add_argument("--type-budget", type=int, default=0)
    parser.add_argument(
        "--per-cell-cap",
        type=int,
        default=0,
        help=(
            "Term-enumerator cap per context/type/size; 0 is exhaustive. "
            "A positive cap is only a heuristic tranche."
        ),
    )
    parser.add_argument(
        "--classifier-occurrences",
        type=int,
        default=1,
        help="Exact occurrences for generated builders; 0 means any positive.",
    )
    parser.add_argument(
        "--maximum-classifier-quantifier-depth",
        type=int,
        default=0,
        help="-1 removes this filter.",
    )
    parser.add_argument("--no-priority-builders", action="store_true")
    parser.add_argument("--max-candidates", type=int, default=100)
    parser.add_argument("--stock-term-size", type=int, default=2)
    parser.add_argument("--rounds", type=int, default=20)
    parser.add_argument("--node-cap", type=int, default=100000)
    parser.add_argument(
        "--progress-every",
        type=int,
        default=100,
        help="Print a progress line after this many candidates; 0 disables.",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=1,
        help=(
            "Parallel Python screening workers. Candidate generation stays "
            "single-source and Isabelle replay remains serial."
        ),
    )
    parser.add_argument(
        "--worker-chunksize",
        type=int,
        default=8,
        help="Candidate batch size sent to each Python worker.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=PROJECT / "pure_diagonal_search" / "runs" / "latest",
    )
    parser.add_argument(
        "--emit-purity-audit",
        action="store_true",
        help="Generate, but do not build, an aggregate candidate-purity audit.",
    )
    parser.add_argument(
        "--build-purity-audit",
        action="store_true",
        help="Generate and serially build the aggregate candidate-purity audit.",
    )
    parser.add_argument(
        "--build-contradiction-replay",
        action="store_true",
        help="Serially build an emitted contradiction replay after a hit.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if (
        args.min_builder_size < 1
        or args.max_builder_size < args.min_builder_size
        or args.stock_term_size < 1
    ):
        raise SystemExit("size bounds must be positive")
    if args.quantifier_type_depth < 0 or args.type_budget < 0:
        raise SystemExit("type bounds must be nonnegative")
    if args.classifier_occurrences < 0:
        raise SystemExit("classifier-occurrences must be nonnegative")
    if args.workers < 1 or args.worker_chunksize < 1:
        raise SystemExit("worker bounds must be positive")

    profile = Profile(args.profile)
    candidates = list(
        enumerate_candidates(
            max_builder_size=args.max_builder_size,
            min_builder_size=args.min_builder_size,
            quantifier_type_depth=args.quantifier_type_depth,
            type_budget=args.type_budget,
            per_cell_cap=args.per_cell_cap,
            classifier_occurrences=args.classifier_occurrences,
            maximum_classifier_quantifier_depth=(
                args.maximum_classifier_quantifier_depth
            ),
            include_priority=not args.no_priority_builders,
        )
    )[: args.max_candidates]
    if not candidates:
        raise SystemExit("the displayed bounds generated no candidates")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    audit_dir = output / "purity_audit"
    audit_session = "Goodman_Pure_Diagonal_Audit"
    purity_audit_exit = None
    purity_audit_emitted = (
        args.emit_purity_audit or args.build_purity_audit
    )
    if purity_audit_emitted:
        emit_purity_audit(audit_dir, profile, candidates, audit_session)
    if args.build_purity_audit:
        purity_audit_exit, build_log = _build_session(
            audit_dir, audit_session
        )
        (audit_dir / "build.log").write_text(build_log)

    bounds = Bounds(
        type_depth=args.quantifier_type_depth,
        type_budget=args.type_budget,
        term_size=args.stock_term_size,
        term_cell_cap=args.per_cell_cap,
        rounds=args.rounds,
        node_cap=args.node_cap,
    )
    records: list[dict[str, object]] = []
    certified_hit = False
    candidate_hit = False
    executor = None
    if args.workers == 1:
        screened = (
            screen_candidate(profile, bounds, candidate)
            for candidate in candidates
        )
    else:
        executor = ProcessPoolExecutor(max_workers=args.workers)
        screened = executor.map(
            screen_candidate,
            repeat(profile),
            repeat(bounds),
            candidates,
            chunksize=args.worker_chunksize,
            buffersize=args.workers * 4,
        )
    try:
        for index, (candidate, record) in enumerate(
            zip(candidates, screened, strict=True)
        ):
            if record["contradiction_found_by_reference_saturator"]:
                candidate_hit = True
                pool, _ = candidate_pool(profile, bounds, candidate)
                seeds = candidate_seed_terms(candidate)
                result = saturate(pool, bounds, seeds)
                validate_result(pool, result)
                if not result.found:
                    raise AssertionError(
                        "parallel contradiction hit did not reproduce"
                    )
                core, minimized = minimize_support(
                    pool, result, bounds, seeds
                )
                validate_result(core, minimized)
                replay_dir = output / f"contradiction_{index}"
                session_name = f"Goodman_Pure_Diagonal_Replay_{index}"
                emit_replay(
                    replay_dir,
                    profile,
                    core,
                    minimized,
                    session_name=session_name,
                )
                record["candidate_core_ids"] = [
                    axiom.stable_id for axiom in core
                ]
                record["contradiction_replay"] = str(replay_dir)
                if args.build_contradiction_replay:
                    replay_exit, replay_log = _build_session(
                        replay_dir, session_name
                    )
                    (replay_dir / "build.log").write_text(replay_log)
                    record["contradiction_replay_exit"] = replay_exit
                    if replay_exit == 0:
                        certified_hit = True
                        records.append(record)
                        break
            records.append(record)
            if (
                args.progress_every > 0
                and len(records) % args.progress_every == 0
            ):
                print(
                    f"screened {len(records)}/{len(candidates)} candidates",
                    flush=True,
                )
            if candidate_hit:
                break
    finally:
        if executor is not None:
            executor.shutdown(
                wait=not candidate_hit,
                cancel_futures=candidate_hit,
            )

    status = (
        "certified_inconsistent_core"
        if certified_hit
        else (
            "candidate_core"
            if any(
                record["contradiction_found_by_reference_saturator"]
                for record in records
            )
            else "bounded_no_refutation"
        )
    )
    manifest = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "status": status,
        "profile": profile.value,
        "candidate_count": len(records),
        "bounds": {
            "min_builder_size": args.min_builder_size,
            "max_builder_size": args.max_builder_size,
            "quantifier_type_depth": args.quantifier_type_depth,
            "type_budget": args.type_budget,
            "per_cell_cap": args.per_cell_cap,
            "classifier_occurrences": args.classifier_occurrences,
            "maximum_classifier_quantifier_depth": (
                args.maximum_classifier_quantifier_depth
            ),
            "priority_builders": not args.no_priority_builders,
            "max_candidates": args.max_candidates,
            "stock_term_size": args.stock_term_size,
            "rounds": args.rounds,
            "node_cap": args.node_cap,
            "workers": args.workers,
            "worker_chunksize": args.worker_chunksize,
        },
        "purity_audit": {
            "directory": str(audit_dir) if purity_audit_emitted else None,
            "emitted": purity_audit_emitted,
            "build_requested": args.build_purity_audit,
            "build_exit": purity_audit_exit,
            "certified": purity_audit_exit == 0,
        },
        "terminology": {
            "bounded_no_refutation": (
                "No contradiction was found for these builders with the "
                "displayed sound but incomplete proof-rule and witness bounds. "
                "This is not a consistency result."
            ),
            "candidate_core": (
                "The reference saturator found a contradiction and emitted "
                "the existing finite-core Isabelle replay, but that replay "
                "has not built successfully."
            ),
            "certified_inconsistent_core": (
                "The existing finite-core Isabelle replay built successfully."
            ),
        },
        "candidates": records,
    }
    (output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(f"{status}: {len(records)} candidates ({output})")
    if purity_audit_exit is not None:
        print(f"purity audit exit: {purity_audit_exit}")
    return 0 if not args.build_purity_audit or purity_audit_exit == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
