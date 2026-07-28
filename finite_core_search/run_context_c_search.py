from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from finite_core_search.axioms import Bounds, Profile  # type: ignore
else:
    from .axioms import Bounds, Profile


PROJECT = Path(__file__).resolve().parent.parent
ENGINE_DIR = PROJECT / "finite_core_search" / "c_engine"
ENGINE = ENGINE_DIR / "finite_core_context1"


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run the context-depth-1 CEV+ trigger engine at a finite bound."
        )
    )
    parser.add_argument(
        "--profile",
        choices=[profile.value for profile in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument("--term-size", type=int, default=4)
    parser.add_argument("--priority-extensions", action="store_true")
    parser.add_argument("--max-term-nodes", type=int, default=50_000_000)
    parser.add_argument(
        "--reuse-input",
        action="store_true",
        help="reuse an existing input.bin/input.json pair in the output folder",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=(
            PROJECT / "finite_core_search" / "runs" / "context_c_search"
        ),
    )
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=0,
        term_size=args.term_size,
        term_cell_cap=0,
        context_depth=1,
        node_cap=args.max_term_nodes,
        priority_extensions=args.priority_extensions,
    )
    input_path = args.output / "input.bin"
    emit_command = [
        sys.executable,
        "-m",
        "finite_core_search.context_c_input",
        "--profile",
        args.profile,
        "--type-depth",
        str(args.type_depth),
        "--term-size",
        str(args.term_size),
        "--max-term-nodes",
        str(args.max_term_nodes),
        "--output",
        str(input_path),
    ]
    if args.priority_extensions:
        emit_command.append("--priority-extensions")
    if args.reuse_input:
        if not input_path.is_file() or not (args.output / "input.json").is_file():
            parser.error("--reuse-input requires existing input.bin and input.json")
    else:
        emitted = subprocess.run(
            emit_command,
            cwd=PROJECT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        (args.output / "emit.log").write_text(emitted.stdout)
        if emitted.returncode != 0:
            return emitted.returncode
    manifest = json.loads((args.output / "input.json").read_text())
    if args.reuse_input:
        saved_bounds = manifest.get("bounds", {})
        expected = {
            "type_depth": args.type_depth,
            "term_size": args.term_size,
            "node_cap": args.max_term_nodes,
            "priority_extensions": args.priority_extensions,
        }
        if manifest.get("profile") != args.profile or any(
            saved_bounds.get(key) != value for key, value in expected.items()
        ):
            parser.error("--reuse-input arguments do not match input.json")
    build = subprocess.run(
        ["make", "-C", str(ENGINE_DIR), "finite_core_context1"],
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (args.output / "build.log").write_text(build.stdout)
    if build.returncode != 0:
        return build.returncode
    completed = subprocess.run(
        [str(ENGINE), str(input_path), str(args.max_term_nodes)],
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (args.output / "engine.out").write_text(completed.stdout)
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    engine_result = {"status": "engine_failed"}
    for line in reversed(lines):
        try:
            candidate = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(candidate, dict):
            engine_result = candidate
            break
    if engine_result["status"] == "engine_failed":
        engine_result["returncode"] = completed.returncode
        if lines:
            engine_result["last_output_line"] = lines[-1]
    status = {
        "fixed_point_no_refutation":
            "bounded_no_refutation_context_depth_1",
        "candidate_refutation": "candidate_refutation_requires_trace_replay",
        "term_node_cap": "context_search_truncated_at_term_node_cap",
    }.get(engine_result.get("status"), "context_engine_failed")
    payload = {
        "status": status,
        "profile": args.profile,
        "bounds": vars(bounds),
        "manifest_counts": {
            key: manifest[key]
            for key in (
                "pool_axioms",
                "term_records",
                "seed_records",
                "typed_records",
                "eg_edges",
            )
        },
        "engine": engine_result,
        "returncode": completed.returncode,
        "coverage": manifest["coverage"],
        "limitations": manifest["limitations"],
        "certification": {
            "no_refutation": (
                "The fixed point establishes bounded non-derivability only. "
                "It is not a consistency proof."
            ),
            "candidate_refutation": (
                "The present context engine does not yet emit a replay trace. "
                "A candidate must be rerun with trace support and replayed in "
                "Isabelle before it is called an inconsistent core."
            ),
        },
    }
    (args.output / "result.json").write_text(
        json.dumps(payload, indent=2) + "\n"
    )
    print(json.dumps(payload, indent=2))
    return 0 if completed.returncode in {0, 3} else completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
