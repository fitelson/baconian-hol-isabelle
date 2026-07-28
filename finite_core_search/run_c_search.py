from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from finite_core_search.axioms import Bounds, Profile  # type: ignore
    from finite_core_search.c_input import emit_c_input  # type: ignore
else:
    from .axioms import Bounds, Profile
    from .c_input import emit_c_input


PROJECT = Path(__file__).resolve().parent.parent
ENGINE_DIR = PROJECT / "finite_core_search" / "c_engine"
ENGINE = ENGINE_DIR / "finite_core_size4"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run the compact C fixed-point engine."
    )
    parser.add_argument(
        "--profile",
        choices=[p.value for p in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--type-depth", type=int, default=1)
    parser.add_argument("--term-size", type=int, default=4)
    parser.add_argument("--priority-extensions", action="store_true")
    parser.add_argument("--max-term-nodes", type=int, default=20_000_000)
    parser.add_argument(
        "--output",
        type=Path,
        default=PROJECT / "finite_core_search" / "runs" / "c_search",
    )
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=0,
        term_size=args.term_size,
        term_cell_cap=0,
        node_cap=args.max_term_nodes,
        priority_extensions=args.priority_extensions,
    )
    input_path = args.output / "input.bin"
    emit_c_input(
        input_path,
        args.output / "input.json",
        Profile(args.profile),
        bounds,
    )
    build = subprocess.run(
        ["make", "-C", str(ENGINE_DIR)],
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (args.output / "build.log").write_text(build.stdout)
    if build.returncode != 0:
        raise SystemExit(build.returncode)
    completed = subprocess.run(
        [
            str(ENGINE),
            str(input_path),
            str(args.max_term_nodes),
            str(args.output / "trace.txt"),
        ],
        cwd=PROJECT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    (args.output / "engine.out").write_text(completed.stdout)
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    engine_result = json.loads(lines[-1]) if lines else {
        "status": "engine_failed"
    }
    status = {
        "fixed_point_no_refutation": "c_bounded_fixed_point_no_refutation",
        "candidate_refutation": "c_candidate_refutation",
        "term_node_cap": "c_truncated_at_term_node_cap",
    }.get(engine_result.get("status"), "c_engine_failed")
    payload = {
        "status": status,
        "profile": args.profile,
        "bounds": vars(bounds),
        "engine": engine_result,
        "returncode": completed.returncode,
        "certification": {
            "no_refutation": (
                "A fixed point without ObjFalse is bounded "
                "non-derivability only, not consistency."
            ),
            "candidate_refutation": (
                "A C trace must replay in Isabelle before it is called an "
                "inconsistent core."
            ),
            "scope": (
                "The C kernel implements the currently documented sound "
                "fragment: axiom introduction, ObjTrue, reflexivity, "
                "universal instantiation, modus ponens, conjunction "
                "introduction/elimination, double-negation elimination, "
                "contradiction, and zeroary Equivalence."
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
