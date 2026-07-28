from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from finite_core_search.axioms import (  # type: ignore
        Bounds,
        Profile,
        bounded_axiom_pool,
    )
    from finite_core_search.replay import emit_manifest_audit  # type: ignore
else:
    from .axioms import Bounds, Profile, bounded_axiom_pool
    from .replay import emit_manifest_audit


PROJECT = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build an Isabelle audit of one bounded axiom manifest."
    )
    parser.add_argument(
        "--profile",
        choices=[profile.value for profile in Profile],
        default=Profile.CENTRAL_RECOMBINATION.value,
    )
    parser.add_argument("--type-depth", type=int, default=3)
    parser.add_argument("--type-budget", type=int, default=6)
    parser.add_argument("--term-size", type=int, default=2)
    parser.add_argument("--term-cell-cap", type=int, default=50)
    parser.add_argument(
        "--priority-extensions",
        action="store_true",
        help="Include the T4, T6, RS, and footnote-59 builders.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=PROJECT / "finite_core_search" / "runs" / "manifest_audit",
    )
    args = parser.parse_args()
    bounds = Bounds(
        type_depth=args.type_depth,
        type_budget=args.type_budget,
        term_size=args.term_size,
        term_cell_cap=args.term_cell_cap,
        priority_extensions=args.priority_extensions,
    )
    pool, _ = bounded_axiom_pool(Profile(args.profile), bounds)
    emit_manifest_audit(args.output, Profile(args.profile), pool)
    command = [
        "isabelle",
        "build",
        "-d",
        str(PROJECT),
        "-d",
        str(PROJECT / "fresh_attack"),
        "-D",
        str(args.output),
    ]
    completed = subprocess.run(command, cwd=PROJECT, check=False)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
