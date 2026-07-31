#!/usr/bin/env python3
"""Check that Bacon's exact model and its Goodman extensions are PER-free."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories"
HOL_ZF = THEORIES / "goodman" / "models" / "hol_zf"
CANONICAL = HOL_ZF / "canonical"
EXTENSIONS = HOL_ZF / "extensions"
SECONDARY = HOL_ZF / "secondary"

THEORY_RE = re.compile(r"^theory\s+([A-Za-z0-9_']+)", re.MULTILINE)
IMPORT_RE = re.compile(r"\bimports\b(.*?)\bbegin\b", re.DOTALL)
TOKEN_RE = re.compile(r'"([^"]+)"|([A-Za-z][A-Za-z0-9_\-\.]*)')


def theory_name(path: Path) -> str:
    match = THEORY_RE.search(path.read_text(encoding="utf-8"))
    if match is None:
        raise ValueError(f"No theory declaration in {path}")
    return match.group(1)


def imports(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    match = IMPORT_RE.search(text)
    if match is None:
        return []
    result: list[str] = []
    for quoted, bare in TOKEN_RE.findall(match.group(1)):
        token = quoted or bare
        result.append(token.rsplit(".", 1)[-1])
    return result


def project_import(token: str) -> bool:
    """Return whether an unresolved import purports to be project-local."""
    short = token.rsplit(".", 1)[-1]
    return short.startswith(("Bacon_", "Goodman_", "Audit_Goodman_"))


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def main() -> int:
    paths = list(THEORIES.rglob("*.thy"))
    by_name: dict[str, Path] = {}
    errors: list[str] = []
    for path in paths:
        name = theory_name(path)
        previous = by_name.get(name)
        if previous is not None:
            errors.append(
                f"duplicate theory {name}: {relative(previous)}, {relative(path)}"
            )
        by_name[name] = path

    protected = list(CANONICAL.glob("*.thy")) + list(EXTENSIONS.glob("*.thy"))
    protected_closure: set[Path] = set()
    for start in protected:
        pending = [start]
        seen: set[Path] = set()
        while pending:
            path = pending.pop()
            if path in seen:
                continue
            seen.add(path)
            protected_closure.add(path)
            if SECONDARY in path.parents:
                errors.append(
                    f"{relative(start)} reaches secondary theory {relative(path)}"
                )
                continue
            for imported in imports(path):
                target = by_name.get(imported)
                if target is not None:
                    pending.append(target)
                elif project_import(imported):
                    errors.append(
                        f"unresolved project import from {relative(path)}: {imported}"
                    )

    protected_forbidden = re.compile(
        r"\bPER\b|pp_uval_per|pp_per_dom|pp_closure_PER|DefaultClosurePER|"
        r"pp_n_domain"
    )
    for path in protected_closure:
        match = protected_forbidden.search(path.read_text(encoding="utf-8"))
        if match is not None:
            errors.append(
                "secondary carrier terminology in exact dependency closure: "
                f"{relative(path)}: {match.group(0)}"
            )

    per_declarations = {
        "fun pp_uval_per",
        "locale pp_closure_PER",
        "definition pp_per_dom",
    }
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for declaration in per_declarations:
            if declaration in text and SECONDARY not in path.parents:
                errors.append(
                    f"PER declaration outside secondary/: {relative(path)}: {declaration}"
                )

    canonical_names = {theory_name(path) for path in CANONICAL.glob("*.thy")}
    required = {
        "Bacon_PP_ZF_Word_Propositions",
        "Bacon_PP_ZF_Full_MSet",
        "Bacon_PP_ZF_Exact_Frame",
        "Bacon_PP_ZF_Exact_Substitution",
        "Bacon_PP_ZF_Exact_10_1",
        "Bacon_PP_ZF_Exact_CEV_Soundness",
        "Bacon_PP_ZF_Exact_Enumeration",
        "Bacon_PP_ZF_Exact_Completeness",
    }
    missing = required - canonical_names
    if missing:
        errors.append("canonical Bacon spine missing: " + ", ".join(sorted(missing)))

    root_text = (ROOT / "ROOT").read_text(encoding="utf-8")
    canonical_session = re.search(
        r"session Higher_Order_Metaphysics_PP_ZF_Model\b"
        r"(.*?)(?=\nsession |\Z)",
        root_text,
        re.DOTALL,
    )
    secondary_session = re.search(
        r"session Higher_Order_Metaphysics_PP_ZF_Secondary\b"
        r"(.*?)(?=\nsession |\Z)",
        root_text,
        re.DOTALL,
    )
    if canonical_session is None:
        errors.append("canonical Bacon session is missing from ROOT")
    else:
        block = canonical_session.group(1)
        if '"secondary"' in block or "Bacon_PP_Central_Model_Obligations" in block:
            errors.append("canonical Bacon session contains secondary theories")
    if secondary_session is None:
        errors.append("secondary HOL-ZF session is missing from ROOT")
    elif "Higher_Order_Metaphysics_PP_ZF_Model +" not in secondary_session.group(1):
        errors.append("secondary HOL-ZF session is not a child of the canonical session")

    if errors:
        print("Exact Bacon boundary check failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(
        "Exact Bacon boundary check passed: the canonical session contains "
        "only canonical/ and extensions/; neither reaches secondary/; "
        "PER declarations are quarantined."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
