#!/usr/bin/env python3
"""Report which registration sites a validation check still owes.

    uv run python .../scripts/registration_sites.py <check_name> [--repo PATH]

A new check in SK_EFT_Hawking must be registered in ~11 places. Several are
frozen contracts that break on arrival if missed. The list is derived here by
probing the live tree, because a quoted list goes stale and a hand-derived one
gets it wrong: the plan for ADR-013 P1 named four of eleven.

Exit 0 when every site is satisfied, 1 otherwise. Reports the numeric floors as
deltas rather than pass/fail, since only the author knows the intended direction.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

#: (label, relpath, predicate-kind). Probed in the live tree, never assumed.
SITES: tuple[tuple[str, str, str], ...] = (
    ("check definition", "scripts/validation/checks/", "any-in-dir"),
    ("_CANONICAL_ORDER", "scripts/validate.py", "name"),
    ("validate.py re-export", "scripts/validate.py", "export"),
    ("EXPECTED_CHECKS (count+order)", "tests/test_validate_registry_contract.py", "name"),
    # CONDITIONAL, and getting this wrong is the mistake this script exists to stop.
    # `EXPECTED_CHECK_FUNCTIONS` lists check functions a test reaches AS
    # `validate.check_<name>`. A check whose tests import it from its own checks module
    # does not belong there, and adding it would be wrong. The predicate below asks
    # whether any test actually reaches it that way — the decider — rather than treating
    # membership as owed by every check.
    ("EXPECTED_CHECK_FUNCTIONS (only if a test reaches it via `validate.`)",
     "tests/test_validate_public_surface.py", "public-surface"),
    ("mutation obligation", "tests/test_d5_mutation_obligation.py", "name"),
    ("cannot-measure baseline", "tests/test_cannot_measure_baseline.py", "optional"),
    ("verify_scope path mapping", "scripts/verify_scope.py", "name"),
    ("sync edge (only if it writes an artifact)", "scripts/sync_manifest.py", "optional"),
    ("SURFACE_INVENTORY (regenerate)", "docs/architecture/SURFACE_INVENTORY.md", "name"),
)


def _reached_via_validate(root: Path, check: str) -> bool:
    """Does any test reach this check AS `validate.check_<name>`?

    The DECIDER for `EXPECTED_CHECK_FUNCTIONS` membership. A test that calls the
    function through its own checks module (`fr.check_x`) does not put the name on
    `validate`'s external surface, so listing it there would assert a coupling that
    does not exist.
    """
    fn = f"check_{check}"
    pats = (re.compile(rf"from\s+validate\s+import\s+[^\n]*\b{fn}\b"),
            re.compile(rf"\bv(?:alidate)?\.{fn}\b"))
    tests = root / "tests"
    if not tests.is_dir():
        return False
    return any(p.name != "test_validate_public_surface.py"
               and any(rx.search(p.read_text(encoding="utf-8", errors="ignore"))
                       for rx in pats)
               for p in tests.rglob("test_*.py"))


def _hit(root: Path, rel: str, kind: str, check: str) -> bool | None:
    """True satisfied, False owed, None not-applicable-or-unreadable."""
    target = root / rel
    if kind == "any-in-dir":
        return any(check in p.read_text(encoding="utf-8", errors="ignore")
                   for p in target.rglob("*.py")) if target.is_dir() else None
    if not target.is_file():
        return None
    text = target.read_text(encoding="utf-8", errors="ignore")
    if kind == "public-surface":
        if not _reached_via_validate(root, check):
            return None          # not applicable — nothing reaches it that way
        return f"check_{check}" in text
    if kind == "export":
        return f"check_{check}" in text
    return check in text


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("check", help="the registered check name, e.g. module_census_fresh")
    ap.add_argument("--repo", type=Path, default=Path.cwd(),
                    help="repo root (default: cwd)")
    args = ap.parse_args(argv)
    root, check = args.repo.resolve(), args.check

    if not (root / "scripts" / "validate.py").is_file():
        print(f"not a SK_EFT_Hawking checkout: {root}", file=sys.stderr)
        return 2

    owed: list[str] = []
    print(f"registration sites for {check!r}:\n")
    for label, rel, kind in SITES:
        state = _hit(root, rel, kind, check)
        if state is None:
            mark, note = "  --", "not applicable to this check"
        elif state:
            mark, note = "  ok", rel
        else:
            mark, note = "OWED", rel
            if kind != "optional":
                owed.append(label)
        print(f"  [{mark}] {label:<42} {note}")

    # Numeric floors: report the delta, never a verdict — only the author knows
    # whether a check is being added or removed, and the two move it opposite ways.
    print("\n  numeric floors — confirm the direction yourself:")
    cfg = root / "scripts" / "validation" / "_config.py"
    if cfg.is_file():
        m = re.search(r"CI_MIN_CHECKS_RUN:\s*int\s*=\s*(\d+)", cfg.read_text())
        if m:
            print(f"    CI_MIN_CHECKS_RUN = {m.group(1)}  "
                  f"(+1 when adding a non-CI_SKIP check, -1 when removing one)")
    mut = root / "tests" / "test_d5_mutation_obligation.py"
    if mut.is_file():
        m = re.search(r"FIXTURE_ONLY_CEILING\s*=\s*(\d+)", mut.read_text())
        if m:
            print(f"    FIXTURE_ONLY_CEILING = {m.group(1)}  "
                  f"(unchanged if the new check is PRODUCTION_SEEDED; +1 if fixture-only)")

    if owed:
        print(f"\n{len(owed)} site(s) owed: {', '.join(owed)}")
        return 1
    print("\nall required sites satisfied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
