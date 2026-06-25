#!/usr/bin/env python3
"""
Aristotle submission CLI (SAFE, partial-submission process — ADR-006).

This is the canonical Aristotle CLI. As of 2026-06-25 (ADR-006) it implements
the SAFE process and the dangerous full-project process has been retired:

  - Submission stages a MINIMAL Lean project — only the transitive import
    closure of the target sorry file(s) — never the full ~1,172-file project.
  - Re-incorporation is retrieve -> review -> hand-graft ONLY the target
    theorem bodies -> verification gauntlet (lake build + axiom/kernel-purity
    audit + validate.py + tests). It never whole-file-overwrites the tree.

The previous FULL-PROJECT CLI (full upload + blind `--integrate` whole-file
copy) is archived, verbatim and disabled, at:
    scripts/archive/submit_to_aristotle.py
It is retained — not deleted — because it is the Methods-of-record for prior
papers (papers/I1, papers/paper15_methodology, papers/D1). See
docs/adrs/ADR-006-aristotle-submission-rewrite.md.

STATUS: the safe engine (src/core/aristotle_submit.py) is under construction
(ADR-006 step 2). Until it lands, only the harmless `--dry-run` sorry scan is
available here; every submission/integration path is refused, by design.

Usage:
    # List current sorry gaps in the Lean source (safe, no network):
    uv run python scripts/submit_to_aristotle.py --dry-run
"""

import argparse
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
LEAN_SRC = PROJECT_ROOT / "lean" / "SKEFTHawking"
ARCHIVE = "scripts/archive/submit_to_aristotle.py"
ADR = "docs/adrs/ADR-006-aristotle-submission-rewrite.md"


def _is_sorry_line(line: str) -> bool:
    s = line.strip()
    return s in ("sorry", "by sorry") or s.endswith(":= by sorry")


def find_sorry_files() -> dict[str, int]:
    """Scan Lean source for sorry tactics. Returns {relative_path: count}."""
    out: dict[str, int] = {}
    for f in sorted(LEAN_SRC.rglob("*.lean")):
        count = sum(1 for line in f.read_text().splitlines() if _is_sorry_line(line))
        if count:
            out[str(f.relative_to(LEAN_SRC))] = count
    return out


def dry_run() -> None:
    sorry_files = find_sorry_files()
    if not sorry_files:
        print("No sorry gaps found in lean/SKEFTHawking/.")
        return
    total = sum(sorry_files.values())
    print(f"Current sorry gaps: {total} across {len(sorry_files)} file(s):")
    for fname, n in sorted(sorry_files.items(), key=lambda x: -x[1]):
        print(f"  {fname}: {n}")
    print(
        "\nNOTE: this is the dry-run sorry scan only. The safe partial-submission "
        "path (minimal-closure staging) is under construction — see "
        f"{ADR}."
    )


def _refuse(flag: str) -> None:
    sys.stderr.write(
        f"\n[ADR-006] `{flag}` is not available from this CLI.\n"
        "  The full-project submission + blind whole-file --integrate paths were\n"
        "  foot-guns at the current substrate scale and have been retired.\n"
        f"  The SAFE partial-submission + verify-then-graft engine is under\n"
        f"  construction (ADR-006 step 2). See {ADR}.\n"
        f"  To reproduce the OLD full-project behaviour (prior-paper provenance only),\n"
        f"  see the archived, disabled copy at {ARCHIVE}.\n\n"
    )
    raise SystemExit(2)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Aristotle submission CLI (safe partial-submission process; ADR-006)."
    )
    parser.add_argument("--dry-run", action="store_true",
                        help="List current sorry gaps in the Lean source (safe, no network).")
    # Retired full-project flags — accepted so we can emit a precise pointer, never executed.
    for flag in ("--submit", "--integrate", "--resume", "--force"):
        parser.add_argument(flag, action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--retrieve", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--priority", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--target", type=str, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()

    if args.dry_run:
        dry_run()
        return

    for flag, val in (
        ("--submit", args.submit), ("--integrate", args.integrate),
        ("--resume", args.resume), ("--force", args.force),
        ("--retrieve", args.retrieve), ("--priority", args.priority),
        ("--target", args.target),
    ):
        if val:
            _refuse(flag)

    parser.print_help()


if __name__ == "__main__":
    main()
