#!/usr/bin/env python3
"""Whitespace-normalized phrase search across prose and source files.

WHY THIS EXISTS
---------------
A line-wise ``grep`` cannot find a phrase that a text editor or a formatter has
wrapped across a newline. That is not a hypothetical: it cost this project two
Stage-13 rounds.

In the 2026-07-31 D12 round-3 review, a confabulated citation subtitle
("Information theory and hypothesis testing, in Lean") was remediated at two of
its four sites. The remediation sweep used ``grep`` and reported the phrase gone.
It was not gone — it survived in the primary-source cache header and in the
bundle's ``prior_art_novelty.md``, in both cases broken across a line boundary.
The three hits ``grep`` *did* return were all records of the fix, which made the
sweep look thorough while it was in fact blind to every live assertion.

A whitespace-normalized scan finds all five.

USE THIS, NOT ``grep``, for any prose-phrase sweep during remediation --- and in
particular before declaring a Stage-13 finding closed.

USAGE
-----
    uv run python scripts/find_phrase.py "some phrase that may be wrapped"
    uv run python scripts/find_phrase.py --roots papers docs "phrase"
    uv run python scripts/find_phrase.py --ignore-case "phrase"

Exit status is 1 when at least one match is found (so it composes with shell
``&&``/``||``), 0 when clean.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

DEFAULT_ROOTS = ("papers", "docs", "src", "scripts", "lean/SKEFTHawking", "notebooks")

# Workspace-level trees that live beside the repo, not inside it. The
# primary-source cache is here, and it is exactly where the round-3 finding hid.
DEFAULT_WORKSPACE_ROOTS = ("Lit-Search",)

TEXT_SUFFIXES = {
    ".tex", ".md", ".py", ".lean", ".txt", ".json", ".jsonl", ".ipynb",
    ".yaml", ".yml", ".toml", ".cfg", ".sh",
}

SKIP_DIR_PARTS = {".lake", ".git", "__pycache__", ".venv", "node_modules", ".mypy_cache"}


def _iter_files(roots: list[Path]) -> list[Path]:
    out: list[Path] = []
    for root in roots:
        if not root.exists():
            continue
        if root.is_file():
            out.append(root)
            continue
        for p in root.rglob("*"):
            if not p.is_file():
                continue
            if p.suffix not in TEXT_SUFFIXES:
                continue
            if SKIP_DIR_PARTS & set(p.parts):
                continue
            out.append(p)
    return out


def _normalize(text: str) -> tuple[str, list[int]]:
    """Collapse every whitespace run to a single space.

    Returns the normalized text plus a map from each normalized character index
    back to its offset in the original, so hits can be reported at a real line.
    """
    buf: list[str] = []
    idx: list[int] = []
    prev_ws = False
    for i, ch in enumerate(text):
        if ch.isspace():
            if not prev_ws:
                buf.append(" ")
                idx.append(i)
            prev_ws = True
        else:
            buf.append(ch)
            idx.append(i)
            prev_ws = False
    return "".join(buf), idx


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("phrase", help="phrase to find; internal whitespace is treated as flexible")
    ap.add_argument("--roots", nargs="*", default=None,
                    help="repo-relative roots to scan (default: papers docs src scripts lean notebooks)")
    ap.add_argument("--ignore-case", action="store_true")
    ap.add_argument("--no-workspace", action="store_true",
                    help="skip the workspace-level Lit-Search tree")
    ap.add_argument("--context", type=int, default=90, help="context chars either side")
    args = ap.parse_args()

    roots = [REPO / r for r in (args.roots or DEFAULT_ROOTS)]
    if not args.no_workspace and args.roots is None:
        try:
            sys.path.insert(0, str(REPO))
            from src.core.workspace import find_workspace
            ws = find_workspace()
            roots += [ws / r for r in DEFAULT_WORKSPACE_ROOTS]
        except Exception as exc:  # pragma: no cover
            print(f"note: workspace roots skipped ({type(exc).__name__}: {exc})", file=sys.stderr)

    needle, _ = _normalize(args.phrase)
    needle = needle.strip()
    if args.ignore_case:
        needle = needle.lower()

    hits = 0
    for path in sorted(_iter_files(roots)):
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        norm, idx = _normalize(raw)
        hay = norm.lower() if args.ignore_case else norm
        start = 0
        while True:
            j = hay.find(needle, start)
            if j < 0:
                break
            orig = idx[j] if j < len(idx) else 0
            line = raw.count("\n", 0, orig) + 1
            lo = max(0, j - args.context)
            hi = min(len(norm), j + len(needle) + args.context)
            try:
                rel = path.relative_to(REPO)
            except ValueError:
                rel = path
            print(f"{rel}:{line}: …{norm[lo:hi]}…")
            hits += 1
            start = j + max(1, len(needle))

    print(f"\n{hits} match(es) — whitespace-normalized "
          f"(a line-wise grep may report fewer)", file=sys.stderr)
    return 1 if hits else 0


if __name__ == "__main__":
    raise SystemExit(main())
