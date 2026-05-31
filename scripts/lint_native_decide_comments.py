#!/usr/bin/env python3
"""
lint_native_decide_comments.py — detect comment-provenance artifacts left by a
blind ``native_decide`` → ``decide`` substitution.

Background
----------
The 2026-05-30 ``native_decide`` trust-surface cleanup (ADR-002) converted ~63
Bucket-B modules with a file-wide ``perl -i -pe 's/\\bnative_decide\\b/decide/g'``.
That blind replace also rewrote the word ``native_decide`` inside *comments and
docstrings* of files whose proofs were NOT converted, producing false /
self-contradictory provenance text — e.g. "kernel-pure, no ``decide``" (nonsense:
it meant "no ``native_decide``"), or "``decide`` / ``decide``" duplications, or
performance claims that ``decide`` is tractable on deg-16 cyclotomic matrices
(impossible — the ℚ-wall). Those were repaired in the 2026-05-31 follow-up commit.

This linter is the standing backstop so that class cannot silently reappear,
*however* it is introduced (not just via the perl driver). It is a pure text
scan — no Lean, sub-second — intended to be run by hand after any
``native_decide``-touching edit and before commit (ADR-002 §"2026-05-31 process
hardening"). It is deliberately NOT registered in ``validate.py``'s standing
suite; it is a targeted tool for one specific, infrequent maintenance operation.

What it flags
-------------
ERROR (always a mangled substitution — zero expected false positives):
    ``decide`` / ``decide``      ``decide``/``decide``      ``decide`` or ``decide``
  A duplicated alternative collapses to one tactic; the pair is the fingerprint
  of "native_decide / decide" or "decide / native_decide" having both sides
  rewritten to ``decide``.

WARN (contrastive phrase almost always meant to read ``native_decide``; a Lean
comment contrasting kernel ``decide`` against the compiler-trust evaluator):
    no ``decide``     never ``decide``     not ``decide``     tracked ``decide``
  Legitimate prose says "without ``native_decide``", "no ``native_decide``", or
  simply omits the contrast — so each WARN is review-required, not auto-wrong.

Known blind spot (documented, not auto-detectable)
--------------------------------------------------
A comment asserting ``decide`` tractability/timeout on a high-degree cyclotomic
type (deg ≥ 8: QCyc16/40/80, QCyc*Ext, or matrices over them) is wrong — kernel
``decide`` cannot reduce ℚ arithmetic at that degree — but "30-deep ``decide``"
is not textually distinguishable from a legitimate finite ``decide``. This class
(Rouabah-style) is caught only by the **mandatory full-diff read** + the
``#print axioms`` discipline (a genuinely-converted high-degree theorem fails to
build or retains the native axiom). See ADR-002.

Usage
-----
    uv run python scripts/lint_native_decide_comments.py           # ERROR-tier gates
    uv run python scripts/lint_native_decide_comments.py --strict  # WARN also gates
    uv run python scripts/lint_native_decide_comments.py --quiet   # only print hits

Exit status: 1 if any ERROR-tier hit (or any hit under --strict), else 0.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Resolve the Lean source root relative to this script (scripts/ -> repo -> lean/).
REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO_ROOT / "lean" / "SKEFTHawking"

# ERROR tier: duplicated-alternative artifacts. The `\s*/\s*` form also catches
# the no-space "`decide`/`decide`" variant.
ERROR_PATTERNS = [
    (re.compile(r"`decide`\s*/\s*`decide`"), "duplicated `decide` / `decide`"),
    (re.compile(r"`decide`\s+or\s+`decide`"), "duplicated `decide` or `decide`"),
]

# WARN tier: contrastive phrases that almost always lost their `native_` prefix.
# `\b` before the keyword avoids matching inside larger words; the literal
# backtick-delimited `decide` cannot match inside `native_decide` (the backtick
# falls between "native" and "decide"), so correct text is never flagged.
WARN_PATTERNS = [
    (re.compile(r"\b(?:no|never|not)\s+`decide`"),
     "contrastive 'no/never/not `decide`' — did you mean `native_decide`?"),
    (re.compile(r"\btracked\s+`decide`"),
     "'tracked `decide`' — tracked compiler-trust deps are `native_decide`"),
]


def scan_file(path: Path) -> tuple[list[tuple[int, str, str]], list[tuple[int, str, str]]]:
    """Return (errors, warns); each entry is (lineno, message, line_text)."""
    errors: list[tuple[int, str, str]] = []
    warns: list[tuple[int, str, str]] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError) as exc:  # pragma: no cover - surfaced, not hidden
        print(f"WARNING: could not read {path}: {exc}", file=sys.stderr)
        return errors, warns
    for lineno, line in enumerate(text.splitlines(), start=1):
        for pat, msg in ERROR_PATTERNS:
            if pat.search(line):
                errors.append((lineno, msg, line.strip()))
        for pat, msg in WARN_PATTERNS:
            if pat.search(line):
                warns.append((lineno, msg, line.strip()))
    return errors, warns


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--strict", action="store_true",
                        help="WARN-tier hits also cause a nonzero exit")
    parser.add_argument("--quiet", action="store_true",
                        help="suppress the summary line; print only hits")
    args = parser.parse_args()

    if not LEAN_ROOT.is_dir():
        print(f"ERROR: Lean source root not found: {LEAN_ROOT}", file=sys.stderr)
        return 2

    total_errors = 0
    total_warns = 0
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        errors, warns = scan_file(path)
        rel = path.relative_to(REPO_ROOT)
        for lineno, msg, line in errors:
            print(f"ERROR {rel}:{lineno}: {msg}\n    {line}")
        for lineno, msg, line in warns:
            print(f"WARN  {rel}:{lineno}: {msg}\n    {line}")
        total_errors += len(errors)
        total_warns += len(warns)

    if not args.quiet:
        print(f"\nlint_native_decide_comments: {total_errors} error(s), "
              f"{total_warns} warning(s) across {sum(1 for _ in LEAN_ROOT.rglob('*.lean'))} files.")

    if total_errors:
        return 1
    if args.strict and total_warns:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
