#!/usr/bin/env python3
"""Report citation keys used in a draft's reader-visible prose with no `\\bibitem`.

Written as the `verify` mechanism for the 2026-08-12 citation-integrity findings
(ADR-012 D1: a finding names a runnable command that proves it fixed). Exits 1 when
any cited key is undefined, so it can be used directly as a gate.

⚠️ **Exact-key matching, never substring.** A substring test on this corpus is wrong:
`Crossley2017` matches `Crossley2017II`, which produced a false finding during the
2026-08-12 triage. Keys are split out of `\\cite*{a,b}` and compared whole.

⚠️ **LaTeX comments are stripped first.** A key surviving only inside a `%` block is
not cited by the manuscript — counting it credits the draft for a reference no reader
sees. Same reasoning as `bundle_lean_module_coverage`'s comment handling.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent

_COMMENT = re.compile(r"(?<!\\)%.*$", re.M)
_CITE = re.compile(r"\\cite[a-zA-Z]*\{([^}]*)\}")
_BIBITEM = re.compile(r"\\bibitem\{([^}]*)\}")


def undefined_keys(tex_path: Path) -> list[str]:
    """Cited-but-undefined keys, in stable order."""
    body = _COMMENT.sub("", tex_path.read_text(errors="replace"))
    cited: set[str] = set()
    for match in _CITE.finditer(body):
        cited |= {k.strip() for k in match.group(1).split(",") if k.strip()}
    return sorted(cited - set(_BIBITEM.findall(body)))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("bundle", help="bundle code, e.g. D10")
    ap.add_argument("--key", help="check only this key")
    args = ap.parse_args()

    tex = PROJECT_ROOT / "papers" / args.bundle / "paper_draft.tex"
    if not tex.is_file():
        print(f"no draft at {tex}", file=sys.stderr)
        return 2

    missing = undefined_keys(tex)
    if args.key:
        missing = [k for k in missing if k == args.key]

    if not missing:
        target = f"`{args.key}`" if args.key else "every cited key"
        print(f"{args.bundle}: {target} resolves to a bibitem")
        return 0

    print(f"{args.bundle}: {len(missing)} cited key(s) with no bibitem: {', '.join(missing)}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
