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

⚠️ **`\\bibitem` IS NOT THE DECIDER — resolvability is.** This checker originally asked
"does a `\\bibitem` exist for this key", which is a PROXY for the question that matters,
"does this citation resolve for a reader". The two come apart on any draft that uses
BibTeX: `\\bibliography{name}` + `papers/<bundle>/<name>.bib` resolves perfectly and
contains no `\\bibitem` at all. Measured 2026-08-15: D8 and D10 each carry 17 BibTeX
entries covering every key they cite, and this checker reported all 34 as undefined —
34 of the 209 open blocking findings on the submission bundles, on two Tier-1 bundles,
every one of them a false positive it had generated itself.

`readiness_gates.py:_eval_citation_integrity` already knew D8/D10 were BibTeX papers
(corroborate-before-passing branch, 2026-08-09). This script did not, which is how a
`verify` command kept re-asserting a defect the corpus did not have. Keys now resolve
against `\\bibitem` **or** the `.bib` named by `\\bibliography{}`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent

_COMMENT = re.compile(r"(?<!\\)%.*$", re.M)
_CITE = re.compile(r"\\cite[a-zA-Z]*\{([^}]*)\}")
_BIBITEM = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]*)\}")
_BIBLIOGRAPHY = re.compile(r"\\bibliography\{([^}]*)\}")
_BIBENTRY = re.compile(r"@[A-Za-z]+\s*\{\s*([^,\s]+)\s*,")


def defined_keys(tex_path: Path, body: str) -> set[str]:
    """Every key a reader can resolve: inline `\\bibitem`s plus any BibTeX database.

    `\\bibliography{a,b}` may name several databases, relative to the draft's own
    directory, with or without the `.bib` suffix. A named-but-absent database is
    simply contributed nothing — its keys then surface as undefined, which is the
    honest answer rather than a crash.
    """
    defined = set(_BIBITEM.findall(body))
    for match in _BIBLIOGRAPHY.finditer(body):
        for name in (n.strip() for n in match.group(1).split(",")):
            if not name:
                continue
            bib = tex_path.parent / (name if name.endswith(".bib") else f"{name}.bib")
            if bib.is_file():
                defined |= set(_BIBENTRY.findall(bib.read_text(errors="replace")))
    return defined


def undefined_keys(tex_path: Path) -> list[str]:
    """Cited-but-unresolvable keys, in stable order."""
    body = _COMMENT.sub("", tex_path.read_text(errors="replace"))
    cited: set[str] = set()
    for match in _CITE.finditer(body):
        cited |= {k.strip() for k in match.group(1).split(",") if k.strip()}
    return sorted(cited - defined_keys(tex_path, body))


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
        print(f"{args.bundle}: {target} resolves")
        return 0

    print(f"{args.bundle}: {len(missing)} cited key(s) resolve to nothing "
          f"(no bibitem, no BibTeX entry): {', '.join(missing)}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
