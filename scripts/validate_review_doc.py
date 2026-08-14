#!/usr/bin/env python3
"""Validate ONE review document against the marker contract, before it is committed.

WHY THIS EXISTS
---------------
The rules a review document must satisfy are real, enforced, and stated nowhere a
reviewer agent can act on them. A fresh-context agent writes a Stage-13 report, the
report is committed, and `review_severity_declared` fails afterwards — at gate time,
in a full-suite run, attributed to whoever next runs the suite rather than to the
author.

Measured on 2026-08-14: one dispatched review broke the gate two ways at once —
eleven `Blocked-by:` tokens that resolve to nothing (`none`, a bare `3.1`), and
no-finding section headings at `###` that the checker counts as findings and then
finds no severity for. Neither is inferable from the agent's own prompt.

⛔ THIS ADDS NO NEW PREDICATE. It runs the registered checks and filters their
findings to one path. A second implementation of the marker rules would be a second
mechanism beside the gate — the failure `CLAUDE.md` rule 1 names — and would drift
from it the first time either changed. If a rule is wrong, fix it in
`scripts/validation/checks/reviews.py`; this file will follow automatically.

USAGE
-----
    uv run python scripts/validate_review_doc.py papers/AutomatedReviews/<dir>/<T>.md

Exit 0 = the document satisfies the contract. Exit 1 = it does not, and each problem
is printed with the rule it violates.

THE CONTRACT, STATED FOR AUTHORS
--------------------------------
1. **Every finding heading declares `- **Severity:** <value>`.** A finding heading is
   ANY `###`/`####`/`#####` heading. A section that reports NO findings must therefore
   be `##`, not `###` — adding a Severity line to it instead would mint a phantom
   finding node.
2. **Severity and Lane values come from the declared vocabularies.** A typo is not a
   cosmetic defect: an unmappable severity lands the finding as `advisory`, and an
   unmappable lane routes it to no worker at all.
3. **`Blocked-by:` names a minted finding id or a valued release scheme.** ABSENCE IS
   VALID — omit the line entirely when nothing blocks the finding. `none` is not a
   value; a token nothing can satisfy makes the finding read WAITING when it is STUCK,
   and it reaches no worker either way.
4. **`Verify:` is ONE command.** `close_finding.py` parses it as a single line and
   refuses a closure whose verify does not match, so a two-command line strands the
   finding.
"""
from __future__ import annotations

import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
sys.path.insert(0, str(SCRIPT_DIR.parent))

#: The registered checks whose findings are keyed by review-document path. Extend this
#: when a new check gains that property — never by copying its predicate here.
_REVIEW_DOC_CHECKS = ("review_severity_declared", "review_docs_mint_findings")


def validate(target: Path) -> tuple[bool, list[str]]:
    """Return (ok, problems) for one review document, using the registered checks."""
    from validation.checks import reviews as rv

    try:
        rel = str(target.resolve().relative_to(Path.cwd().resolve()))
    except ValueError:
        rel = str(target)

    problems: list[str] = []
    for name in _REVIEW_DOC_CHECKS:
        fn = getattr(rv, f"check_{name}", None)
        if fn is None:                      # a renamed check must not pass silently
            problems.append(
                f"{name}: not found in validation.checks.reviews — this validator is "
                f"stale against the gate it delegates to, so it cannot vouch for anything")
            continue
        result = fn()
        for d in result.details:
            if d.passed:
                continue
            # Details are keyed by the document's repo-relative path; the summary row
            # is corpus-wide and belongs to no single document.
            if d.name == "summary":
                continue
            if rel.endswith(d.name) or d.name.endswith(rel) or target.name in d.name:
                problems.append(f"[{name}] {d.message}")
    return (not problems), problems


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if len(args) != 1:
        print(__doc__)
        return 2
    target = Path(args[0])
    if not target.is_file():
        print(f"✗ {target} is not a file")
        return 2

    ok, problems = validate(target)
    if ok:
        print(f"✓ {target} satisfies the review-document marker contract")
        return 0
    print(f"✗ {target} violates the marker contract:\n")
    for p in problems:
        print(f"  {p}\n")
    print("See this script's docstring for the contract, or "
          "scripts/validation/checks/reviews.py for the enforcing predicates.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
