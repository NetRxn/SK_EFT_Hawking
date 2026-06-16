#!/usr/bin/env python3
"""PostToolUse(Edit|Write) de-pollution guard.

When a managed orchestrator edits its own settled-goal source-of-truth doc (the
marker's roadmap/notebook) and introduces escape-language, warn and flag for
revert — catching the exact Phase-5q.F roadmap re-pollution at write time. A
linter, not a hijack: it nudges via additionalContext; it never blocks the
edit. Fail-open.

Scope note: applies to the managed orchestrator (solo or lead) editing the
marker's own source-of-truth docs. 5q.F was a *solo* loop re-polluting its own
roadmap, so restricting to team-leads only would miss the motivating case.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import read_event, read_marker, emit_context

ESCAPE = re.compile(
    r"(?i)(person[- ]?years?|precluded\b|no foothold|re-?scope|this is a wall|"
    r"\binfeasible\b|multi[- ]?(?:week|month)s?\b[^.\n]{0,40}\b(?:stop|defer|halt|"
    r"next session|too long))"
)


def _doc_basenames(m: dict) -> set:
    return {os.path.basename(p) for p in (m.get("roadmap_path"), m.get("notebook_path")) if p}


def _new_text(ev: dict) -> str:
    ti = ev.get("tool_input") or {}
    return ti.get("content") or ti.get("new_string") or ""


def main() -> int:
    ev = read_event()
    m = read_marker(ev)
    if not m:
        return 0
    fpath = (ev.get("tool_input") or {}).get("file_path") or ""
    if not fpath or os.path.basename(fpath) not in _doc_basenames(m):
        return 0  # not a source-of-truth doc → inert
    hits = sorted({mo.group(0).lower() for mo in ESCAPE.finditer(_new_text(ev))})
    if not hits:
        return 0
    emit_context(
        "PostToolUse",
        f"[dev-harness] ⚠ The edit to the settled-goal source-of-truth doc "
        f"({os.path.basename(fpath)}) introduced escape-language ({', '.join(hits)}). "
        f"This is the Phase-5q.F re-pollution antipattern: the goal's scope is settled "
        f"and not yours to re-litigate inside the tracked doc. Revert that wording and "
        f"continue the next brick. Record any genuine blocker in the lab notebook as a "
        f"fact to work, not as goal re-scoping.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
