#!/usr/bin/env python3
"""SessionStart re-injection — the Phase-5q.F durability fix.

After a context boundary (`source` is compact|resume), re-inject the
role-appropriate goal/roadmap directive so a managed `/goal` loop keeps the big
picture across the compaction (the exact failure mode that derailed 5q.F).
Default-inert (no marker, or a subagent) + fail-open.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import read_event, read_marker, emit_context


def main() -> int:
    ev = read_event()
    if (ev.get("source") or "") not in ("compact", "resume"):
        return 0
    m = read_marker(ev)
    if not m:
        return 0
    goal = m.get("goal", "")
    roadmap = m.get("roadmap_path", "")
    notebook = m.get("notebook_path", "")
    src = ev.get("source")
    if m.get("role") == "lead":
        ctx = (
            f"[dev-harness] You LEAD an autonomous /goal dev loop; context was just "
            f"restored ({src}). Before acting, re-read the native task list and the "
            f"roadmap ({roadmap}); coordinate and synthesize the next increment — do not "
            f"start building yourself. Goal: {goal}"
        )
    else:
        ctx = (
            f"[dev-harness] Autonomous /goal dev loop; context was just restored ({src}). "
            f"The scope is SETTLED — do the next increment of real work THIS turn; a "
            f"stop-hook firing is a GO signal, never a cue to stop, hold, or re-scope. "
            f"Re-read the roadmap ({roadmap}) and lab notebook ({notebook}), then continue "
            f"the next brick. Legitimate stops only: a kernel-checked no-go or a genuine "
            f"user decision. Goal: {goal}"
        )
    emit_context("SessionStart", ctx)
    return 0


if __name__ == "__main__":
    sys.exit(main())
