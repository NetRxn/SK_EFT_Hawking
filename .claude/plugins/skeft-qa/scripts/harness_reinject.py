#!/usr/bin/env python3
"""SessionStart re-injection — the Phase-5q.F durability fix (v4.0).
On source=compact|resume, re-inject the SHARED re-orientation payload (contract B —
build_reorientation_payload: the /goal condition + the always-on RE-ANCHOR + the live FRONTIER +
a MANDATED PRE_DECISIONS.md read + the OPTIONAL staleness-labeled coaching block) for THIS session's
managed marker, wrapped with UNIFORM, ROLE-AGNOSTIC framing (spec 4/5 review item 2 — the harness does
NOT prescribe build-vs-delegate-vs-team; that is the agent's emergent judgment, unknowable at launch,
so the SAME settled posture is injected regardless of the marker's `role`). The first-turn self-check
is folded into the payload's RE_ANCHOR (no separate trailing directive). The marker's
`role` is DESCRIPTIVE METADATA ONLY (logging / harvest attribution — spec 5/A.5): it is
READ into the marker but NEVER acted on here (no role branch, no ~/.claude/teams lookup).
Default-inert + fail-open. startup/clear are intentionally inert (startup has fresh
CLAUDE.md; /clear also clears /goal). Runs under the repo's uv Python >=3.14."""

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import (
    read_event,
    read_marker,
    emit_context,
    repo_root,
    build_reorientation_payload,
    harvest_state_path,
)

# The first-turn self-check is folded into the payload's always-on RE_ANCHOR (harness_common.RE_ANCHOR)
# — a concrete "confirm the close-path before resuming the summary's tactic", rather than a separate
# hedged trailing directive. So there is no longer a _SELF_CHECK appended here.


def drift_note(last_ts, now, cadence_hours):
    """Pure (no IO; unit-testable). Return a one-line drift warning if the System-2 harvest is
    overdue (now - last_ts > 2x cadence_hours), else ''. Missing last_ts/cadence -> '' (first
    run stays silent). The cadence comes from harvest_state (written each harvest run), NOT a
    hardcoded literal (spec 6.3 / A.4)."""
    try:
        if not last_ts or not cadence_hours:
            return ""
        overdue_s = float(now) - float(last_ts)
        if overdue_s > 2.0 * float(cadence_hours) * 3600.0:
            return (
                "\n\n⚠ System-2 harvest hasn't run in ~%.0f day(s) — start its host "
                "(/skeft-qa:harvest) so the active-issues view stays fresh."
                % (overdue_s / 86400.0)
            )
    except Exception:
        pass
    return ""


def notebook_note(notebook_path, repo):
    """Read-only nudge (the SessionStart half of the lab-notebook self-leveling backstop):
    if the active shard is over the token budget, the INDEX lacks the DECISIONS block, or the
    FRONTIER SHA is stale vs git HEAD, surface a one-line warning so it can't go silent. Never
    mutates the notebook (self-improving, never self-mutating); best-effort + guarded so a read
    error never blocks the durability re-injection."""
    try:
        if not notebook_path:
            return ""
        import notebook_lib as nl  # same scripts dir (sys.path already inserted at import time)
        from pathlib import Path

        res = nl.op_check(str(Path(notebook_path).parent), repo=repo)
        warns = res.get("warnings", [])
        if warns:
            return "\n\n⚠ lab-notebook: " + " ".join(warns) + " (run /skeft-qa:notebook sync|shard)"
    except Exception:
        pass
    return ""


def compose_directive(src, goal, roadmap, notebook, payload):
    """Wrap the shared `payload` with a MINIMAL, role-agnostic frame: a single GO-signal line — the
    irreducible anti-over-defer posture, kept INJECTED as a backstop even if the mandated
    PRE_DECISIONS.md read is skipped. The concrete re-orientation lives in the payload (RE_ANCHOR +
    the live FRONTIER + the coaching block); the full discipline is the mandated read. No `role`
    parameter / branch (spec 4/5): the SAME settled posture for a solo loop or a team lead — the
    harness never prescribes build-vs-delegate-vs-team (the agent's emergent judgment)."""
    frame = (
        f"[dev-harness] Autonomous /goal loop; context restored ({src}). Scope is SETTLED — do the "
        f"next increment of real work THIS turn; a stop-hook firing is a GO signal, not a cue to "
        f"stop/hold/re-scope. Roadmap: {roadmap}. Re-orient from the RE-ANCHOR + coaching block below, "
        f"then ship the next brick (open the notebook INDEX {notebook} only for deeper context — "
        f"don't re-read the full log)."
    )
    return frame + "\n\n" + payload


def main():
    ev = read_event()
    if (ev.get("source") or "") not in ("compact", "resume"):
        return 0
    m = read_marker(ev)
    if not m:
        return 0
    # `role` is read into the marker but is descriptive-only (spec 5/A.5) — NOT passed
    # to compose_directive and never used to branch the injected framing.
    root = repo_root(ev.get("cwd"))
    payload = build_reorientation_payload(m, root)
    ctx = compose_directive(
        ev.get("source", ""),
        m.get("goal", ""),
        m.get("roadmap_path", ""),
        m.get("notebook_path", ""),
        payload,
    )
    # Drift warning (cadence-driven, spec 6.3 / A.4): append a one-line nudge if the System-2
    # harvest is overdue. Absent harvest_state (first run) -> silent. Best-effort — a read
    # error never blocks the durability re-injection. Resolve harvest_state from the SAME
    # ev["cwd"]-resolved root as the marker (consistent with read_marker).
    try:
        st = (
            json.loads(harvest_state_path(root).read_text()) if root is not None else {}
        )
    except Exception:
        st = {}
    ctx += drift_note(st.get("last_run_ts"), time.time(), st.get("cadence_hours"))
    ctx += notebook_note(m.get("notebook_path", ""), root)
    emit_context("SessionStart", ctx)
    return 0


if __name__ == "__main__":
    sys.exit(main())
