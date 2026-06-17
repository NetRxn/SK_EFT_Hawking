#!/usr/bin/env python3
"""SessionStart re-injection — the Phase-5q.F durability fix (v4.0).
On source=compact|resume, re-inject the SHARED re-orientation payload (contract B —
build_reorientation_payload: the /goal condition + 're-read CLAUDE.md' + active System-2
issues + decision heuristics) for THIS session's managed marker, wrapped with UNIFORM,
ROLE-AGNOSTIC framing (spec 4/5 review item 2 — the harness does NOT prescribe
build-vs-delegate-vs-team; that is the agent's emergent judgment, unknowable at launch,
so the SAME settled posture is injected regardless of the marker's `role`) + a BEST-EFFORT
first-turn self-check directive (review A3 — its ordering vs /goal's restored continuation
is not doc-guaranteed; the re-attached posture core is the durable backstop). The marker's
`role` is DESCRIPTIVE METADATA ONLY (logging / harvest attribution — spec 5/A.5): it is
READ into the marker but NEVER acted on here (no role branch, no ~/.claude/teams lookup).
Default-inert + fail-open. startup/clear are intentionally inert (startup has fresh
CLAUDE.md; /clear also clears /goal). Runs under the repo's uv Python >=3.14."""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import (read_event, read_marker, emit_context, repo_root,
                            build_reorientation_payload, harvest_state_path)

# First-turn self-check (13): the per-compaction analog of the once-per-wave review.
# BEST-EFFORT (review A3): this directive lands in the SessionStart(compact) additionalContext,
# but whether the model acts on it BEFORE /goal's own restored continuation reason drives turn 1
# is NOT doc-guaranteed — so it is a best-effort re-grounding, not a hard gate. (The always-on
# posture core, which re-attaches every compaction, is the durable backstop. The harness self-test
# Task 10 Step 5 confirms, on a real compaction, that the directive is present AND acted on first.)
_SELF_CHECK = ("BEST-EFFORT FIRST-TURN SELF-CHECK: ideally, before resuming, re-read the above "
               "(goal prompt + CLAUDE.md + active issues + heuristics), confirm you are aligned "
               "with the SETTLED scope, then do the next increment. If /goal's restored "
               "continuation already drove this turn, do the self-check at the first natural break.")


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
            return ("\n\n⚠ System-2 harvest hasn't run in ~%.0f day(s) — start its host "
                    "(/skeft-qa:harvest) so the active-issues view stays fresh."
                    % (overdue_s / 86400.0))
    except Exception:
        pass
    return ""


def compose_directive(src, goal, roadmap, notebook, payload):
    """Wrap the shared re-orientation `payload` with UNIFORM, ROLE-AGNOSTIC framing + the
    best-effort first-turn self-check (review A3 — not a hard ordering gate). There is NO
    `role` parameter and NO role branch (spec 4/5 review item 2): the harness injects the
    SAME settled posture for a solo loop or a team lead, and never prescribes
    build-vs-delegate-vs-team — that is the agent's emergent judgment, unknowable at launch."""
    frame = (
        f"[dev-harness] Autonomous /goal dev loop; context was just restored ({src}). "
        f"The scope is SETTLED — do the next increment of real work THIS turn; a "
        f"stop-hook firing is a GO signal, never a cue to stop, hold, or re-scope. "
        f"Re-read the roadmap ({roadmap}) and lab notebook ({notebook}), then continue "
        f"the next brick. Legitimate stops only: a kernel-checked no-go or a genuine "
        f"user decision."
    )
    return frame + "\n\n" + payload + "\n\n" + _SELF_CHECK


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
        m.get("goal", ""), m.get("roadmap_path", ""), m.get("notebook_path", ""), payload)
    # Drift warning (cadence-driven, spec 6.3 / A.4): append a one-line nudge if the System-2
    # harvest is overdue. Absent harvest_state (first run) -> silent. Best-effort — a read
    # error never blocks the durability re-injection. Resolve harvest_state from the SAME
    # ev["cwd"]-resolved root as the marker (consistent with read_marker).
    try:
        st = json.loads(harvest_state_path(root).read_text()) if root is not None else {}
    except Exception:
        st = {}
    ctx += drift_note(st.get("last_run_ts"), time.time(), st.get("cadence_hours"))
    emit_context("SessionStart", ctx)
    return 0


if __name__ == "__main__":
    sys.exit(main())
