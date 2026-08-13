"""What `/goal` loops are running, from state the harness already writes (ADR-012 D20).

⚠️ **NO NEW WRITER.** Everything read here is produced by the dev-harness on every loop. D20's
argument for building this at all is that the state is *"machine-readable info we're already
using in our hooks/context bootstrap and harvest infrastructure"*, so the pane is a reader and
nothing more.

⚠️ **AN EMPTY ROSTER IS NOT "NO LOOPS RUNNING", AND THIS MODULE REFUSES TO CONFLATE THEM.**
`.claude/dev-harness/` is gitignored and local, so on a fresh clone every source here is absent.
D20 states the obligation directly: the pane *"must say so rather than render an empty roster as
'no loops running'"*. `armed_loops()` therefore returns a `state` of `no-harness` /
`none-armed` / `armed`, and the caller must render the first two differently from each other.

⚠️ **D20'S FILENAME TABLE IS WRONG FOR THREE OF ITS FIVE ROWS, MEASURED 2026-08-12.** It says
snapshots, stall history and coaching are keyed `<goal_id>`. They are keyed by **UTC timestamp**
(`snapshot_20260730T032457.json`, `stall_history/20260617T231250.json`). Worse for the design:
**a snapshot's CONTENT carries no goal id either** — its keys are `head_sha`, `last_message`,
`transcript_hwm`, `ts`. So a snapshot cannot be attributed to a specific goal by any available
means, and this module does not pretend otherwise: heartbeat and stall data are reported as
**harness-wide**, not per-loop. The marker's own fields are the only genuinely per-loop data.

The one row D20 gets exactly right is the marker: `role · goal · goal_id · roadmap_path ·
notebook_path · jsonl_path · repo · question_guard`, all eight present. `roadmap_path` and
`notebook_path` are the load-bearing ones — a live edge from a *running loop* to the *planning
artifact that authorized it*, the one direction the system otherwise cannot traverse.
"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
HARNESS = PROJECT_ROOT / ".claude" / "dev-harness"

#: The eight keys a marker carries. Frozen so a schema change is a visible test failure
#: rather than a pane that silently renders blanks.
MARKER_KEYS = ("goal", "goal_id", "jsonl_path", "notebook_path",
               "question_guard", "repo", "roadmap_path", "role")


def _read_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def armed_loops() -> dict:
    """`{'state': ..., 'loops': [...], 'note': ...}`.

    `state` is three-valued and the distinction is the whole point:

    * `no-harness`  — `.claude/dev-harness/` is absent. Nothing is known. This is the fresh-clone
      case, and it must NOT render as a calm empty list.
    * `none-armed`  — the harness exists and no goal is currently armed. A real, measured zero.
    * `armed`       — one or more markers.

    ⚠️ `managed/*.json.cleared-YYYYMMDD` files are DISARMED markers and are excluded. Counting
    them would report loops that ended weeks ago as running.
    """
    if not HARNESS.is_dir():
        return {"state": "no-harness", "loops": [], "note":
                "`.claude/dev-harness/` is absent — it is gitignored and local, so this pane "
                "knows NOTHING here. That is not the same as no loops running."}

    managed = HARNESS / "managed"
    live = sorted(managed.glob("*.json")) if managed.is_dir() else []
    loops = []
    for p in live:
        m = _read_json(p)
        if not isinstance(m, dict):
            loops.append({"session": p.stem, "unreadable": True})
            continue
        missing = [k for k in MARKER_KEYS if k not in m]
        loops.append({
            "session": p.stem,
            "goal_id": m.get("goal_id"),
            "goal": m.get("goal"),
            "role": m.get("role"),
            "repo": m.get("repo"),
            # The load-bearing edge: a running loop -> the artifact that authorized it.
            "roadmap_path": m.get("roadmap_path"),
            "notebook_path": m.get("notebook_path"),
            "question_guard": m.get("question_guard"),
            # A marker missing keys is REPORTED, never quietly rendered with blanks.
            "missing_keys": missing,
        })
    if not loops:
        return {"state": "none-armed", "loops": [], "note":
                "the harness is present and no goal is armed — a measured zero, not an "
                "absence of information."}
    return {"state": "armed", "loops": loops, "note": None}


def harness_activity() -> dict:
    """Heartbeat, stall signal and harvest cadence — **harness-wide, not per-loop**.

    ⚠️ THE ATTRIBUTION GAP IS REPORTED, NOT PAPERED OVER. D20 assumed these artifacts are keyed
    by `goal_id`; they are keyed by timestamp and carry no goal id in their contents. Presenting
    a harness-wide heartbeat as one loop's heartbeat would be a fabricated join — and with more
    than one loop ever armed, silently wrong.
    """
    snaps = sorted(HARNESS.glob("snapshot_*.json")) if HARNESS.is_dir() else []
    stalls = sorted((HARNESS / "stall_history").glob("*.json")) \
        if (HARNESS / "stall_history").is_dir() else []
    latest_snap = _read_json(snaps[-1]) if snaps else None

    # A residual repeating across compactions is the non-convergence signal. It is the one
    # genuine bottleneck detector already computed and never surfaced (D20).
    repeats: dict[str, int] = {}
    if stalls:
        recs = _read_json(stalls[-1])
        for r in (recs if isinstance(recs, list) else []):
            rid = (r or {}).get("residual_id") if isinstance(r, dict) else None
            if rid:
                repeats[rid] = repeats.get(rid, 0) + 1

    harvest = _read_json(HARNESS / "harvest_state.json") or {}
    return {
        "attribution": "harness-wide",
        "attribution_note":
            "snapshots and stall history are keyed by TIMESTAMP and carry no goal id, so these "
            "cannot be attributed to a specific loop. Reported harness-wide rather than joined "
            "on a guess.",
        "snapshot_count": len(snaps),
        "last_heartbeat": (latest_snap or {}).get("ts"),
        "last_head_sha": (latest_snap or {}).get("head_sha"),
        "stall_files": len(stalls),
        "repeating_residuals": sorted(
            ((k, v) for k, v in repeats.items() if v > 1),
            key=lambda kv: (-kv[1], kv[0])),
        "harvest_last_run": harvest.get("last_run_ts"),
        "harvest_cadence_hours": harvest.get("cadence_hours"),
    }


def blocked_question_count() -> dict:
    """How many operator questions are waiting, and how stale the newest is.

    ⚠️ D12 CORRECTED an earlier claim that this log is "read by nothing" — it has two live
    consumers (the `coach` agent in-time, `harvest-extractor` asynchronously). What is missing
    is an operator-facing surface and a latency floor, which is what this count is for.
    """
    p = HARNESS / "blocked_questions.jsonl"
    if not p.is_file():
        return {"available": False, "count": None,
                "note": "no blocked-questions log on this machine — unknown, not zero."}
    try:
        lines = [ln for ln in p.read_text(encoding="utf-8").splitlines() if ln.strip()]
    except OSError as exc:
        return {"available": False, "count": None, "note": f"unreadable ({exc})"}
    return {"available": True, "count": len(lines),
            "harvest_note": "reaches a human only via harvest; see harvest_cadence_hours"}


def loops_panel() -> dict:
    """Everything the pane renders, in one call."""
    return {
        "armed": armed_loops(),
        "activity": harness_activity(),
        "blocked_questions": blocked_question_count(),
        "generated": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


if __name__ == "__main__":  # pragma: no cover — operator convenience
    print(json.dumps(loops_panel(), indent=2))
