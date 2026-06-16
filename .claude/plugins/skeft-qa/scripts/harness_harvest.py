#!/usr/bin/env python3
"""PreCompact learning-harvest.

Before compaction squashes a managed loop's recorded learnings, append the
lab-notebook tail to the QI intake so a later `/debrief` can synthesize
agent-reviewed findings. For a 24/7 loop this is the only recurring harvest
point (it never fires Stop and the user won't invoke `/debrief`). Managed-only
+ fail-open.
"""
import json
import os
import sys
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import read_event, read_marker, qi_intake_dir


def main() -> int:
    ev = read_event()
    m = read_marker(ev)
    if not m:
        return 0
    notebook = m.get("notebook_path") or ""
    if not notebook or not os.path.isfile(notebook):
        return 0
    try:
        text = open(notebook, encoding="utf-8").read()
    except Exception:
        return 0
    intake_dir = qi_intake_dir()
    try:
        os.makedirs(intake_dir, exist_ok=True)
    except Exception:
        return 0
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    record = {
        "captured_at": stamp,
        "session_id": ev.get("session_id"),
        "trigger": ev.get("trigger"),
        "goal": m.get("goal", ""),
        "roadmap_path": m.get("roadmap_path", ""),
        "notebook_path": notebook,
        "notebook_tail": text[-4000:],
    }
    try:
        out = os.path.join(intake_dir, f"{ev.get('session_id', 'session')}-{stamp}.json")
        with open(out, "w", encoding="utf-8") as f:
            json.dump(record, f, indent=2)
    except Exception:
        return 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
