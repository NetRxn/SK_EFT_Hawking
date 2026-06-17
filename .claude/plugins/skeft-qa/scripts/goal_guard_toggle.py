#!/usr/bin/env python3
"""Toggle the marker's question_guard for the current managed session.
Usage: goal_guard_toggle.py <on|off> [session_id]
  <on|off>      the new guard state.
  [session_id]  optional; defaults to $CLAUDE_SESSION_ID, then $CLAUDE_CODE_SESSION_ID.
                (The /goal-guard skill passes the substituted ${CLAUDE_SESSION_ID} as the
                arg, so the toggle never depends on an env var being exported to the shell.)
Runs under the repo's uv Python >=3.14; stdlib only; fail-open (returns False, never raises)."""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import repo_root, marker_path


def set_question_guard(root, sid, value):
    """Set question_guard=<value:bool> in the marker for `sid` under `root`.
    Returns True on success, False if the marker is absent/unreadable (fail-open)."""
    try:
        p = marker_path(root, sid)
        m = json.loads(p.read_text())
        m["question_guard"] = bool(value)
        tmp = p.parent / (p.name + ".tmp")
        tmp.write_text(json.dumps(m))
        os.replace(str(tmp), str(p))   # atomic
        return True
    except Exception:
        return False


def main():
    arg = (sys.argv[1] if len(sys.argv) > 1 else "").strip().lower()
    if arg not in ("on", "off"):
        print("usage: goal_guard_toggle.py <on|off> [session_id]")
        return 0
    sid = (sys.argv[2] if len(sys.argv) > 2 else
           os.environ.get("CLAUDE_SESSION_ID") or os.environ.get("CLAUDE_CODE_SESSION_ID", ""))
    sid = (sid or "").strip()
    root = repo_root(os.getcwd())
    if not sid or root is None:
        print("goal-guard: no managed session resolved (inert)")
        return 0
    ok = set_question_guard(root, sid, arg == "on")
    print("goal-guard: question_guard=" + arg if ok else "goal-guard: no marker for this session")
    return 0


if __name__ == "__main__":
    sys.exit(main())
