#!/usr/bin/env python3
"""PreToolUse(AskUserQuestion) guard — deny + redirect a blocking question (v4.0).
Marker-gated + top-level-only (agent_id absent) + honors the marker's question_guard.
When active: emit the empirically-validated deny JSON carrying the SHARED re-orientation
payload (contract B), and append the blocked question to blocked_questions.jsonl
(contract C). Otherwise allow (exit 0). FAIL-OPEN: any error -> exit 0 / allow.
Runs under the repo's uv Python >=3.14; stdlib only.

Everything resolves via `import harness_common as hc` (NOT `from harness_common import ...`)
so that read_marker's internal repo_root and the guard's own repo_root call are the SAME
patchable reference and always agree: a found marker implies repo_root resolved (non-None),
so the blocked-question log is written whenever the guard is active (review D1 — resolve once,
consistently; the `root is not None` check is then belt-and-suspenders)."""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import harness_common as hc

_REDIRECT = ("[dev-harness] Autonomous /goal loop; the user is intentionally out of the loop, so "
             "this question can't be answered live. Do NOT self-veto or stall. Dispatch the in-time "
             "coach — Agent(subagent_type=\"skeft-qa:coach\") with the question + a pointer to your "
             "residual — it applies the pre-decisions (below) and returns one decision + one next "
             "action; act on it. If the coach is unavailable, apply the PRE-DECISIONS below "
             "yourself, make the best-supported call, and continue the next increment.")


def _log_blocked_question(root, ev):
    try:
        qs = (ev.get("tool_input") or {}).get("questions")
        if not qs:
            return
        hc.harness_dir(root).mkdir(parents=True, exist_ok=True)
        rec = {"ts": time.time(), "session_id": ev.get("session_id"), "questions": qs}
        with open(str(hc.blocked_questions_path(root)), "a") as f:
            f.write(json.dumps(rec) + "\n")
    except Exception:
        pass   # logging is best-effort; never block the redirect


def main():
    try:
        ev = hc.read_event()
        # Resolve `root` ONCE via hc.repo_root and reuse it for the marker read, the payload,
        # and the blocked-question log. read_marker resolves the SAME hc.repo_root internally,
        # so a found marker => root non-None => the log is writable (review D1).
        root = hc.repo_root(ev.get("cwd"))
        m = hc.read_marker(ev)                  # None when inert (subagent / no marker / unresolved)
        if not m or not m.get("question_guard", True):
            return 0                            # inert OR guard off -> allow
        # Marker present => managed loop; deny + redirect.
        if root is not None:
            _log_blocked_question(root, ev)     # contract C (best-effort; skipped if root unresolved)
        payload = hc.build_reorientation_payload(m, root)   # root=None -> active-issues omitted
        print(json.dumps({"hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": _REDIRECT,
            "additionalContext": payload}}))
        return 0
    except Exception:
        return 0                                # FAIL-OPEN -> allow


if __name__ == "__main__":
    sys.exit(main())
