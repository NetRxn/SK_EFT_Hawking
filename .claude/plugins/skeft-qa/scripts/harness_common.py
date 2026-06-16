"""Shared helpers for the skeft-qa dev-harness hooks/commands. Stdlib only; fail-open.

Every harness hook is DEFAULT-INERT: it acts only for a *managed* `/goal` dev
loop — one for which `/dev-goal` wrote a marker — and NEVER for a subagent
(`agent_id` present). A non-managed interactive session, an Explore/Plan/review
subagent, or any error all resolve to "do nothing, exit 0".

State lives under a fixed, load-mechanism-independent dir
(`~/.claude/skeft-harness/`) rather than `$CLAUDE_PLUGIN_DATA`. Reason
(build-time): `$CLAUDE_PLUGIN_DATA` is injected for hooks but NOT for slash
commands (`/dev-goal`, `/debrief`), and its `{plugin}-{marketplace}` id varies
with how the plugin was loaded (e.g. `skeft-qa-skeft-local` vs `skeft-qa-inline`).
The fixed dir is computable identically by both hooks and commands; markers are
keyed by the globally-unique `session_id`, so one shared dir is collision-free
across projects and concurrent loops.
"""
import json
import os
import sys


def harness_dir() -> str:
    return os.path.join(os.path.expanduser("~"), ".claude", "skeft-harness")


def marker_path(session_id: str) -> str:
    return os.path.join(harness_dir(), "managed", f"{session_id}.json")


def qi_intake_dir() -> str:
    return os.path.join(harness_dir(), "qi_intake")


def read_event() -> dict:
    """Parse the hook event JSON from stdin; {} on any error."""
    try:
        return json.load(sys.stdin)
    except Exception:
        return {}


def read_marker(ev: dict):
    """Return this session's managed-loop marker dict, or None.

    None ⟺ inert: not a dict event, a subagent (`agent_id`), no session_id, or
    no marker file for this session.
    """
    if not isinstance(ev, dict) or ev.get("agent_id"):
        return None
    sid = ev.get("session_id")
    if not sid:
        return None
    try:
        with open(marker_path(sid)) as f:
            return json.load(f)
    except Exception:
        return None


def emit_context(event_name: str, text: str) -> None:
    """Inject `text` as additionalContext for the given hook event."""
    try:
        print(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": event_name,
                "additionalContext": text,
            }
        }))
    except Exception:
        pass
