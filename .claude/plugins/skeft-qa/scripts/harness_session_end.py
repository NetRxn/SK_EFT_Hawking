"""SessionEnd cleanup hook (v4.1, RC5).

Removes THIS session's managed-loop marker when the session ends with the goal definitively gone.
**Only acts on `reason == "clear"`** — the `/clear`-new-conversation case, which also removes any
active goal (goal.md). It does NOT act on `logout` / `prompt_input_exit` / `resume` / `other`,
because a goal still active when a session ends is **restored on `--resume`/`--continue`** (goal.md)
and must keep its marker, or the resumed loop would be unmanaged.

(The mid-session `/goal clear` case fires no event at all — there is no `Goal*` hook and Stop input
carries no goal state — so that case is handled by the explicit `/goal-end` command, not here.)

Marker-gated, fail-open, inert for subagents.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_common import read_event, repo_root, remove_marker  # noqa: E402


def main():
    ev = read_event()
    if not isinstance(ev, dict) or ev.get("agent_id"):
        return
    # Conservative: only tear down when the goal is definitively gone (a /clear). Never strand a
    # goal that an --resume would restore.
    if ev.get("reason") != "clear":
        return
    remove_marker(repo_root(ev.get("cwd")), ev.get("session_id"))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass  # fail-open: a teardown hook must never block session exit
