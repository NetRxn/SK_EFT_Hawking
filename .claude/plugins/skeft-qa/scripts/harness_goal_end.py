"""`/goal-end` teardown CLI (v4.1, RC5) — the explicit disarm that matches goal-prompt's arm.

Removes THIS session's managed-loop marker. For the mid-session `/goal clear` case the platform
emits NO event (there is no `Goal*` hook; Stop input carries no goal state — verified at source), so
the marker would otherwise persist and keep the SessionStart re-injection + the AskUserQuestion guard
firing on a dead loop. Run `/goal-end` when you clear/finish a goal mid-session. cwd-safe; fail-open.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_common import repo_root, remove_marker  # noqa: E402


def main():
    sid = sys.argv[1].strip() if len(sys.argv) > 1 else ""
    if not sid:
        print("⚠ no session id supplied — nothing to do.")
        return
    root = repo_root()
    if root is None:
        print("⚠ repo root unresolved (launch from the workspace root or inside the repo) — no action.")
        return
    if remove_marker(root, sid):
        print(f"✓ managed-loop marker removed for {sid}. The harness re-injection and the "
              f"AskUserQuestion guard are now inert for this session.")
    else:
        print(f"(no managed marker for {sid} — this session is already unmanaged; nothing to do.)")


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"(goal-end: {e})")
