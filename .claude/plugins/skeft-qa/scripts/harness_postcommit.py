#!/usr/bin/env python3
"""PostToolUse(Bash) — after a `git commit`, keep deterministic indices fresh.

Runs the project's existing regenerators, then flags any regenerated *tracked*
artifact so the agent re-commits it (stale autogen artifacts are a known
failure mode). Managed-only + fail-open; degrades gracefully where a script is
absent (e.g. the private repo has no validate.py). The full validate.py suite
runs at the wave/task gate, not on every commit (cost-scoping).
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import read_event, read_marker, emit_context

GIT_COMMIT = re.compile(r"\bgit\b[^&|;]*\bcommit\b")


def _repo_root(ev: dict) -> str:
    d = ev.get("cwd") or os.getcwd()
    for _ in range(10):
        if os.path.isfile(os.path.join(d, "lean", "lakefile.toml")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return ev.get("cwd") or os.getcwd()


def _run(root: str, script: str, timeout: int) -> None:
    path = os.path.join(root, "scripts", script)
    if not os.path.isfile(path):
        return  # degrade gracefully (script not present in this repo)
    try:
        subprocess.run(["uv", "run", "python", path], cwd=root,
                       capture_output=True, text=True, timeout=timeout)
    except Exception:
        pass


def main() -> int:
    ev = read_event()
    m = read_marker(ev)
    if not m:
        return 0
    cmd = (ev.get("tool_input") or {}).get("command") or ""
    if not GIT_COMMIT.search(cmd):
        return 0
    root = _repo_root(ev)
    for script in ("update_counts.py", "update_inventory_index.py", "qi_register.py"):
        _run(root, script, 90)
    try:
        st = subprocess.run(["git", "status", "--porcelain"], cwd=root,
                            capture_output=True, text=True, timeout=15)
        dirty = [ln for ln in (st.stdout or "").splitlines() if ln.strip()]
    except Exception:
        dirty = []
    if dirty:
        emit_context(
            "PostToolUse",
            "[dev-harness] Post-commit index refresh changed tracked artifacts "
            "(counts / inventory / QI register). Commit them so the tree stays in sync — "
            "do not leave them stale:\n" + "\n".join(dirty[:20]),
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
