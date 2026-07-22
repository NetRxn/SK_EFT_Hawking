#!/usr/bin/env python3
"""Defense-in-depth Codex guard for ADR-008 build/integration authority.

The MCP proxy removes ``lean_build`` server-side. This hook additionally blocks
raw shell spellings so the only supported build/integration path is ``slotctl``.
Hooks are not the lease authority and are intentionally not treated as a
complete security boundary.
"""
from __future__ import annotations

import json
import re
import sys


_FORBIDDEN = re.compile(
    r"(?:^|[;&|()\n]\s*|\s+)"
    r"(?:"
    r"lake\s+(?:build|clean|update)\b|"
    r"lake\s+exe\s+cache\s+get\b|"
    r"git\s+(?:merge|rebase|cherry-pick|reset|pull|push|fetch|switch|checkout|"
    r"clean|restore|worktree|update-ref|symbolic-ref|branch)\b|"
    r"(?:\S*/)?slotctl\.py\s+(?:acquire|prepare|ready|heartbeat|absorb|release|reclaim|build|"
    r"config|session|supervisor)\b|"
    r"(?:rm|cp|mv)\b[^\n;&|]*\.lake(?:/|\b)"
    r")",
    re.IGNORECASE,
)


def decision(payload: dict) -> dict | None:
    tool_name = str(payload.get("tool_name", ""))
    if tool_name.endswith("__lean_build"):
        reason = "ADR-008: Lean workers cannot call lean_build; use orchestrator slotctl build/absorb."
    elif tool_name in {"Bash", "exec_command"}:
        tool_input = payload.get("tool_input") or {}
        command = str(tool_input.get("command") or tool_input.get("cmd") or "")
        if not _FORBIDDEN.search(command):
            return None
        reason = (
            "ADR-008: raw build/cache/integration commands are disabled for Codex. "
            "Use the primary orchestrator's scripts/slotctl.py command."
        )
    else:
        return None
    return {
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }
    }


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    result = decision(payload)
    if result is not None:
        print(json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
