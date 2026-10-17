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
import shlex
import sys


_FORBIDDEN = re.compile(
    r"(?:^|[;&|()\n]\s*|\s+)"
    r"(?:"
    r"lake\s+(?:build|clean|update)\b|"
    r"lake\s+exe\s+cache\s+get\b|"
    r"git\s+(?:merge|rebase|cherry-pick|reset|pull|push|fetch|switch|checkout|"
    r"clean|restore|worktree|update-ref|symbolic-ref|branch)\b|"
    r"(?:\S*/)?slotctl\.py\s+(?:acquire|prepare|ready|heartbeat|absorb|release|reclaim|build|"
    r"config|session|supervisor|checkpoint)\b|"
    r"(?:rm|cp|mv)\b[^\n;&|]*\.lake(?:/|\b)"
    r")",
    re.IGNORECASE,
)


def _shell_continuations(command: str) -> str:
    """Remove shell backslash-LF pairs while retaining single-quoted bytes.

    This is the continuation step needed by the bounded slotctl recognizer,
    not a general shell parser. Other escapes and unescaped newlines remain.
    """
    result = []
    quote = None
    cursor = 0
    while cursor < len(command):
        char = command[cursor]
        if quote == "'":
            result.append(char)
            if char == "'":
                quote = None
            cursor += 1
            continue
        if char == "\\" and cursor + 1 < len(command):
            following = command[cursor + 1]
            if following != "\n":
                result.extend((char, following))
            cursor += 2
            continue
        result.append(char)
        if char in {"'", '"'}:
            if quote is None:
                quote = char
            elif quote == char:
                quote = None
        cursor += 1
    return "".join(result)


def _slotctl_lifecycle(command: str) -> bool:
    """Recognize accepted global inventory arguments after shell quote removal."""
    try:
        lexer = shlex.shlex(_shell_continuations(command), posix=True,
                            punctuation_chars="();<>|&\n")
        # A remaining unquoted LF separates shell commands; quoted LF stays
        # inside its token. Do not join a later command to slotctl's arguments.
        lexer.whitespace = lexer.whitespace.replace("\n", "")
        lexer.whitespace_split = True
        lexer.commenters = ""
        tokens = list(lexer)
    except ValueError:
        return False
    owner_commands = {"acquire", "prepare", "ready", "heartbeat", "absorb", "release",
                      "reclaim", "build", "config", "session", "supervisor", "checkpoint"}
    for index, token in enumerate(tokens):
        if token.rsplit("/", 1)[-1].lower() != "slotctl.py":
            continue
        cursor = index + 1
        while cursor < len(tokens):
            option, equals, _ = tokens[cursor].partition("=")
            # argparse accepts unique long-option prefixes as well as the full
            # spelling, repeated options, separate values and --inventory=PATH.
            if len(option) <= 2 or not "--inventory".startswith(option):
                break
            cursor += 1 if equals else 2
        if cursor < len(tokens) and tokens[cursor].lower() in owner_commands:
            return True
    return False


def decision(payload: dict) -> dict | None:
    tool_name = str(payload.get("tool_name", ""))
    if tool_name.endswith("__lean_build"):
        reason = "ADR-008: Lean workers cannot call lean_build; use orchestrator slotctl build/absorb."
    elif tool_name in {"Bash", "exec_command"}:
        tool_input = payload.get("tool_input") or {}
        command = str(tool_input.get("command") or tool_input.get("cmd") or "")
        if not (_FORBIDDEN.search(command) or _slotctl_lifecycle(command)):
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
