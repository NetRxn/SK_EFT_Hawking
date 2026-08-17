"""PreToolUse(Bash) — deny build / cache / integration commands to SUBAGENT workers.

ADR-008 parity with `.codex/hooks/pre_tool_use_policy.py`: workers prove and commit; the
orchestrator builds, publishes caches, and integrates.

SCOPE: subagents only, keyed on `agent_id` (present for a subagent, absent for the lead —
the same discriminator `harness_common.read_marker` uses). The lead is never affected.

FAIL DIRECTION, asymmetric on purpose: inside a subagent, any error denies. An event that
cannot be parsed at all is indistinguishable from the lead and ALLOWS — bricking the lead's
Bash is the worse failure. Residual window: malformed event + subagent + build command.

`lake build <OneModule>` is denied too: Lake has no job cap, so a single-module build is
still unbounded. Granting it is a lead decision, one slot at a time.
"""
from __future__ import annotations

import json
import re
import sys

#: (pattern, why). Matched anywhere in the command, so a `cd x && …` prefix or a `;` chain
#: cannot smuggle one past. Mirrors the Codex-side denied set.
DENIED: tuple[tuple[str, str], ...] = (
    (r"\blake\s+build\b", "builds are the orchestrator's; Lake has no job cap, so a slot "
                          "build takes the whole machine"),
    (r"\blake\s+clean\b", "destroys build state the orchestrator owns"),
    (r"\blake\s+update\b", "moves dependency pins, which are a coupled set (Mathlib / "
                            "PhysLib / REPL / toolchain) the orchestrator owns"),
    (r"\blake\s+exe\s+cache\s+get\b", "cache publication is the orchestrator's"),
    (r"\brm\s+-rf?\b[^\n]*\.lake\b", "workers do not repair shared build state"),
    # ⚠️ ASSERT THE DECIDER (does this touch `.lake`?), NOT A FLAG SPELLING. Matching a
    # recursion flag cannot work: `-r`, `-R`, `-a`, `--recursive`, `--archive`, coalesced
    # into one token or split across several, in any order. So deny ANY `cp` naming `.lake`
    # in either operand — a worker has no legitimate reason to copy a build cache in or out,
    # and the flags were never what made it unsafe.
    (r"\bcp\b[^\n|;&]*\.lake\b", "cache seeding is the orchestrator's"),
    # Same shape for the other bulk copiers a worker might reach for instead.
    (r"\b(rsync|ditto|install)\b[^\n|;&]*\.lake\b", "cache seeding is the orchestrator's"),
    # Broad process killing: a worker stopping "its own" contending processes by pattern has
    # no way to tell its runs from a sibling agent's in a shared repo, so a name pattern
    # reaches another agent's suite. Workers stop their own work by returning, not by
    # signalling.
    (r"\b(pkill|killall)\b", "workers do not signal processes; a name pattern cannot "
                             "distinguish your run from a concurrent agent's"),
    (r"\bkill\s+(-\w+\s+)?\$?\(", "workers do not signal process groups discovered by "
                                  "substitution; that reaches other agents' runs"),
    (r"\bgit\s+merge\b", "integration is the orchestrator's"),
    (r"\bgit\s+rebase\b", "integration is the orchestrator's"),
    (r"\bgit\s+cherry-pick\b", "breaks ancestry; the reset guard then reads absorbed work "
                               "as unmerged (62e8da08)"),
    (r"\bslotctl(\.py)?\b[^\n]*\b(build|absorb|supervisor)\b",
     "slot lifecycle is the orchestrator's"),
)

_ALLOW = json.dumps({})


def _deny(reason: str) -> str:
    return json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        },
        "systemMessage": reason,
    })


def decide(ev: object) -> str:
    """`allow` json for the lead and benign worker commands; `deny` json otherwise."""
    if not isinstance(ev, dict):
        return _ALLOW
    if not ev.get("agent_id"):
        return _ALLOW
    try:
        cmd = (ev.get("tool_input") or {}).get("command") or ""
    except Exception:
        return _deny("worker shell guard could not read the command")
    if not isinstance(cmd, str):
        return _deny("worker shell guard got a non-string command")
    for pattern, why in DENIED:
        if re.search(pattern, cmd):
            return _deny(
                f"DENIED for a slot worker: {why}. Your gate is the MCP loop "
                f"(`lean_diagnostic_messages` / `lean_goal` / `lean_verify`). Report what you "
                f"need built; the lead runs it on main after the merge. ADR-008.")
    return _ALLOW


def main() -> int:
    try:
        ev = json.load(sys.stdin)
    except Exception:
        print(_ALLOW)
        return 0
    print(decide(ev))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
