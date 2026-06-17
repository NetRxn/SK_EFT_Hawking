---
name: goal-guard
description: Toggle the AskUserQuestion guard for the current managed /goal loop. Turn it off when you want the loop to be able to ask you a question; turn it back on to resume autonomous protection. Use when you want to enable or disable being asked questions during an autonomous dev loop.
argument-hint: <on|off>
disable-model-invocation: true
allowed-tools: Bash(uv run *)
---
<!-- disable-model-invocation: true is USER-ONLY by deliberate policy (spec 11 refined): an
     agent must NOT be able to toggle OFF its own AskUserQuestion guard — that would defeat
     the safeguard entirely. The `!`cmd`` injection below runs BEFORE the skill is sent and
     is gated by `disableSkillShellExecution`, NOT allowed-tools. -->

Toggle the `PreToolUse(AskUserQuestion)` guard by flipping `question_guard` in this
session's marker. **Default is `on`** in goal mode (questions are intercepted + redirected).
Turn it **off** when you genuinely want to be asked; **on** to resume autonomous protection.

The session id is passed as an argument (the substituted `${CLAUDE_SESSION_ID}`), so the
toggle does not depend on an env var being exported to the shell:

Run: `` !`uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/goal_guard_toggle.py" $ARGUMENTS ${CLAUDE_SESSION_ID} 2>/dev/null` ``

Then confirm the new state to the user (`question_guard=on|off`). If the line above is empty
or reads `[shell command execution disabled by policy]`, tell the user shell execution is
disabled (the toggle could not run). If it reports no marker for this session, the session is
not a managed loop — there is nothing to toggle.
