---
description: End/disarm the current managed /goal loop — removes this session's harness marker so the SessionStart re-injection and the AskUserQuestion guard stop firing. Run after you /goal clear (or finish a goal) mid-session.
disable-model-invocation: true
allowed-tools: Bash(uv run *)
---
<!-- A COMMAND (v4.1), user-only: the explicit disarm matching goal-prompt's arm. Native /goal clear
     mid-session fires NO hook (there is no Goal* event; Stop input carries no goal state), so the marker
     would otherwise persist and keep the re-inject + guard firing on a dead loop. The SessionEnd hook only
     auto-cleans on a /clear-new-conversation; this command covers the mid-session case. -->

Remove this session's managed-loop marker (the explicit teardown for a mid-session `/goal clear`):

Run: `` !`uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_goal_end.py" ${CLAUDE_SESSION_ID} 2>/dev/null` ``

Report the result to the user verbatim. If the line is empty or reads `[shell command execution disabled by
policy]`, tell the user shell execution is disabled (the marker could not be removed). If it says the session
is already unmanaged, there was nothing to do.
