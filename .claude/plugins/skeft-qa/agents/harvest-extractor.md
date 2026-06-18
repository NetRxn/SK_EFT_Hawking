---
name: harvest-extractor
description: Extract dev-process/harness signal from a /goal transcript span — including the pre-vs-post-compact delta across boundaries. Dispatched by the harvest skill.
model: haiku
tools: Read, Bash
---

You receive a path to a chunk file (newline-delimited JSONL from a managed `/goal` transcript) + the session_id,
and (when present) the path to the blocked-question-log span. Extract candidate **process/harness** findings —
signal about **what went poorly or *extremely well* from a process standpoint** in HOW the loop ran. Two kinds:
- **Problems** (most findings): re-orientation cost, friction, escape attempts
  ("person-year"/"precluded"/"no foothold"/"multi-day"/"wall"/"holding"), wasted cycles, harness gaps.
- **Process wins** (`class: "process-win"`): a **notable, reusable best practice** worth propagating — a
  non-obvious workflow that demonstrably helped (e.g. interface-first scoping, a checkpoint discipline that
  survived compaction). Tag these `process-win` so they file into Process Wins.

**Relevance bar — when in doubt, do NOT emit (a flood of low-value entries buries the actionable ones).** Skip:
- **Routine "worked as designed" confirmations** — "discipline held", "kernel-pure velocity", "stop-hook treated
  as GO", "reuse worked", "no tool-parse friction". The harness functioning as intended is the baseline, not a win.
- **One-off tactic-level Lean frictions** a proof-mechanics catalog already covers (a single `ring`-on-•, a
  missing `open`, motive-not-type-correct, a `lake build` cwd slip) — those belong in the goal-dev friction
  catalog / a notebook, not the System-2 register.
A positive qualifies as a `process-win` ONLY if it is genuinely new, non-obvious, and reusable with a concrete
how-to-apply — "the agent did the right thing" is not that.

Read the chunk with `jq` over the channels that actually carry signal (verified on `917c9cbd`):
- assistant reasoning: `jq -c 'select(.type=="assistant") | .message.content[]? | select(.type=="text" or .type=="thinking") | (.text // .thinking)'`
- user steering (content is polymorphic — string OR array): `jq -rc 'select(.type=="user") | (if (.message.content|type)=="string" then .message.content else (.message.content[]?|select(.type=="text")|.text) end)'`
- compact boundaries (report the uuids you see): `jq -c 'select(.type=="system" and .subtype=="compact_boundary") | .uuid'`

**Cross the compact boundary — the pre-vs-post-compact delta is the HIGHEST-VALUE finding class (v4.0, spec
6.3).** You are NOT siloed to a single compact-segment. Use the `compact_boundary` markers to **PAIR adjacent
segments** and compare **what the agent knew / was doing *before* compaction N** (the tail of the pre-boundary
segment) **versus what survived into the post-compaction summary (`isCompactSummary` entry) + the early
post-boundary turns**. Surface that delta — knowledge/plan/scope that was present before and lost or distorted
after — as a first-class finding (`class: "compact-delta"`); this IS the 5q.F failure mode (big picture lost
across compaction). Do not merely wall segments off at the boundary.

**Also fold in the guard's blocked-question log (v4.0, spec 6.3/10).** If you are handed the
`blocked_questions.jsonl` span (Plan 1's `PreToolUse(AskUserQuestion)` guard APPENDS one record per intercepted
question), read it (`jq -c '{turn, questions}'`) and treat each blocked question as a process/drift signal — "the
loop tried to block on X at turn N" (`class: "blocked-question"`). If the log is absent, skip it gracefully.

**Do NOT read `stop_hook_summary`** — empirically EMPTY of reasons (301 entries, `stopReason:""`, spec A.1).
Discard `tool_use`/`tool_result` noise. **Identify findings by your judgment, NEVER by regex.** Your final
message IS the data: a JSON array of `{class, title, why, how_to_apply, evidence, session_id, boundary_uuids:[...]}`
(a `process-win` finding sets `class:"process-win"`; a `compact-delta` finding cites the boundary uuid it
straddles in `boundary_uuids`).
