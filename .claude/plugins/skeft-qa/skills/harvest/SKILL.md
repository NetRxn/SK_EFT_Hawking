---
name: harvest
description: Off-hot-loop System-2 harvest. Reads each managed /goal session's transcript from a byte-offset watermark, extracts process/harness signal (Haiku) — crossing the compact boundary for the pre-vs-post-compact delta and ingesting the guard's blocked-question log — and a register-AWARE Opus consolidator files/combines it into the four-section register (Open / Process Wins / Closed / Misfiled) — re-opening a recurring closed finding, grouping semi-related ones, filing real wins to Process Wins (capped at agent-reviewed, never injected), and dropping noise (never writing Misfiled — that is /debrief's human sweep) — then refreshes the open-only active-issues view. Invoked by a Desktop scheduled task or a second-session /loop — never inside a /goal session.
disallowed-tools: AskUserQuestion
allowed-tools: Bash(jq *), Bash(uv run python *), Bash(python3 *), Read, Agent
---

You are the System-2 harvest. Run ONLY off the hot loop. Native CC throughout — no headless.
Let `CLI = ${CLAUDE_SKILL_DIR}/../../scripts/harness_common_cli.py` and `REPO = $(uv run --no-sync python "$CLI" repo-root)`.

-1. **Disabled-shell fail-loud [BLOCKER/MAJOR A2 — spec 2 "Arm-time guarantees", A.6 step 8(i)].** The
   `!cmd` / Bash substitutions above (resolving `CLI`, `REPO`, the `jsonl_path` glob) run **before** the
   skill is sent and are gated by `disableSkillShellExecution`, **not** `allowed-tools`. If that managed-settings
   kill-switch is set, each injection is replaced by the sentinel `[shell command execution disabled by policy]`.
   **Detect that sentinel in `CLI`/`REPO`/any resolved path and STOP immediately with a clear message** — never
   proceed to read transcripts or write findings with `UNRESOLVED` paths (a degrade-loudly, not run-silently-wrong
   posture; same guarantee `goal-prompt` enforces at arm-time).

0. **Self-abort guard (FAIL-CLOSED).** `uv run --no-sync python "$CLI" is-managed ${CLAUDE_SESSION_ID}`. If it prints
   `MANAGED` (this is a `/goal` session) — or errors / can't resolve the workspace — **STOP immediately**
   (running inside `/goal` would burn its context + confuse the evaluator; an unresolved workspace fails closed).

1. **GC + enumerate.** `uv run --no-sync python "$CLI" gc`; then read every marker in `$REPO/.claude/dev-harness/managed/`
   (this plugin's repo only — leak-safe). For each, take its `jsonl_path` + `session_id` **+ its `goal_id` and the
   `goal_prompt_<goal_id>.md` path** (the marker carries `goal_id`, spec A.5) — these are the **goal pointer**
   (spec A.4) stamped onto every occurrence the consolidator writes for this session. If a marker predates
   `goal_id` (older arm), carry it through as absent rather than failing.
2. **Per session — incremental BYTE-RANGE read (NOT the Read tool — the file is ~110 MB).**
   `off=$(uv run --no-sync python "$CLI" read-watermark <sid>)`; if `os.path.getsize(jsonl) <= off`, skip. Read the span
   `[off, last-complete-newline]` with a byte reader, e.g.
   `uv run --no-sync python -c "import sys;f=open(sys.argv[1],'rb');f.seek(int(sys.argv[2]));d=f.read();e=d.rfind(b'\n')+1;sys.stdout.buffer.write(d[:e])" <jsonl> <off>`
   → split into ~N-MB chunk files at newline boundaries. Build the canonical compact-event map ONCE per file by
   scanning `compact_boundary` lines for `{uuid: first_byte_offset}` (**first occurrence wins** — uuids repeat,
   26→16 in `917c9cbd`, spec A.1) → `compact_event_id = "<sid>:<first_offset>"`.
   - **Chunk ACROSS the compact boundary (v4.0 — spec 6.3), do NOT wall segments off.** Slice chunks so each
     compact boundary lands *inside* a chunk along with the **tail of its pre-boundary segment AND the
     `isCompactSummary` entry + early post-boundary turns** — i.e. arrange chunk windows so the Haiku extractor
     can compute the pre-vs-post-compact delta for every boundary (overlap adjacent chunks at boundaries if a
     boundary would otherwise fall on a chunk edge). The per-segment siloing of the v3.0 draft is dropped.
   - **Locate the blocked-question log span (v4.0 — spec 6.3/10).** `BQLOG=$REPO/.claude/dev-harness/blocked_questions.jsonl`
     (Plan 1's `PreToolUse(AskUserQuestion)` guard APPENDS to it). If it exists, byte-range-read its new span the
     same way (a small per-session/per-log watermark, or just read the whole file — it is tiny) → a
     `blocked_questions` span file to hand the extractor. If absent, skip gracefully.
3. **Step 1 — extract (Haiku).** For each chunk, dispatch the **`harvest-extractor`** subagent (Agent tool,
   agentType `harvest-extractor`) with the chunk path + session_id **+ (when present) the blocked-question-log
   span path**. Collect its candidate findings (including the `compact-delta` and `blocked-question` classes).
4. **Step 2 — consolidate (Opus).** Dispatch the **`harvest-consolidator`** subagent (Agent tool, agentType
   `harvest-consolidator`) with all candidates + the `{boundary_uuid: compact_event_id}` map + **the per-session
   `{session_id: {goal_id, goal_prompt}}` goal-pointer map (from step 1's markers, spec A.4/A.5)** + `$REPO`. It
   writes each via `system2_register.py --upsert` — stamping each occurrence with its `compact_event_id` **and its
   `goal_id` + `goal_prompt` path** — whose **deterministic public leak-scrub** drops any private-token finding
   (the agent's own drop is belt-and-suspenders), then **refreshes `active_issues.json` (register-wide) via
   `system2_register.py --write-active-issues`** (the view Plan 1's re-injection / AskUserQuestion redirect read).
5. **Commit the watermark LAST:** only after the consolidator's writes succeed,
   `uv run --no-sync python "$CLI" advance-watermark <sid> <new_offset>` (atomic, boundary-aligned). Then
   `uv run --no-sync python "$CLI" harvest-state-set <now> <cadence_hours>` for the drift warning.
   Pass `<cadence_hours>` = **the scheduled task's actual cron interval (default 4 — adjustable: this just
   feeds the "harvest overdue" nudge, which warns past 2× this value, so keep it equal to whatever the cron is set to).**
5b. **GC the blocked-question log [MINOR D2].** ALSO only after the consolidator's writes succeed: advance the
    blocked-question log past the span just ingested so it does NOT grow unbounded and is NOT re-ingested as
    duplicate findings on the next run. Either **truncate** `$BQLOG` (`: > "$BQLOG"` when the whole file was the
    ingested span) or **watermark** it (`uv run --no-sync python "$CLI" advance-watermark bqlog <new_bqlog_offset>`, the same
    byte-offset machinery, when only a span was read). Skip gracefully if `$BQLOG` is absent. **Note:**
    `gc_dead_markers` does NOT cover `blocked_questions.jsonl` — it prunes only dead markers + watermarks under
    this repo, so this GC step is its own thing and must run here, not be assumed handled by `gc`.
6. Print a one-line summary (sessions, chunks, findings upserted, compact-delta findings, blocked-questions
   folded, blocked-question log GC'd, leak-drops, active-issues refreshed). Do NOT touch CLAUDE.md / hooks / roadmaps.
