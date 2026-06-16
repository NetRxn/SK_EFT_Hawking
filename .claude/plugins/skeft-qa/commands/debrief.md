---
description: Synthesize harvested dev-loop learnings into proposed QI findings (agent-reviewed tier) — never auto-edits CLAUDE.md.
argument-hint: [all|<session_id>]
---

Synthesize the dev-loop learnings the `PreCompact` harvest captured into
**proposed** quality-improvement findings. These are tagged `agent-reviewed`:
usable immediately by the next run, but the human promotes them to
`human-reviewed` via the QI consolidator. **Never edit CLAUDE.md, roadmaps, or
hooks here** — that is the on-the-fly-pollution failure mode this whole harness
exists to prevent.

To keep the main context clean, prefer to do the read+synthesis in a **subagent**
(Explore or general-purpose) and return only the digest.

1. **Collect intake.** Read `~/.claude/skeft-harness/qi_intake/*.json` (each is a
   harvested notebook tail with goal/roadmap/session). Scope to `$ARGUMENTS`
   (`all`, default, or a specific session_id).

2. **Synthesize** across the intake — dedup/cluster recurring items into:
   - **Went well** (patterns to keep), **Went poorly** (anti-patterns to avoid),
   - **Best practices** and **gotchas/corrections** (e.g. tactic that worked, a
     wrong assumption that cost time), each with a one-line "why" and "how to apply".
   - An **efficacy** note: did the loop ship real bricks, or churn?

3. **Write proposals** to `~/.claude/skeft-harness/proposals/debrief-<UTC-stamp>.md`
   as a list of candidate findings, each with: title, class
   (best-practice | anti-pattern | process-gap), `review_level: agent-reviewed`,
   evidence (which intake/session), and a proposed action. Use the
   `## QI Candidate` heading style so the QI consolidator can ingest them.

4. **Archive consumed intake** into `~/.claude/skeft-harness/qi_intake/archive/`
   so the next `/debrief` doesn't re-synthesize the same records.

5. **Surface a short digest** (≤ 10 bullets) and the proposals path. State plainly
   that these are `agent-reviewed` proposals awaiting human promotion — do not
   apply any of them to a hard rule (CLAUDE.md / hook / roadmap) without explicit
   user sign-off.
