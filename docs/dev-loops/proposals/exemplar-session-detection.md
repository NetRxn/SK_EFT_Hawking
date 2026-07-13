# GAP-A proposal: exemplar-session detection (the "gold-standard lens")

**Status:** DRAFT — pending `/skeft-qa:debrief` sign-off. Informational only (a harvest-emitted
per-session rollup + a flag); **no hook, no gate, no auto-action.** Hand-authored 2026-07-12 from
the harvest of session `6b847cb9` (goal `20260712T150610`), not by `--propose-gate` — see "Why
this isn't a normal recurrence proposal" below.

**Mechanizes** a harvest blind spot the 2026-07-12 harvest exposed in itself: the register-aware
consolidator is **dedup-first**, so when an exceptional session fires *all* the high-tally known-good
practices at once and *avoids* the register's most common frictions, it flattens to "0 new wins, N
recurrences" — the exact opposite of raising a flag. Magnitude and friction-*absence* are session-level
emergent properties that no current stage measures. The 2026-07-12 loop (~28 kernel-pure commits, 15
worker branches, a clean compaction, near-zero re-orientation cost) was ~10× a normal session and the
harvest recorded it as unremarkable.

## What it does
Off the hot loop, the harvest already reads each managed session start→watermark and crosses compact
boundaries. Add one **per-session rollup** it emits alongside the register upserts: a small score over
(a) **throughput**, (b) **win : problem candidate ratio**, and (c) a checklist of **which known
frictions were AVOIDED**. When a session clears the good list and dodges the bad one, flag it
`exemplar=true` and surface it — as a one-line note in the harvest summary and an `exemplar_sessions`
list in `active_issues.json` — so the operator knows *which whole sessions to study and replicate
wholesale* (arguably higher-value than any single cataloged win). **Never a Stop signal, never a
`/goal` gate.**

## Mechanism (DB-free, over data the harvest already holds)
Per managed session, from the orchestrator transcript span + the subagent transcript dir
(`<session>/subagents/agent-*.jsonl`, which the harvest does NOT yet read — see the known-gap TODO
"b") + the register deltas this run produced:

- **Throughput proxies** (cheap, transcript-derivable): kernel-pure commits in span; distinct worker
  branches dispatched + their closed/partial verdicts; commits-per-active-hour; gate passes (validate
  N/N) in span.
- **Win : problem ratio**: count this run's win-class vs problem-class candidates (the consolidator
  already has these before it dedups them — capture the *pre-dedup* counts, which is the signal that
  today gets destroyed by stacking).
- **Friction-AVOIDED checklist** — the discriminating feature. Score the session for the *absence* of
  the register's highest-frequency frictions, e.g.: no `compact-delta` re-orientation-cost finding on
  its boundary; no goldfish-reseed; no `proof-strategy-tunneled`; no context-window-deferral; no
  unproductive-subagent-grind. A session that hits the win list **and** the avoided list at unusual
  density is the exemplar signature.
- **Flag + surface**: `exemplar = (throughput ≥ p75 of recent sessions) ∧ (win:problem ≥ threshold) ∧
  (frictions_avoided ≥ K)`. Emit the rollup to a new `session_rollups.jsonl` and, if flagged, to
  `active_issues.json.exemplar_sessions` + the harvest one-line summary. Thresholds tunable; start
  descriptive (log the score for every session) before making the flag load-bearing.

## Why this isn't a normal recurrence proposal
GAP-A proposals normally fire when a **problem** recurs across ≥3 compact-events (README). This is the
inverse: it mechanizes detection of **excellence**, and its trigger was a single session plus a
first-principles argument about a structural blind spot, not a recurrence tally. Flagging it here so
`/debrief` can decide whether to (a) build the descriptive rollup now, (b) also close the
**subagent-transcript harvest gap** (TODO "b") since branch-level throughput is the richest exemplar
signal and is currently invisible, or (c) reject.

## Dependencies / notes
- Best implemented **together with** extending the harvest to enumerate + extract subagent transcripts
  (the known-gap TODO "b" in the harvest skill) — the per-branch verdict/commit data is the strongest
  throughput signal and lives only in those separate transcripts.
- Companion artifact: the worked example this proposal came from —
  [SESSION_20260712_gold_standard_analysis.md](../SESSION_20260712_gold_standard_analysis.md) — which
  traces all 15 branches and is exactly the kind of study the flag should trigger.
