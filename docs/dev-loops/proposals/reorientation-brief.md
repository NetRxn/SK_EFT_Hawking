# Tier-2 coaching block — the harvest-authored per-goal re-orientation (build #3)

**Status:** APPROVED (the user's own design). **Atlas:** ADR-005 Phase 1a. **Goal-safe:**
harvest-authored off-loop; read by the existing SessionStart re-inject; no new hook.

## What it is
A per-goal, freshly (re-)written-each-harvest synthesized note — the human-proxy coach's note — that
the SessionStart re-inject reads from a gitignored cache and injects as an OPTIONAL enhancement to the
post-compaction payload. The READER side is **built** (`harness_common._read_coaching_block` +
`build_reorientation_payload`); this spec is the AUTHORING side (what `/skeft-qa:harvest` writes).

## Why (the injection problem it fixes)
The old payload injected a blind top-8 active-issues list — failure descriptions that prime the loop
with "what we suck at + how to reproduce" (the user's read: this *lowers* P(success)). That injection
is **removed**. The coaching block is the forward-framed substitute: terse, specific, authored by the
harvest Opus consolidator with fresh cross-compaction context.

## It is an ENHANCEMENT, never a dependency (the lag/absence contract)
The harvest is async (default ~4h cadence), so the coaching block:
- is **ABSENT** for a new goal until the first harvest authors one (up to a cadence), and
- **AGES** between harvests (a goal can compact several times against the same block).

So the BASELINE re-orientation must not depend on it — and it doesn't: the always-injected `RE_ANCHOR`
(a payload constant — the PD-4 essence) + the **live LAB-NOTEBOOK FRONTIER** (which the loop authors
itself each turn, so it's always current) carry the re-anchor with or without a coaching block. The
reader surfaces the block's **authoring facts only** — the absolute timestamp, the age (a timedelta),
and the transcript **high-water-mark** it was authored as-of — plus a brief process note, and lets the
loop judge. **No staleness verdict is baked in** (a fixed age threshold would misjudge a fast goal vs a
slow one and could add failure modes we don't anticipate).

## Cache format (what the harvest writes)
`.claude/dev-harness/coaching/<goal_id>.json` (gitignored): `{"authored_ts": <epoch>, "watermark":
<transcript high-water-mark the harvest authored as-of — optional>, "text": "<the coaching text>"}`.
The reader wraps `text` with a brief process note + the authoring facts (timestamp, age, high-water-mark);
`text` itself is the content below.

## `text` content (what the consolidator authors)
1. **The close-path** — name THIS goal's current most-gating open node (top of the atlas `frontier`,
   or the live `CONDITIONALLY_PROVED` keystone): the specific enrichment of the generic `RE_ANCHOR`.
2. **One branch:**
   - **On-track:** brief forward reassurance — the close-path is advancing; here is the next node.
     (Atlas-independent — authorable from commit/notebook cadence alone, so this branch ships first.)
   - **Stalled** (stall-detector fired): course-correction — the load-bearing residual's `atlas_status`
     has not advanced across K compact-events while N other open residuals sit untouched; climb the
     PD-1 ladder at the matched rung (B sweep / D decompose / E arc-trace); if K keeps rising, escalate.

## Discipline
- **Forward-framed, terse** — re-orientation, not a failure catalog (the negative-priming guard).
- **No "nuke"/destructive language** (injected-artifact rule).
- **Precedence under the real 10k limit — the `/goal` condition (≤4k) ALWAYS wins.** With the
  pre-decisions now a mandatory READ (not injected), the payload is goal + RE_ANCHOR + live frontier +
  the first-action mandate + (optionally) this coaching block. The goal (≤4k, always full) and the
  RE_ANCHOR are never dropped; the **coaching block is the droppable section** — included whole only if
  it fits, dropped (never truncated mid-text) otherwise. Post-redesign there is large headroom (emitted
  ~5.6k at the 4k-goal max vs the 10k limit), so a drop is rare.

## Where it lives (goal-safe)
Harvest Opus consolidator authors the cache each pass (it already crosses compact boundaries) →
gitignored per-goal cache → the SessionStart re-inject reads it (built). Consumes the stall-detector
for the stalled branch; the on-track branch is atlas-independent. No new hook; nothing competes with
`/goal`; self-improving-not-self-mutating.

## Build status
READER + staleness + baseline-fallback + end-to-end budget: **BUILT + tested** (this conversation).
AUTHORING (the harvest consolidator writes the cache): remaining — couples with the stall-detector
(`stall-detector.md`) for the stalled branch; the on-track branch (atlas-independent) can ship first.
