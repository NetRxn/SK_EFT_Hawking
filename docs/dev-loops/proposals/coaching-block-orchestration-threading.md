# GAP-A proposal: thread coaching-block authoring into the harvest skill orchestration (+ verify + report)

**Status:** DRAFT — for `/skeft-qa:debrief` sign-off. Never auto-applied. Edits target the **harvest
skill** only (`skills/harvest/SKILL.md`); no `/goal`-wording change, no hook, no gate, no `validate.py`
check. (Honors spec §1 principle 6 — self-improving, not self-mutating.)

**Origin:** diagnostic session 2026-06-23 (harvest of goal `20260617T231250`, session `8ca6a498`). Not
yet a numbered System-2 finding — recommend filing as a `harness-gap` finding alongside this proposal
(see "Register companion" below). Sibling to the coaching-dependent corrective layer in
`process-meta-rca-keepshipping-no-convergence-gate-5qf-l2` (the per-goal coaching block IS the relevance
layer the RCA's tier-2 brief relies on).

## The failure it prevents

The per-goal **coaching block** (`coaching/<goal_id>.json`) — the forward-framed post-compaction
re-orientation the SessionStart re-inject surfaces, which **replaced the blind active-issues
injection** — was **never authored** for goal `20260617T231250` despite a full harvest run. The
`coaching/` dir has been empty since it was created (2026-06-22); the authoring step has effectively
**never fired for any goal**.

Root cause is two independent layers:

1. **Cache/scope miss (separately fixed, not this proposal).** The goal + harvest bind the
   **workspace-root-scoped** plugin install, which was pinned to a pre-coaching commit
   (`84bb411cdf68`, Jun 18) while the update landed on the **SK_EFT_Hawking-scoped** install. Fixed
   2026-06-23 by `claude plugin update … --scope local` from the workspace root
   (`84bb411cdf68 → f8a779a3077b`, a descendant that carries authoring + reader). **Open follow-up
   (deferred):** the two independent plugin scopes are themselves the footgun — consolidating to one
   scope prevents the next instance. Tracked separately from this proposal.

2. **Orchestration SPOF + zero observability (THIS proposal).** Coaching authoring lives **only** in
   the consolidator *agent definition*, never in the harvest `SKILL.md` orchestration nor in the
   runtime *dispatch prompt* the skill builds. Confirmed: `grep -c coach skills/harvest/SKILL.md`
   = **0** in every version (old cache, current `f8a779a3077b`, repo source). Consequences:
   - A stale/cached or otherwise variant consolidator that lacks the agent-def step **silently
     no-ops** — exactly what happened this run (the dispatched consolidator was the pre-coaching
     `84bb411cdf68` build and had nothing to author from).
   - The miss is **invisible**: the harvest summary line never reports coaching status, so a goal can
     run for days with its coaching layer silently un-refreshed and no signal surfaces.

The reader/writer plumbing is otherwise intact (`harness_reinject.py` SessionStart reader →
`_read_coaching_block`; `write-coaching` CLI → `write_coaching_block`). This is purely an
**orchestration + observability** gap.

## What it does

Make coaching authoring a **first-class, runtime-threaded, verified, and reported** step of the
harvest skill — robust to a variant consolidator and loud on a miss. Off the hot loop, informational
only; never a Stop signal, never a `/goal` gate.

Three edits to `skills/harvest/SKILL.md`:

### EDIT 1 — Step 4: thread coaching into the consolidator **dispatch prompt** (not the agent def alone)
Append to step 4 (after the `--write-active-issues` sentence):

> **+ Author the per-goal COACHING BLOCK (for EACH `goal_id` in this run's markers).** The
> consolidator *dispatch prompt* MUST instruct it to author one terse, forward-framed,
> facts-not-verdict coaching block per goal — the post-compaction re-orientation the SessionStart
> re-inject surfaces (it replaced the blind active-issues injection):
> `printf '%s' "<text>" | uv run --no-sync python "$CLI" write-coaching <goal_id> [<new_offset>]`.
> Thread this into the **runtime prompt explicitly** — do NOT rely on the agent definition alone; a
> stale/cached/variant consolidator may lack the step. On-track vs stalled branch per commit/notebook
> cadence; leak-safe (public tokens only). Authoring is OPTIONAL/fail-soft for the *reader* but
> **mandatory to attempt every run**: a goal left with no fresh coaching block is a harvest MISS, not
> the steady state.

### EDIT 2 — new Step 4b: verify-and-fallback (the SPOF backstop)
Insert before "5. Commit the watermark LAST":

> 4b. **Verify coaching was authored THIS run [observability backstop].** After the consolidator
> returns, for EACH `goal_id` check `$REPO/.claude/dev-harness/coaching/<goal_id>.json` exists with
> `authored_ts >= <this run's start>`. If absent or stale, author a **thin fallback** yourself from the
> live FRONTIER + the single highest-priority open register item
> (`printf '%s' "<fallback>" | uv run --no-sync python "$CLI" write-coaching <goal_id> <new_offset>`)
> and mark it `coaching=FALLBACK` in the summary. Never complete a run with a goal's coaching silently
> un-refreshed. (Watermark LAST still gates on the consolidator's register writes, not on coaching —
> coaching is fail-soft and must never block watermark advance.)

### EDIT 3 — Step 6: surface coaching in the summary line
Add one field to the one-line summary:

> …leak-drops, active-issues refreshed, **coaching [per goal: ok / fallback / skipped]**…

No change is needed in the consolidator **agent definition** — `f8a779a3077b` already carries the
authoring step (5 refs). The fix is entirely skill-side: the dispatch-prompt threading (EDIT 1) makes
it version-robust; the verify (EDIT 2) and summary (EDIT 3) make a miss loud.

## Design decisions (recommended; the two sign-off choices)

These are the two decision points surfaced in the 2026-06-23 review; the draft above encodes the
recommended resolution:

1. **Author-and-verify (RECOMMENDED) vs. skill-sole-writer.** Keep the consolidator as author + a
   skill-side verify/fallback (EDIT 2). Rationale: smaller change, matches the existing consolidator
   agent def, and the verify step is precisely what catches a miss. The alternative — consolidator
   only *returns* text, skill is the sole writer — is more robust to consolidator CLI/env drift but a
   bigger refactor; not justified given EDIT 1 already removes the agent-def dependency at the prompt
   layer.
2. **Thin labeled fallback (RECOMMENDED) vs. loud no-write.** On a synthesis miss, write a thin block
   (FRONTIER + top register item) labeled `coaching=FALLBACK` rather than refusing to write.
   Rationale: the loop is never left blind, and the label keeps the degraded quality visible. A pure
   loud-no-write leaves the next session on the bare RE_ANCHOR/FRONTIER baseline — acceptable, but the
   thin fallback strictly dominates as long as it is clearly labeled.

## Where it lives (goal-safe)

Entirely within the off-loop harvest skill, which already runs only off the hot loop (Desktop
scheduled task / second-session `/loop`). No new hook, no `/goal`-wording change, nothing competes
with `/goal`. Consistent with the RCA corrective map's "no `/goal`-wording change, all off-loop"
scoping.

## Register companion (recommended)

File a `harness-gap` System-2 finding to carry this across future harvests:
*"Per-goal coaching block authoring lives only in the consolidator agent def, not the harvest skill
orchestration → a stale/variant consolidator silently no-ops with zero observability; coaching layer
never refreshed."* This proposal is its structural fix; the cache/scope miss (layer 1) is its
triggering enabler.

## Sign-off ask

Approve EDITs 1–3 to `skills/harvest/SKILL.md` (dispatch-prompt threading + verify/fallback + summary
field), with the two recommended design resolutions above. Skill-only; off-loop; informational; no
hook, no gate, no `/goal` change. Apply via `/skeft-qa:debrief` (or in-session at the operator's
direction) — not auto-applied by this draft.
