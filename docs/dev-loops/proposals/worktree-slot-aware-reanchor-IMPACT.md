# Impact Assessment — slot-aware post-compaction re-anchor

**Companion to** [worktree-slot-aware-reanchor.md](worktree-slot-aware-reanchor.md) (APPROVED build task).
**Prepared** `/debrief` 2026-07-04 after reading the 7 ADRs, the Live-Anchor spec, the probe, the
payload builder, the marker writer, reset_slot, and the hook wiring. **Status: pre-implementation —
two design decisions below need the operator's call before I write code.**

---

## 1. The defect (verified in code, not just self-report)

Both live-anchor surfaces are **main-rooted**, so a slot-venue goal re-anchors on the wrong tree:

- **The probe** — `scripts/repo_state_probe.py`. `default_repo()` anchors on `__file__.parent.parent`
  (= main repo), and **every** git call runs `cwd=repo`. So `git status --porcelain` (§3, line 269),
  the `git log <arm>..HEAD` delta (§1-2), `HEAD` (line 248), and active-file detection all reflect
  **main's** tree. A slot's branch HEAD, its ahead-of-main commits, and its dirty draft are
  structurally invisible.
- **The injected pointer** — `harness_common.live_head_anchor()` (line 461) runs `git -C root` on
  main and emits `LIVE ANCHOR … HEAD=<main-sha>`. `FIRST_ACTION` (line 384) then sends the agent to
  the main-rooted probe.

Net: after a compaction, a solo-on-wt2 goal (this is exactly the 5q.H `20260703T155014` case, and the
`20260702T184323` case before it) is told main is HEAD and clean, while the live work sits ahead and
dirty on `worktree-wt2`. Worst case it commits/reasons against the stale tree.

**Why the fix is mechanically clean:** worktrees are first-class git — `git -C <slot>` yields the
slot's own HEAD/branch/status against the *shared* object DB. So `git -C .claude/worktrees/wt2 log
main..HEAD` and `… status --porcelain` give exactly the slot state the probe needs. The hard part is
**not** git; it is knowing *which* slots the goal owns (§3).

## 2. This *completes* an existing design principle (lowers risk)

Live-Anchor spec §A already asserts the isolation intent verbatim:

> *"The probe resolves the current session's marker only (never iterates all markers), so two
> simultaneous goals each see their own arm anchor and active set."*

The slot-blindness is a **gap in that principle**, not a new one: the probe isolates the *marker* but
then reads *main's* tree instead of the session's slot. The fix extends "current session's marker
only" to "current goal's owned slots only." It is squarely within the locked design intent, which is
why this is a targeted change, not a redesign.

## 3. THE core design decision — where "goal → owned slots" lives

There is **no** goal→slot binding today (verified: marker schema is
`{role, goal, goal_id, mode, arm_sha, armed_ts, roadmap_path, notebook_path, jsonl_path, repo,
question_guard}` — no slot field; slots are purely conventional). Pure git-detection of "which slot
is live" (ahead-of-main or dirty) is **rejected**: with 2 goals each on their own worktree, goal A's
probe would see goal B's ahead/dirty slot and inject it → the exact cross-goal bleed the operator
flagged as "as severe as the stale-main error." **An explicit per-goal ownership record is required.**

Ownership must be **dynamic** — a goal engages/reassigns slots mid-loop (fan-out via `/reset-slot` +
`lean-worker`; solo picks one slot; both can change across the run). So an arm-time-only field is
insufficient; the record must be updatable when a slot is engaged.

**Recommended design (hybrid): marker `slots` list as the ownership filter + git for liveness.**
- **Ownership (the isolation filter):** the marker gains `slots: [<n>, …]` — the slots THIS goal owns.
  Small, per-goal, already the isolation key, single source of truth, torn down with the marker.
- **Liveness (computed fresh, never stored):** at probe time, for each *owned* slot, `git -C <slot>`
  computes branch / HEAD / ahead-of-main / dirty. The "live" slot = the owned slot that is
  ahead-of-main or dirty (tie-break: most recent commit). No liveness state persists → no staleness.

This satisfies all three constraints: **isolated** (only owned slots), **dynamic** (git liveness is
live), **degrades cleanly** (empty/absent `slots` ⇒ today's main-only behavior, fail-open per
principle 6).

### Decision 3a — who STAMPS ownership into the marker
- **(A, recommended) `reset_slot.py` stamps it.** `/reset-slot N` is already the prep-step before a
  goal uses a slot (fan-out *and* solo). It runs inside the goal session, so it can resolve the
  current marker (same `resolve_marker` the probe uses) and add `N` to `slots`. Natural claim point;
  also the place to **detect a conflict** (refuse/ warn if slot N is already owned by another goal's
  marker — a bonus isolation guard the current unmerged-commit check doesn't give).
  - *Gap:* a solo goal that works a slot **without** `/reset-slot` wouldn't stamp. Covered by
    arm-time declaration (Decision 3b) + a one-line goal-dev instruction to stamp on first slot use.
- **(B) A sibling `slot_binding_<goal_id>.json`.** Keeps the marker schema frozen, but adds a second
  per-goal truth source + its own teardown/GC. I prefer (A) — one source of truth per goal.

### Decision 3b — arm-time declaration
The `goal-prompt` skill (marker writer) gains an **optional** `slots` line: if the goal already knows
its venue ("solo on wt2", "fan out wt1/wt2"), record it at arm. Otherwise omit and let 3a populate it.
Matches how `mode`/`active_hint` are set at arm. **Backfill the live 5q.H marker** (`20260703T155014`)
by hand with `slots: [<its live slot>]` — a one-time migration, exactly as `arm_sha` was backfilled.

## 4. Exact edit sites + blast radius

| # | File | Change | Risk |
|---|------|--------|------|
| A | `scripts/repo_state_probe.py` | Resolve owned slots from the marker; for each, add a per-slot section (`git -C <slot>` branch/HEAD/ahead/dirty); flag the LIVE slot as the re-anchor tree; keep main as merge target. Self-resolves (no caller flag); `--slot` override for tests. | Med — most logic; fully fail-open |
| B | `harness_common.live_head_anchor()` | When the goal owns a live slot, the ~1-line pointer names it: `LIVE ANCHOR: work on wt2 @ <sha> (main @ <sha>) — anchor there`. **Pointer-grade only** (principle 1: 10k cap sacred — no per-slot dump in the payload). | Low |
| C | `reset_slot.py` | Stamp `slots` into the current goal's marker on reset; optional cross-goal-ownership warning. | Low |
| D | `goal-prompt` SKILL.md | Optional arm-time `slots` line + schema doc. | Low (doc) |
| E | Live-Anchor spec + HARNESS_GUIDE | Document the slot-aware anchor + the marker `slots` field. | Low (doc) |
| F | tests | Multi-slot fixtures: owned-slot isolation (goal A never sees goal B's slot), liveness detection, fail-open on absent `slots`, dirty-slot surfacing. | Low |
| — | Backfill | Hand-set `slots` in the live 5q.H marker. | Low (1-time) |

**NOT affected (verified against ADRs):**
- **ADR-005 D-A (DB-free):** change is git-only; no Postgres. ✓
- **ADR-005 D-I (atlas frontier):** the frontier is global; per-slot anchoring repeats the same
  frontier, never fragments it. ✓
- **ADR-004 #16 / ADR-007 (assumption + no-go ledgers):** repo-wide, not slot-scoped — untouched.
- **ADR-002 (native_decide / kernel-purity wording):** repo-wide — untouched.
- **SessionStart firing model:** fires **once** per session; we emit per-slot *lines*, we do **not**
  fire the hook per slot (the Explore map's "conditional per-slot fire" is not the design).
- **Coaching block / SETTLED GOAL / RE_ANCHOR / PRE_DECISIONS:** unchanged.

## 5. Risks & mitigations
- **Stale `slots` after teardown / slot reuse.** A goal that ends without clearing its marker, then a
  new goal reuses that slot: mitigated because the marker is torn down by `/goal-end` / session-end
  (ties to open finding `harness-gap-goal-clear-leaves-marker-live`); a new goal writes a fresh
  marker. `reset_slot`'s conflict check is the belt-and-suspenders.
- **Worktree missing / detached.** `git -C <slot>` fails → that slot's section prints
  `(wtN unavailable)` and the probe continues (principle 6). Never blocks.
- **Over-injection into the 10k payload.** Guarded by keeping B pointer-grade; full per-slot detail is
  agent-run-probe only (progressive disclosure, principle 1).
- **mode gating.** Slots are a Lean-fan-out construct but the isolation principle is general; make the
  slot section **mode-agnostic but binding-gated** (emits only when `slots` is non-empty), so a
  non-Lean goal with no slots is unaffected.

## 6. Test / verification plan (deterministic, no live LLM — matches the existing 41-test discipline)
1. Owned-slot isolation: marker A `slots:[1]`, marker B `slots:[2]`; probe A shows only wt1, never wt2.
2. Liveness: a slot ahead-of-main+dirty is flagged LIVE; a clean at-main owned slot is shown, not LIVE.
3. Fail-open: absent/empty `slots` ⇒ byte-identical to today's main-only output.
4. Missing worktree ⇒ `(wtN unavailable)`, exit 0.
5. Pointer budget: `build_reorientation_payload` stays < `PAYLOAD_MAX_CHARS` with the slot line.
6. `reset_slot` stamps `slots` idempotently; conflict warning fires when the slot is another goal's.

## 7. Decisions — RESOLVED (operator, 2026-07-04) + implementation
1. **Binding home** → marker `slots` field. ✓
2. **Stamp owner** → `reset_slot.py` auto-stamps the **active goal's** marker (exclusive transfer:
   removes the slot from any other marker) + an **ownership guard** that refuses to reclaim a slot
   another goal's marker owns unless `--force` (the escape hatch); the existing unmerged-commits guard
   remains the hard work-loss protection (piggybacked, per operator). Stale goals need no liveness
   detector — handled by existing `/goal-end` / session-end teardown + `gc`. ✓
3. **Scope** → full pass. ✓

**Implemented 2026-07-04** (140/140 harness tests green; 15 new in `tests/test_slot_aware.py`):
- `scripts/repo_state_probe.py`: `slot_states()` / `slot_delta()` + a top-of-report LIVE-slot warning
  + an "OWNED WORKTREE SLOTS" section (per-slot branch/HEAD/ahead/dirty + the live slot's own
  `git log main..HEAD`); main sections relabeled `[MAIN]`. Self-resolves owned slots from the marker.
- plugin `harness_common.py`: `_live_slot_pointer()` (pointer-grade, budget-safe) prepended by
  `live_head_anchor(root, marker)`; call site updated.
- plugin `reset_slot.py`: `--force`, pre-reset cross-goal ownership guard, post-reset
  `_stamp_ownership()` with exclusive transfer.
- `goal-prompt` SKILL + Live-Anchor spec §B: document the optional `slots` field.

**Backfill:** N/A — the live 5q.H marker was torn down (goal ended) before backfill; the feature
takes effect on the next goal's arm or first `/reset-slot`. **Remaining:** refresh the plugin cache
(source→cache) so a running loop picks it up, and commit (operator's call).

## 8. Adversarial review round (fresh-context Opus, 2026-07-04)
Six findings; four fixed, two dispositioned-no-fix. All fixes tested (suite now 24 slot-aware /
149 harness, green):
- **#1 (BLOCKER as rated) hardcoded `main`** → FIXED. Added `base_ref()` (resolves the primary
  worktree's branch, falls back to `main`) and threaded it through `slot_states`/`slot_delta`/
  `_live_slot_pointer`/`reset_slot`. Rated BLOCKER by the reviewer but over-severe for this repo (the
  whole slot harness is `main`-by-construction and pre-existing `reset_slot` already hardcoded it); the
  fix removes a real silent-degrade for sibling deployments. New test on a `master`-default repo.
- **#2 (MAJOR) unmerged-commits guard defeated on git error** → FIXED. `reset_slot` now refuses on
  `rc != 0` (not just non-empty output), so a bad base ref can't silently pass the guard. New test.
- **#3 (MAJOR) `slots` as a bare string mis-parses into per-char slots (isolation breach)** → FIXED.
  `isinstance(list)` guard in `slot_states` / `_live_slot_pointer` / reset paths → fail-open to []. New test.
- **#4 (MINOR) two `goal_id`-absent markers collide** → FIXED. `_other_owners` treats
  `cur_goal is None` (and both-absent) as a conflict (safe default; `--force` escape). New test.
- **#5 (MINOR) detached-HEAD cosmetic** → NO FIX (reviewer agreed; `ahead` still computes correctly).
- **#6 (MINOR) out-of-session reset refuses** → NO FIX (defensible safe-default; message already
  names `--force`).
- Reviewer non-findings confirmed clean: field-preservation on transfer, same-goal non-conflict,
  `marker=None`/`[]`/`[None]`/`["wtX"]` fail-open, broken-worktree fail-open + exit-0. Added explicit
  regression tests for field-preservation, the `--force` end-to-end path, and broken-worktree exit-0.
