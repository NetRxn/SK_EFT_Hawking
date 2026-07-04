# GAP-A proposal: dynamic, goal-isolated slot-aware post-compaction re-anchor

**Status:** IMPLEMENTED (`/debrief` 2026-07-04, pending cache-refresh + commit) — operator green-lit
the "A items" with the ownership model refined below. Acceptance criteria met: dynamic per-goal slot
binding (marker `slots`) + cross-goal isolation + fresh git liveness. 140/140 harness tests pass
(15 new in `tests/test_slot_aware.py`). Implementation detail + blast radius:
[worktree-slot-aware-reanchor-IMPACT.md](worktree-slot-aware-reanchor-IMPACT.md). Files touched:
`scripts/repo_state_probe.py` (slot_states + report section), plugin `harness_common.py`
(`_live_slot_pointer` + `live_head_anchor(marker)`), plugin `reset_slot.py` (stamp + exclusive
transfer + `--force` ownership guard), `goal-prompt` SKILL (schema), Live-Anchor spec §B.
No hook, no gate, no auto-action; a signal/correctness fix on the probe + SessionStart re-inject.

**Mechanizes** `harness-gap-post-compaction-repo-state-probe-slot-blind-in-multi-worktree-goal`
(self-flagged by the loop in-transcript; recurred across goals `20260702T184323` and
`20260703T155014` in one week).

## The failure (sharpened past the register's original framing)
The register first logged this as an *observability* gap ("the probe reports main HEAD/tree only and
misses wtN state"). The operator (2026-07-04 review) re-framed it as a **re-orientation correctness
hazard**: when the live branch is ahead/dirty on a worktree slot, the post-compaction probe presents
**stale `main` as the tree to re-anchor on**. A loop that trusts that injection reasons against — or
worse, commits against — the wrong tree, re-deriving or clobbering work that only exists on the slot.
The clean-path counterexample `compact-delta-positive-clean-reentry-via-first-action-probe` (tally 5)
confirms the probe works *when pointed at the right tree*; the defect is that it is pointed at `main`.

## Load-bearing design constraint — DYNAMIC + goal-isolated (operator, 2026-07-04)
The fix is **not** "always sweep wt1/wt2/wt3." A goal owns *some, all, or none* of the slots, and the
mechanism must make **N goals × N worktrees** as safe as **1 goal × 1 worktree**:

1. **Dynamic slot binding.** Resolve *which slots THIS goal actually owns* at probe time — never a
   fixed slot list. Source of truth = a per-goal "goal → owned slots" binding, not directory
   enumeration (a bare `.claude/worktrees/*` scan cannot tell whose slot is whose).
2. **Cross-goal isolation is a hard invariant.** Injecting *another* goal's slot state into this
   goal's re-anchor is **as severe** as the stale-`main` error. Example that must work: 3 phases / 3
   goals, each with its own worktree, each re-anchoring only on its own slot — zero bleed. The probe
   must therefore filter to the current goal's owned slots and emit nothing about the others.
3. **Single-worktree and zero-worktree goals degrade cleanly.** A solo-on-one-slot goal shows that
   one slot; a no-worktree goal shows `main` as today (no regression, no empty slot noise).

## Mechanism (candidate — to be settled at build time)
- **Establish the binding.** When a goal arms a slot (the `goal-dev` / reset-slot / lean-worker
  dispatch path), record `goal_id → {slot_root, branch}` in the goal's marker or a sibling
  `slot_binding_<goal_id>.json` under `.claude/dev-harness/`. The marker already carries `goal_id`
  and a venue description; make the slot ownership *structured*, not prose.
- **Probe reads the binding, not the filesystem.** The post-compaction repo-state probe, for the
  current `goal_id`, emits one line per *owned* slot — e.g.
  `wt2: worktree-wt2 @ 28288ae0 (clean | 6 uncommitted edits) [LIVE: goal's active branch]` — and
  flags which slot holds the live work vs. `main`. If the goal owns no slots, it emits `main` only.
- **Re-anchor injection targets the slot, not main.** The SessionStart re-inject's state block leads
  with the *owned live slot's* HEAD/branch/dirty state as the tree to re-anchor on, with `main` shown
  as the merge target — inverting today's main-first default for slot-venue goals.

## Where it lives (goal-safe)
Purely in the harvest/probe/inject machinery + the arm-time slot-binding write. **No new hook;
nothing competes with `/goal`; self-improving-not-self-mutating** (a truthful state signal, not an
auto-action). The binding write is the only new arm-time step; everything else is read-side.

## Open questions for build
- Where the binding is authoritative: extend the marker vs. a sibling `slot_binding_*.json`.
- Whether `reset-slot` / `lean-worker` must update the binding on slot reassignment (they should).
- Staleness: if a goal ends without tearing down its binding, the next goal reusing that slot must
  overwrite, not inherit (ties to the existing `harness-gap-goal-clear-leaves-marker-live` finding).

## Sign-off ask
Approve as a tracked build task: **(a)** an arm-time `goal_id → owned-slots` binding write, **(b)** a
probe/inject read-side that emits *only the current goal's* owned-slot state and points the re-anchor
at the live slot. Dynamic + goal-isolated are acceptance criteria. No hook, no gate, no auto-action.
