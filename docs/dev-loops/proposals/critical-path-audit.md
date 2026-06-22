# GAP-A proposal: critical-path / layer-size audit (atlas-derived)

**Status:** APPROVED (`/debrief` 2026-06-22). **Atlas:** ADR-005 Phase 1.

> **Primitive note (general, not 5q.F-specific):** the decomposition unit here is a **wave / objective**
> (the project's structure), grouped by **phase/wave** in the atlas (ADR-005 D-H). "L1–L5" was 5q.F's
> one-off relabeling; "layer" is **not** a harness primitive — read "wave/objective" throughout.

**Mechanizes** the goal-scoping finding (`goal-scoping-multi-layer-goal-under-scoped-…`): a multi-layer
goal was under-scoped, the layer-size imbalance not surfaced until the user pressed — and then as a
*defeated "multi-month" calendar estimate* the user rejected.

## What it does
Produce a dependency-ordered **critical-path / layer map in harness-reference-class (node/brick
counts), keystone flagged** — at goal-arming and on demand — so "L2's last lemma open while L3–L9 +
other waves sit untouched" is visible at a glance. **Never a calendar / person-year estimate** (honors
`feedback-ignore-pm-estimates`).

## Mechanism (REAL Phase-1a interface)
From `lean/atlas_view.json` (`frontier` + per-node `frontier_impact`; verified against
`scripts/atlas_view.py`):
- **Frontier ranking** (Phase-1a proxy for the critical path) = the atlas `frontier` array — open
  assumptions ranked by `frontier_impact` (immediate dependents gated, 1-hop), highest first. A true
  dependency-ordered *chain* to the goal endpoint needs Phase-2 (`is_apex` endpoint + transitive
  edges); Phase-1a surfaces the ranked keystone + the per-module imbalance, which is enough to make
  "L2's keystone open while other modules sit untouched" visible.
- **Wave/objective map** = per-module-path (the Phase-1a phase/wave proxy) open-node counts + each
  module's top-impact residual; flag the imbalance (a module whose one open keystone gates many
  immediate dependents).
- **Keystone** = the single open node whose closure unblocks the most (max `frontier_impact`; the top
  of `frontier`) — the thing to focus on now.

## Where it lives (goal-safe)
**(a)** `goal-prompt` arm-time: emit the map into the goal/notebook so the loop has the structure and
the user can re-scope *before* arming; **(b)** `/orient` on demand. Counts only — no calendar.
Off-loop / authoring-time; nothing competes with `/goal`.

## Phase-2 sharpening
Derivable phase/wave (D-H) → a true per-wave layer audit; `is_apex` → the curated apex as the
critical-path endpoint.

## Sign-off ask
Approve the atlas-derived critical-path / layer map as a `goal-prompt` + `/orient` artifact, in
node-count reference-class only.
