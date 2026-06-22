# GAP-A proposal: hypothesis-banking mechanical-discharge (PD-2)

**Status:** APPROVED (`/debrief` 2026-06-22) — efficient (perf below). **Atlas:** ADR-005 Phase 1a.

**Performance:** even cheaper than first specced. The unlock set is **precomputed** — each `unknowns`
entry in `lean/atlas_view.json` already carries its own `dependent_theorems` + `frontier_impact`, so
the check is an O(V) pass over `unknowns` with **no cone traversal**. It rides the existing Phase-1a
derivation cost (the shared atlas cost Phase 1b is optimizing); it adds none → sub-second.

**Mechanizes** PD-2 + the L2 nuance: the loop self-vetoed a "bank this tracked Prop to reach a later
wave" decision (forbidden by the goal's NO-disclosed-Prop AC + the unreachable user-decision escape);
separately, a mid-stall discharge plan is **untrustworthy** (the trust horn) while scattering
hypotheses forces back-payment (the proliferation horn).

## What it does
Make "bank a tracked Prop to unblock downstream" a **mechanically-checked** move — so the loop and the
coach can do it correctly and the user can trust the request — replacing the narrative discharge plan
with a graph fact.

## Mechanism (REAL Phase-1a interface)
A tracked-Prop = an **UNKNOWN node** (`atlas_kind = UNKNOWN`, sourced from `HYPOTHESIS_REGISTRY`),
carrying `dependent_theorems` (the theorems that rest on it) and `frontier_impact =
len(dependent_theorems)`, wired to those theorems by the atlas `edges` (`type: "ASSUMED_BY"`,
hyp → dependent theorem). There is **no** `PROVABLE`/`FULLY_CLOSED` recompute in Phase-1a — the unlock
set is the **precomputed `dependent_theorems`**, not a re-derived cone.
- **Bankable iff** `dependent_theorems` is **non-empty** (`frontier_impact ≥ 1`) — it gates ≥ 1 real
  theorem. A Prop that gates nothing (empty `dependent_theorems`) isn't worth banking; a "discharge
  plan" that names no dependent theorem is the exact mid-stall rationalization PD-2 guards against.
  Strength = `frontier_impact` (rank against the `frontier` array).
- **Proliferation bound:** ≤ 1 new UNKNOWN (banked Prop) per **wave/objective boundary** (the goal's
  decomposition unit; 5q.F's L1/L2 was a one-off label). The per-module/phase UNKNOWN-count is the
  L1-clean-vs-L2-scatter measure; scatter is flagged.

## Where it lives (goal-safe)
**(a)** the **coach** (PD-2) runs the non-empty-`dependent_theorems` check to decide bank-or-grind
under grounded confidence; **(b)** `validate.py --check atlas_hypothesis_discipline`: every registered
UNKNOWN gates ≥ 1 dependent theorem (no orphan assumption), and the per-boundary UNKNOWN-count is
within bound. Off-loop / build-gate; no new CC hook.

## Phase-2 sharpening
`is_apex` sharpens the target (does the Prop gate the *curated apex*, not just *some* theorem);
a transitive `frontier_impact` (Phase-1a is 1-hop) measures the full downstream it unlocks.

## Sign-off ask
Approve **(a)** the coach's mechanical non-empty-`dependent_theorems` unlock-check + **(b)** the
`validate.py` invariant (every tracked hypothesis gates ≥ 1 theorem + per-boundary proliferation
bound). Banking a Prop **still needs explicit user sign-off** (CLAUDE.md axiom/disclosed-Prop policy) —
this makes the request *trustworthy and bounded*, not auto-approved.
