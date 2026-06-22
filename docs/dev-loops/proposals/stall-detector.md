# GAP-A proposal: convergence/stall detector (off-loop)

**Status:** APPROVED (`/debrief` 2026-06-22) — build against the Phase-1a atlas; thresholds K=3 / N,M tunable; no hook, no gate, no auto-action. **Atlas:** ADR-005 Phase 1a (sufficient).

**Mechanizes** the RCA meta-finding (`process-meta-rca-keepshipping-no-convergence-gate-5qf-l2`) +
its constituents (tunneling, abstract-reasoning-too-long, goal-loop-satisfiability): the loop
optimizes *activity*, not *convergence*, so one hard keystone absorbed ~5 days of lateral motion
with nothing measuring whether the load-bearing residual got closer.

## What it does
Off the hot loop, detect that the **load-bearing residual is not converging** and surface it as the
tier-2 brief's "stalled" input + a high-priority active issue — so the next compaction's re-inject
tells the loop to climb the PD-1 ladder (not keep grinding). **Informational only** — never a Stop
signal, never a `/goal` gate, never a new hook.

## Mechanism (over the REAL Phase-1a atlas view, DB-free)
Each harvest pass (it already crosses compact boundaries), read `lean/atlas_view.json`
(`nodes` / `unknowns` / `edges` / `frontier`) + the commit/route history, per managed goal. The real
Phase-1a fields (verified against `scripts/atlas_view.py`, not the spec idealization):
- theorem `nodes` carry `atlas_kind ∈ {TRUE, OBSTRUCTION}`, `atlas_status ∈ {PROVED, OBSTRUCTION,
  CONDITIONALLY_PROVED, AXIOM_TAINTED}`, and `frontier_impact` = **immediate** reverse-dependents (1-hop);
- `unknowns` (tracked hypotheses) carry `atlas_kind = UNKNOWN`, `atlas_status ∈ {STATED, PLANNED}`,
  `dependent_theorems`, and `frontier_impact = len(dependent_theorems)`;
- `frontier` = the `unknowns` pre-ranked by `frontier_impact` desc ("which open node, if discharged,
  unlocks the most"). There is **no** `PROVABLE`/`FULLY_CLOSED` rung in Phase-1a.

1. **The load-bearing residual** = the highest-`frontier_impact` open node — the top of `frontier`
   (most-gating tracked hypothesis) and/or the highest-`frontier_impact` `CONDITIONALLY_PROVED`
   theorem node (a keystone still resting on a `sorry`) in the goal's modules.
2. **No-advance** = its `atlas_status` is **unchanged** across **K** distinct `compact_event_id`s — a
   keystone stuck at `CONDITIONALLY_PROVED` (its `sorry` never discharged to `PROVED`), or an UNKNOWN
   stuck at `STATED`/`PLANNED` (never left the registry). (Reuse the GAP-A compact-event counting;
   propose **K = 3**, the graduation threshold.) The advance that clears the residual is
   `CONDITIONALLY_PROVED → PROVED` or the UNKNOWN leaving the ledger — that binary IS the convergence
   signal (no intermediate lattice rung to read).
3. **Available-but-untouched** = there are **≥ N** OTHER open residuals (`CONDITIONALLY_PROVED`
   theorem nodes / `STATED` unknowns) in modules that received **no commits** in that window — the
   "L4/L5/W6–W9 + other waves sat available while the loop tunneled L2" signature. (Phase-1a has no
   PLANNED-theorem target node, so a true "provable-frontier, deps-all-closed" set is a Phase-2/3
   sharpening; the untouched-other-open-residual proxy is adequate and is what the atlas exposes today.)
4. **Route-proliferation** (corroborating) = ≥ M sibling attempt-modules touching the same residual
   with no status advance (the "23 `*ConnSquare*` files" smell) — from git + module paths.

`(1 ∧ 2 ∧ 3)` → **STALL**. Emit: the residual id, K, the untouched-other-open count, the matched
PD-1 rung (B sweep / D decompose / E arc-trace), and — if K keeps rising — escalate the prescribed rung.

**Corroborating signal — post-compact route-divergence (PD-4 / parallel-L2 corroboration):** if the
no-advance window straddles a **compaction boundary** AND a new/sibling route module for the residual
appears with no status advance right after it, that is the compaction-summary-re-seeds-thrash
signature. Fold it into the brief's re-anchor lead. The tier-2 brief ALWAYS leads with the close-path
re-anchor whether stalled or not (see `reorientation-brief.md`); the stall signal selects its
course-correction branch.

## Where it lives (goal-safe)
The harvest Opus consolidator computes it over `lean/atlas_view.json` + git (no DB, no Lean build) +
the transcript; writes it as the brief's stalled-branch input + a top-priority `active_issues` entry.
Rides the existing SessionStart re-inject. **No new hook; nothing competes with `/goal`;
self-improving-not-self-mutating** (a signal, not an auto-action).

## Phase-2 sharpening (not required to ship)
`is_apex` (D-E) replaces "highest `frontier_impact`" with the curated headline target; `frontier_impact`
becomes a **transitive** cone (Phase-1a is 1-hop); derivable phase/wave (D-H) scopes step 3 per-wave
and gives a true provable-theorem frontier (STATED-but-unproven targets). Until then the 1-hop
`frontier` rank + module-path are the proxies and are adequate (5q.F's keystone was the top open node).

## Sign-off ask
Approve as **(a)** a harvest computation over the Phase-1a atlas + **(b)** a brief/active-issue signal
with thresholds K=3 / N,M tunable. No hook, no gate, no auto-action.
