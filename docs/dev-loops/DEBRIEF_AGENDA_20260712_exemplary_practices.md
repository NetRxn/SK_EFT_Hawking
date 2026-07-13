# `/debrief` promotion agenda — exemplary practices from the 2026-07-12 Phase 5q.H loop

> **What this is.** A pre-staged agenda for the human-governor step. The 2026-07-12 harvest
> (session `6b847cb9`, goal `20260712T150610`) surfaced a run of exemplary dev-loop practices.
> The register-aware consolidator already filed all of them as **recurrences on existing
> Process Wins** — it wrote **0 new wins** precisely because homes existed. So the practices are
> *captured*; what remains is **graduation**.
>
> **The graduation pathway (already built — this doc just feeds it).** `/skeft-qa:debrief` is the
> sole promoter to `human-reviewed` (it's user-only by design: `disable-model-invocation: true`).
> For a **Process Win**, promotion runs the **win LIFECYCLE**:
>
> > promote → **integrate the best practice into the harness** (a CLAUDE.md line / the relevant
> > skill / context bootstrap) → then **close** it (it now lives in the harness).
>
> That integration is the replication mechanism. A win stuck at `agent-reviewed` is a note; a
> promoted win is a standing instruction the next loop inherits.
>
> **Current state:** of 47 Process Wins, only **1** has graduated (`notebook-driven checkpointing`,
> 21+ occurrences, `human-reviewed`, already integrated). Everything below sits at `agent-reviewed`,
> ripe or maturing.
>
> **This doc is not authoritative and does not mutate anything.** It does not edit the register
> (the CLI + `/debrief` own that) and does not touch CLAUDE.md/skills (those need per-win sign-off,
> per the "self-improving, never self-mutating" rule). It is a convenience agenda: open it alongside
> `/debrief` so each promotion is a fast sign-off with the integration edit pre-drafted.

---

## How to run the graduation

```
/skeft-qa:debrief
```

For each cluster, `/debrief` asks: **promote** / **close** / **misfile** / **leave**. For the wins
below, "promote" = confirm the practice → apply the proposed harness edit → close. The command owns
the register write (`system2_register.py --upsert --promote`); do **not** hand-edit the markdown.

Ripeness is a judgment call (recurrence tally is the signal, not a threshold). My read: the four
**RIPE NOW** wins have earned integration; the **maturing** ones are worth one more recurrence unless
you already believe them.

---

## RIPE NOW — high recurrence, agent-reviewed, not yet in the harness

### 1. Substrate-scan / hunt-first: audit for pre-built infrastructure before building
- **Register home:** `process-win-substrate-scan-route-tree-reuse-audit-before-committing-ro` · `agent-reviewed` · **occ 10**
- **This run reinforced it twice:** (a) the "#1 blocker" (`hcoreG`, flagged as needing "genuine
  un-built manifold topology") dissolved on a **direct read of the mod-2 source** — it was
  coefficient-agnostic algebra, not geometry; (b) `SingularPD4Instances` already contained the
  hypothesis-free `poincareDual4Mid/Lo_of_closed`, so the flagged "mod-2 FG wall" was **already
  solved in-tree**; (c) N5's witness tower was found **complete in-tree** by search-before-build.
  The loop now dispatches workers with explicit **hunt-first orders**.
- **Proposed harness integration (on promote):** add to `CLAUDE.md` §"Lean development — MCP-first
  loop" hard rules: *"Hunt-first: before building any infrastructure, search the repo (semantic
  search) and the pinned Mathlib for an existing kernel-pure declaration — five+ loops running, this
  repo keeps surprising us with pre-built infra. Wire before you build."* Also add a one-line
  hunt-first mandate to the `skeft-qa:lean-worker` dispatch-brief template.

### 2. Git due-diligence: read commit history + statement before re-deriving
- **Register home:** `process-win-git-due-diligence-check-commit-history-and-statement-befor` · `agent-reviewed` · **occ 7**
- **This run:** the over-diagnosis correction (see #1) and the worktree-reconciliation adjudication
  (below) are both instances of reading the actual source/history instead of trusting a prior
  verdict or a summary.
- **Proposed harness integration:** a `CLAUDE.md` line under "Process health": *"Before re-deriving
  a blocker a prior turn/summary flagged, read the actual source + git history — over-diagnoses
  dissolve on direct read."* (Pairs naturally with #1 into one "read-first" hard rule if you prefer
  a single edit.)

### 3. MCP-first Lean dev loop: per-brick diagnostics + multi-attempt, zero-diagnostic first passes
- **Register home:** `process-win-mcp-first-lean-dev-loop-per-brick-diagnostic-multiattempt-` · `agent-reviewed` · **occ 5**
- **This run:** sustained clean-first-pass compiles (J₀, L₀, M₀ mirrors — "zero diagnostics"),
  driven by pre-staging signatures and `lean_goal`/`lean_multi_attempt` before writing tactics.
- **Note:** CLAUDE.md already documents the MCP-first loop, so this promotion is largely a
  **confirmation + close** ("integrated: already the documented loop") rather than a new edit —
  unless you want to add the "pre-stage helper signatures before drafting a brick" refinement.

### 4. Anti-thrash lock: cite-and-revert self-enforcement against re-tunneling
- **Register home:** `process-win-anti-thrash-lock-self-enforcement-cite-and-revert-defeats-` · `agent-reviewed` · **occ 11 (highest tally in the register)**
- **Not specific to this run**, but it's the most-recurring un-graduated win and overdue for a
  decision. Worth folding into this pass while you're here.
- **Proposed harness integration:** a bootstrap/`goal-dev` line codifying the cite-the-lock-and-revert
  pattern when the loop notices it's re-opening a settled route.

---

## MATURING — real, but light tally; stack once more or promote if already convinced

| Practice | Register home | Tier · occ | This run's evidence |
|---|---|---|---|
| Machine-encode dead forks (module + `KERNEL_NOGO_REGISTRY` + integrity check), not prose | `machine-feed-negative-frontier-dead-forks-to-every-agent-s` | `agent-reviewed` · 2 | `FGDualityNoGo.lean` as 5th registry entry; **deliberate fork-skip with rationale** (skip refutations against already-resolved cruxes). |
| Research-scout returns a **durable filed verdict**, not a page dump | `research-scout-primary-source-grounding-breaks-multi-agent` | `agent-reviewed` · 2 | Erdős–Kaplansky-over-ℤ impossibility → banned `5qH-fg-ek-over-Z-blocked` in SETTLED_FORKS + Lit-Search file + re-scoped the branch. |
| Safe lead-parallel: named slots, non-overlap, verbatim tool-rules baked into briefs | `safe-lead-parallel-agent-concurrency-named-slots-overlap-c` | `agent-reviewed` · 2 | wt2/wt3 dispatched with mandatory-read stack + hard rules + deliverables; tool guidance ("semantic search over grep") embedded verbatim. |
| Evidence-based disclosed-not-discharged, frozen-debt mapped 1-1 to published proof steps | `evidence-based-durable-disclosed-not-discharged-call-on-no` | `agent-reviewed` · 3 | E2's frozen debt shown to map 1-1 onto Taylor Lemma 1.2's own proof steps. |
| Worktree-slot reconciliation as a codified adjudication law | `worktree-slot-dispatch-with-ff-only-main-gating-for-single` | `agent-reviewed` · 3 | `git cherry -v` + subject-grep to distinguish patch-identical duplicates from genuine unmerged work; embedded as a FIRST_ACTION guard in the arm-2 goal prompt. |
| Read-first master execution-map for multi-worker/multi-effort dispatch (materialized gap-map N1–N5) | `read-first-master-execution-map-for-multi-effort-multi-wor` | `agent-reviewed` · 1 | ASSEMBLY_GAP_MAP updated in place each round as the authoritative frontier source for dispatch. |

---

## ALREADY GRADUATED — confirmed durable this run (no action)

- **Notebook-driven checkpointing / compaction-durable source-of-truth** — `human-reviewed` · occ 21+.
  This run added a textbook confirmation: **clean post-compaction re-orientation with zero goldfish
  reseed** (827k tokens dropped; the loop read the 9-section summary, ran FIRST_ACTION, verified the
  frontier matched exactly, and resumed on-node) and a **kernel-critical anti-commutation finding
  preserved across the boundary** (the −openDuality₀ sign-twist re-cited, not re-proved). Already
  integrated into the harness; these occurrences just reconfirm it holds.

---

## Problem-side residue (not a win — flagged for the Open sweep / a possible GAP-A gate)

The one recurring friction worth a `/debrief` decision on the problem side:

- **Pre-drafting N/N validation claims before reading gate output** — happened **twice this arm**
  (round-2 and round-4, both landing 45/46). The loop self-logged the countermeasure *"verdict
  first, message after."* Its **coupled cause**: a `HYPOTHESIS_REGISTRY` edit that skipped
  `render_tracked_hypotheses.py` regen in the same commit (the check hard-fails on drift by design).
  - **Candidate GAP-A prevention** (for `proposals/`, if you want a structural gate rather than a
    prose rule): a pre-commit / `validate.py` coupling check that fails when `HYPOTHESIS_REGISTRY`
    changes without a matching `render_tracked_hypotheses.py` regeneration in the same commit — which
    also removes one of the two "surprise 45/46" triggers behind the pre-drafting friction.

---

*Generated from the 2026-07-12 System-2 harvest. Register truth lives in
`docs/dev-loops/SYSTEM2_REGISTER.md`; this agenda is a convenience view and may go stale — reconcile
against the register at `/debrief` time.*
