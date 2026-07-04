# GAP-A proposal: broad Lean-patterns progressive-disclosure doc (Lean-gated)

**Status:** DRAFT (`/debrief` 2026-07-04) — pending sign-off. A new read-only reference doc + a
pointer from the `goal-dev` skill. No hook, no gate, no auto-action.

**Mechanizes** the integration target for `lean-friction-whnf-cap-naturality-wall-l2-connecting-square-grouped`
(tally 12, 3 goals) — the highest-tally Lean-friction finding — by giving its *broad* distillations a
home the loop actually reads, without eroding the lab notebook.

## Why a doc, and why gated
The knowledge in that finding is real and recurring, but it must not go anywhere universally
injected: **goal mode runs Lean *and* non-Lean development** (with and without lab notebooks), so a
CLAUDE.md-top or context-bootstrap line would tax every non-Lean goal. It also must not duplicate the
upstream `lean4` skill — which already carries generic *Common Fixes / Type Class Patterns /
Automation Tactics / Troubleshooting* (checked: `skills/lean4/SKILL.md`, 318 lines) but **nothing** on
the project-specific whnf/RingQuot/seam material. So the doc is *additive*, and its injection matches
the existing best-practice-log pattern: **a pointer from the `goal-dev` skill to the file path**, read
only when a Lean dev stretch begins.

## Two hard scoping guards (operator, 2026-07-04)
1. **Broad-only — no over-specified minutia.** Only patterns general enough for *any* Lean dev in this
   project qualify. It is a phrasebook of reusable moves, not a proof log.
2. **Do not erode the lab notebook.** Anything roadmap/phase/wave-specific stays at **notebook**
   level. The doc and the notebook are different tiers: doc = "how to fight this *class* of Lean
   friction anywhere"; notebook = "the state of *this* proof / *this* keystone."

Worked split for the seeding finding:
- **Migrates to the doc (broad):** whnf-heavy definition → keep terms in boundary/Prop-membership form
  at statement level; prefer `erw`/`rw` over `exact`/`apply` on whnf-heavy goals; isolate sub-steps as
  lemmas with **maximally explicit signatures** (explicit variables, homeos as term args, not
  anonymous structs) so a plain `rw` fires without a whnf wall; term-mode `congrArg` to sidestep defeq
  `rw`. Plus the already-in-CLAUDE.md RingQuot rule (`rw` fails at `.reducible` → use `erw`) and the
  no-`ring`/`ring_nf`-on-noncommutative rule — consolidated in one place.
- **Stays in the notebook (specific):** the L2 Poincaré-duality connecting-square seam structure,
  `hcross`/`hmatch`/`hb_pair`, `pullbackCochainMap_comp`, the specific over-engineered nested-subspace
  realization — those are 5q.F state, not general patterns.

## Where it lives
- **Doc:** a Lean-gated reference (candidate: `docs/references/lean_patterns.md`, or fold into the
  existing `temporary/working-docs/.../Lean-Development-Optimization.txt` that CLAUDE.md already names
  as "read before every Lean interactive proof session"). One file, curated, small.
- **Pointer:** the `goal-dev` skill gains a line pointing at that path (matching how the other
  best-practice logs are surfaced), so a Lean dev stretch reads it; non-Lean goals never load it.
- **Curation:** future Lean-friction findings that pass the broad-only guard append to it via
  `/debrief` (the same promotion→integrate→close lifecycle); notebook-level specifics never do.

## Sign-off ask
Approve as a tracked build task: **(a)** create the broad Lean-patterns doc seeded with the whnf/
RingQuot/noncomm distillations above (delta over the `lean4` skill), **(b)** add the `goal-dev`
pointer. Acceptance: broad-only, no notebook-function overlap, no non-Lean-goal tax.
