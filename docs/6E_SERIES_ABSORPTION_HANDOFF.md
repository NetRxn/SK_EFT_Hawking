# `6E*` series → D11/D12 absorption — RESUME HANDOFF

**Written 2026-07-30 at end of the 6EE session, for pickup after compaction.**
Read this first; it is the whole state. Nothing here is speculative except where marked.

---

## 1. What is DONE (do not redo)

The `6E*` Lean substrate is complete and frozen. Five phases:

| Phase | Lean family | Status |
|---|---|---|
| 6EA | `Detection/PoissonDiscrimination`, `GaussianThreshold`, `ShotNoise` | COMPLETE 2026-07-28 |
| 6EB | `Detection/FilterFloors`, `NEPAlgebra`, `MatchedFilter` | COMPLETE 2026-07-29 |
| 6EC | `Electrothermal/ETFModel`, `ETFResponsivity`, `BolometricFloors` | COMPLETE 2026-07-29 |
| 6ED | `GrapheneBand/Honeycomb`, `DiracExpansion`, `HaldaneWitness`, `BernalBilayer` | COMPLETE 2026-07-30 |
| 6EE | `Control/RotatingWave`, `BanachAveraging`, `DriveCalibration`, `CompositeReadoutCeilings` | COMPLETE 2026-07-30 |

`Control/` = 191 declarations, 191/191 kernel-pure, zero project axioms, zero
`sorry`/`native_decide`/`maxHeartbeats`. `lake build SKEFTHawking.ExtractDeps` clean at 10,799 jobs
with **zero `Control/` warnings**. `validate.py` **50/50**.

**LEAN IS FROZEN.** Operator decision at close-out. Do not add declarations to `Control/` for
review-driven reasons.

### Review history and why it stopped

Six completed fresh-context adversarial reviews of 6EE: `1/7/6 → 1/3/5 → 0/3/5 → 0/2/5 → 0/2/4 →
0/3/5` (BLOCKER/MAJOR/IMPORTANT). BLOCKERs converged after round 2 and stayed zero. MAJOR/IMPORTANT
stayed **flat** while `Control/` grew 99 → 191 declarations, essentially all review-driven — round
5's headline fix became round 6's MAJOR. A seventh review was terminated by the operator.

**Root cause, established at close-out:** `skeft-qa:adversarial-reviewer` is defined as *"Fresh-context
adversarial review of a **paper draft** before submission. Runs Stage 13."* Five of its seven finding
classes require a paper (citations, parameter drift vs primary sources, cross-paper contradictions,
narrative overclaims, stale counts). Pointed at Lean modules it had no calibration anchor and graded
docstrings/roadmap prose at paper severity. **Do not re-run it against the substrate.** It becomes
the right instrument once D12 has a draft.

No substantive mathematics or physics error was ever found. Every reviewer independently re-derived
`interactionHamiltonian_decomp`, the `2(Ω/ω)·ℓ¹` Bloch–Siegert constant, `rwaGenerator_sq`,
`‖zRotation‖ = 1`, the Kramers Θ-algebra and the ceiling compositions, and confirmed all of them.
`src/core/constants.py` was never touched by this series.

### Durable gate improvement from this session (keep)

`scripts/validate.py`:
- `_DOCSTRING_STRICT_FAMILIES` now includes `SKEFTHawking.Detection.`, `.Electrothermal.`,
  `.Control.`, `.GrapheneBand.` — the whole `6E*` series FAILs on docstring drift instead of
  printing advisories nobody reads.
- `_DOCSTRING_BLOCK_RE` widened from `/-- -/` + `/-! -/` to include plain `/- -/` **module headers**
  — that omission had hidden a load-bearing reference to a nonexistent
  `combined_floor_add_strictly_sharper` for five review rounds.

Caught three real errors immediately on being widened. **842 advisory drift hits remain repo-wide
outside the strict families** — a separate, unscheduled backlog worth a decision.

---

## 2. What is NOT done — the actual remaining work

Per `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`, a Lean-only phase feeding an **undrafted** bundle is
**Stage A.alt + branch D.1**. Notebooks, figures, per-paper drafts and claims-reviews are **NOT
owed** — an earlier read of this session wrongly said they were; that was retracted.

What *is* owed, and is **missing for all five phases**:

| # | Owed | Protocol ref | Status |
|---|---|---|---|
| 1 | `PAPER_DRAFT_MAPPING.md` row per phase | Stage B / Invariant #14 | **ABSENT** — zero rows for 6EA/6EB/6EC/6ED/6EE or D12 |
| 2 | Substantive synthesis in `temporary/working-docs/` | Stage A.alt gate | **ABSENT** — content lives only in `docs/dev-loops/Phase6E*/` lab notebooks, which are **gitignored** (one `git clean -x` from loss) |
| 3 | `docs/ARCHITECTURE_SCOPE.md` updated | Stage A.alt gate | **ABSENT** — zero `6E` mentions; file last modified 2026-06-01, before the series existed |
| 4 | `bundle_source_manifest.py` + `--check bundle_source_freshness` | Stage C | not runnable until #1 |
| 5 | D12 scheduled into a Phase 7X drafting wave | D.1 passive pickup | **D12 appears in NO `Phase7*.md` roadmap** — operator scheduling decision |

**Net effect:** the substrate is verified but **invisible to the publication machinery**. D.1's
"Action: none" is only safe because it assumes a scheduled drafting wave will collect the bundle.
None is scheduled, and no mapping rows exist for `bundle_source_manifest.py` to find.

---

## 3. IN FLIGHT — blocking item #1

An `Explore` agent was dispatched to verify the proposed assignment before rows are written:

- 6EA/6EB/6EC/6EE → **D12** (*Kernel-Verified Detector & Readout Metrology*, authorized 2026-07-27)
- 6ED → **D11** (*Topological Band Theory & Metamaterial Substrate*; `PAPER_STRATEGY.md:184` already
  admits 6ED as D11's fifth thread)

**Suspected collisions it was asked to settle — re-check these if its report is lost:**
1. **D9** claims *"the readout-window envelopes (relaxation decay probability and the
   thermal-population assignment floor…)"* — and 6EE's `CompositeReadoutCeilings` *consumes* exactly
   those (`readoutDecayProb`, `thermalExcitedPop`, `avgAssignmentError_rational_floor` from
   `QuantumNetwork/`). Is the composite-ceiling layer D12's or D9's?
2. **D1** claims graphene Dirac-fluid content from Phase 5w — does that overlap 6ED's graphene *band
   structure*?
3. **D11** thread (i) (Phase 6CA) deferred a concrete lattice Chern witness; 6ED ships a Haldane one.
   Completion or duplicate?
4. **D7** Chern content vs 6ED/6CA.

Also asked for: any `PAPER_DRAFT_MAPPING.md` row that would be **overridden** (that triggers a Stage-B
user-authorization gate), whether D11/D12 are in `_VALID_BUNDLE_TARGETS` yet, and the verbatim Table-1
format with a sourceless `Lift-action: Synthesize` example row.

---

## 4. NEXT ACTIONS, in order

1. **Read the Explore report.** If it finds a collision, the assignment is an operator decision —
   surface it, do not self-resolve.
2. Write Stage B rows for all five phases. Sourceless form per protocol §Stage B variant:
   `| _phase6EA_lean_only | <Title> | Phase 6EA W1–W3 | **D12 §N** | Synthesize |`
   Destinations: D12 ×4 (6EA/6EB/6EC/6EE), D11 ×1 (6ED). **No authorization gate expected** — both
   bundles are already authorized and nothing existing is being overridden (confirm against the
   Explore report).
3. Write the `temporary/working-docs/` synthesis, lifting the load-bearing content out of the
   gitignored notebooks: the per-phase guardrails, the retracted claims, the kernel no-gos, the
   two-layer posture (formula layer verified / device identification cited, never conflated).
4. Update `ARCHITECTURE_SCOPE.md` with the `6E*` physical-detection layer beneath D9's device
   envelopes.
5. Run Stage C: `bundle_source_manifest.py`, then `validate.py --check bundle_source_freshness`.
6. **Operator decision:** schedule D12 into a Phase 7 drafting wave, or record explicitly that it is
   deferred.

---

## 5. Repo state at handoff

HEAD `d42333c4`. Working tree clean except `docs/dev-loops/proposals/prose-bridged-claims-gate.md`
(untracked, authored by a parallel session — **not mine, do not commit**).

Session commits, newest first:
- `d42333c4` 6E* series: fix two 6ED docstring drifts, gate the series strictly
- `ce1d2908` 6EE close-out: qualify COMPLETE against the operator bar
- `ccabb2d2` 6EE sixth-review remediation + drift gate strengthened
- `ec11e6c3` fifth-review remediation · `e953dfb7` fourth · `f4dc0c51` self-caught de-trivialisation
- `a8abae32` third · `49a3bf4f` second · `ec05532b` Inventory sync · `50944c23` first close

Nothing running except the Explore agent above. `/goal` cleared; managed-loop marker removed.

> The roadmap `docs/roadmaps/Phase6EE_Roadmap.md` carries a close-out qualification block at the top
> stating exactly which bar was and was not met. Its five remediation tables are a **review log, not
> verified claims** — three of their rows were found to misdescribe their own fixes. Git history is
> the reliable record.
