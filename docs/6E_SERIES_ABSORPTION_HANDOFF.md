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

**⚠️ RETRACTED CLAIM — read this before acting on the paragraph that used to be here.**

An earlier version of this document said the adversarial reviewer was "the wrong instrument" for a
Lean substrate and instructed the reader **not to re-run it against the substrate**. That was wrong
and is retracted. **Do not dilute the adversarial review process in any way, including against the
Lean substrate.** Operator direction, 2026-07-30.

The findings were real and Lean-internal, and none of them needed a paper to be true:
- R2's BLOCKER: `hSgen` stated on `S` rather than `−i·S`, which by uniqueness of the derivative made
  the propagator bound **uninstantiable at any Schrödinger propagator pair**.
- R3: the "real propagator pair" witness was degenerate (identity drive ⇒ generator zero).
- R5: the replacement witness was *also* degenerate; the bound had zero call sites.
- R6: `Kq` was an exported free binder while three artifacts claimed it discharged; the applied
  bound admitted `d = 0`.

Every one is a defect in the statement architecture, catchable only by reading the Lean. Treating a
flat MAJOR/IMPORTANT count as evidence the instrument was miscalibrated was a rationalisation, and a
convenient one. The honest reading of the six rounds is narrower: **each remediation added surface
that the next round then reviewed** — the fix cadence, not the review, is what failed to converge.
The correct response is to fix findings without inflating the artifact, not to stop reviewing.

Context worth keeping (as context, not as an excuse): `skeft-qa:adversarial-reviewer` is *documented*
as reviewing a paper draft at Stage 13, and five of its seven named finding classes reference paper
artifacts. That means its **severity calibration** on a substrate is unanchored — not that its
findings are invalid. When D12 has a draft, run it on the draft **as well**, not instead.

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

## 2b. CORRECTION to item 5 — D12's gate is MET, not "missing from Phase 7"

An earlier version of this doc said "D12 appears in no Phase 7 roadmap" and treated that as the
blocker. That framing was too narrow, from having read only half of `PAPER_STRATEGY.md`.

The accurate position, from the roster table `PAPER_STRATEGY.md:395-397`: D10, D11 and D12 all carry
the **Ships** value **`(after phase exec)`** rather than a month, with dependencies listed as their
contributing phases. D12's row reads:

> `| 1 | D12 | Detector & readout metrology (…) | PRX-Q/Quantum/PRApplied | ~35pp | (after phase exec) | Phases 6EA/6EB/6EC/6EE; **authorized 2026-07-27**, scaffolding at first-lift |`

**All four contributing phases have now executed.** D11's row likewise lists "+6ED (graphene/Haldane)
2026-07-27", and 6ED is complete. **Both gates are satisfied as of 2026-07-30.**

The §3 *Sequencing* section (Months 0–12, L1 → … → F) predates D6–D12 and never included them —
that is why nothing schedules D12. The newer bundles are gated on phase execution in the §6 roster,
not on calendar position. So the next action is not "add D12 to a Phase 7 wave"; it is **stand up
the bundle at first content-lift per `BUNDLE_LIFT_PROCEDURE.md`**, which is now unblocked.

Also relevant and owed at lift, `PAPER_STRATEGY.md:375`: primary-source WebFetch+verify is standing
policy — "when a numerical magnitude in a Lean constant, paper claim, or registry entry is
registry-anchored or unverified, the primary-source PDF is fetched and the claim verified before
publication-grade prose relies on it." The `6E*` corpus leans on Le Cam/Bhattacharyya, Mills,
Birnbaum–Feller, McCann, Irwin–Hilton and others; **no `CITATION_REGISTRY` entries exist yet.**

And `PAPER_STRATEGY.md:355`: *"Adversarial review continues per bundle… Each bundle gets at least
one full-pass review before submission, with a pre-submission re-invocation pass after any
substantive revision."* This is standing, non-negotiable process.

---

## 3. Explore verdict (COMPLETE) — **NO COLLISION**

All four suspected risks came back clean, each already adjudicated in writing:

1. **D9 vs 6EE composite ceilings** — no collision. `PAPER_STRATEGY.md:196` already draws it: "D9 owns
   the channel/network certification layer and the qubit-level readout-window envelopes; D12 owns the
   physical detection layer beneath them… with D12's ceilings **consuming** D9's relaxation/thermal
   envelopes as cited floors." Corroborated: `papers/D9/bundle_metadata.json` `contributing_phases`
   stops at `6AQ`; `papers/D9/source_manifest.md` contains "readout" zero times. The Lean is
   consumption-only (`CompositeReadoutCeilings.lean:234`: "cites `avgAssignmentError_rational_floor`,
   no re-proof"). **6EE's ceilings are D12's.**
2. **D1 Phase-5w graphene vs 6ED** — distinct. D1 is hydrodynamic/transport (`GrapheneHawking.lean`,
   `GrapheneNoiseFormula.lean`); 6ED is single-particle band structure (`GrapheneBand/`). Disjoint
   Lean, disjoint physics.
3. **6CA QWZ spike vs 6ED Haldane** — completion, not duplicate. The QWZ spike is **KILL/DEFER**
   (`Phase6CA_prime_Roadmap.md:30`); `Phase6ED_Roadmap.md:52` records that Haldane is therefore the
   repo's first concrete Chern frame and the spike should later cite it. Both land in D11 →
   intra-bundle complement.
4. **D7 Chern vs 6ED/6CA** — different object (categorical↔real-space Chern *marker* bridge vs
   Bloch-band Chern number). No overlap.

**No Stage-B authorization gate fires.** `PAPER_DRAFT_MAPPING.md` has **zero** rows for any `6E*`
phase, any of the four Lean directories, or D11/D12 — so nothing is being overridden. D11 and D12
were both already authorized (2026-06-29 / 2026-07-27).

### ⚠️ Operational hazard found by the Explore pass

`_VALID_BUNDLE_TARGETS` (`scripts/sentence_state.py:203-212`) contains **neither D11 nor D12** — it
stops at D10. Four call sites hard-reject unknown targets: `sentence_state.py:337-344`,
`bundle_source_manifest.py:164`, `review_runner.py:84-87`, `bundle_migration.py:116`.

**Writing D11/D12 mapping rows without extending the registry will make `bundle_migration.py` raise.**
The D10 first-lift precedent is the exact recipe — `git show 23e895c3` — touching `sentence_state.py`
(`_VALID_BUNDLE_TARGETS`), `bundle_source_manifest.py` (regen count map), `datastar_bundles.py`
(title/journal/subphase maps), plus `papers/D1x/{bundle_metadata.json, source_manifest.md,
paper_draft.tex, change_log.md, append_log.json, audit_log.jsonl, prior_art_novelty.md}`.
`bundle_migration.py`'s destination regex is already `D(?:1[0-9]|[1-9])` and needs no change.

Note also: **D11 has never had a mapping row either**, despite 2026-06-29 authorization — so its
other sources (6CA/6CB/6CD/6CE) are equally unmapped. This gap is series-wide, not 6E-specific.
And `docs/agents/claims-reviewer-bundle-prompts.md` has **no D11/D12 reviewer anchor** (stops at D10).

### `PAPER_DRAFT_MAPPING.md` Table 1 format (verbatim, line 23)

```
| Existing draft | Working title | Prior target | New destination(s) | Lift action |
|---|---|---|---|---|
```
Bundle-registration template (line 96, the `D8_initial_draft` form) and per-wave D.4 handle template
(line 104, `_phase6AN_W5_lean_only`) are the two shapes to copy. Destinations bolded, joined ` + `.
Column 3 for sourceless rows: a consolidation date, or `(no standalone draft per Phase 6X
research-only scope; D.4 sourceless)`.

**Stale-count drift to fix while in the file:** `PAPER_DRAFT_MAPPING.md:5` still says "17 publication
targets … 8 Tier 1 deep" (strategy is at 21/12), and `:110` totals still say "17 publication targets".

---

## 3b. IN FLIGHT — none

(Explore agent COMPLETE — verdict in §3 above. Original brief retained below for audit.)

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

1. ~~Read the Explore report.~~ **DONE — no collision (§3).** Assignment confirmed:
   6EA/6EB/6EC/6EE → D12, 6ED → D11.
2. **Extend `_VALID_BUNDLE_TARGETS` FIRST** (D11, D12) per the `23e895c3` D10 recipe — before any
   mapping row is written, or `bundle_migration.py` will raise.
3. Write Stage B rows for all five phases. Sourceless form per protocol §Stage B variant:
   `| _phase6EA_lean_only | <Title> | Phase 6EA W1–W3 | **D12 §N** | Synthesize |`
   Destinations: D12 ×4 (6EA/6EB/6EC/6EE), D11 ×1 (6ED). **No authorization gate expected** — both
   bundles are already authorized and nothing existing is being overridden (confirm against the
   Explore report).
4. Write the `temporary/working-docs/` synthesis, lifting the load-bearing content out of the
   gitignored notebooks: the per-phase guardrails, the retracted claims, the kernel no-gos, the
   two-layer posture (formula layer verified / device identification cited, never conflated).
5. Update `ARCHITECTURE_SCOPE.md` with the `6E*` physical-detection layer beneath D9's device
   envelopes.
6. Run Stage C: `bundle_source_manifest.py`, then `validate.py --check bundle_source_freshness`.
7. Add D11/D12 reviewer anchors to `docs/agents/claims-reviewer-bundle-prompts.md` (stops at D10).
8. Fix the two stale-count drifts in `PAPER_DRAFT_MAPPING.md` (:5 and :110 still say 17 targets).
9. **Operator decision:** D12's `(after phase exec)` gate is now MET — stand up `papers/D12/` at
   first content-lift, or record explicitly that it is deferred. Same question for D11.

**Standing constraint:** adversarial review is NOT to be diluted, including against the Lean
substrate (§1 retraction). Per `PAPER_STRATEGY.md:355` each bundle also gets at least one full-pass
Stage-13 review before submission, plus re-invocation after any substantive revision.

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
