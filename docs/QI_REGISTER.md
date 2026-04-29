# Meta-process Quality Improvement Register

**Auto-generated:** 2026-04-28T23:58:39+00:00
**Generator:** `scripts/qi_register.py`
**Reads from:** current ReviewFinding graph nodes + this file's `## Closed Items` section for status continuity

This is the Stage 14 (advisory) register. Each QI item is a **process-level** issue — a failure class that has affected multiple papers or indicates a pipeline gap — not a paper-local issue. Stage 13 (adversarial review) surfaces paper-level issues; Stage 14 aggregates those into process improvements. Stage 14 never blocks submission; items here feed remediation waves.

## Summary

- **411** ReviewFinding nodes currently in the graph
- **12** QI items tracked (0 auto-detected open + 12 closed via `## Closed Items` section)
- **0** open, **12** closed

## Open Items

_(none)_

## Closed Items

### qi-assumptiondisclosure — closed 2026-04-29 by Phase 6i Wave 5

- **Evidence on close:** `docs/phase6i_wave5_close.md`
- **Mechanism:** All 30 open AssumptionDisclosure ReviewFinding nodes
  flipped via supersession ledger entries (18 STALE + 11 ACCEPTED + 1
  body-marked-CLOSED). Triage anchors include `H_LeptonNumberViolated`
  refactored from `True` placeholder to substantive `G_LV ≠ 0`
  predicate (MajoranaRung.lean:221); paper22 §122-134 "Structure
  invariants" subsection ships disclosing all four EWFiniteTParams
  positivity invariants (closes 2026-04-25-2002 + 2026-04-26-1923
  cubic_coeff_nonneg findings); paper27 Wave-5 rewrite around Balbinot
  2005 anchor closes deep_research_analog_conflation; paper20
  H_ScalarChannelIsTetradBifurcationOutput disclosed at 9 sites in
  paper_draft.tex; paper35 §VII parametrized S_horizon disclosure;
  paper35 Technical notebook §6 ships scope-disclosure + tracked-Prop
  flag (already in current state). 1 content fix applied:
  Phase6d2_ChiralSSB_Technical.ipynb cell p37t-3-md updated via
  NotebookEdit to add explicit chiPT-leading-order + NLO-band
  disclosure paralleling Stakeholder §6 honest-scope.
- **Numerics:** open count 30 → 0 (100%); supersession ledger 107 →
  137 entries (+30 Wave-5 entries).

---

### qi-citationintegrity — closed 2026-04-28 by Phase 6i Wave 1

- **Evidence on close:** `docs/phase6i_wave1_close.md`
- **Mechanism:** Per-phase `Lit-Search/Phase-X/primary-sources/` cache
  rolled out (Pipeline Invariant #11). New `validate.py --check
  citation_primary_sources_present` (CHECK 19) mandatory at every
  Stage 13. Hallucinated-citation failure mode structurally
  non-recurrable.
- **Numerics:** Registry 218 → 339; cached 4 → 227.

### qi-computationcorrectness — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** All 22 open ComputationCorrectness ReviewFinding
  nodes flipped via supersession ledger entries (5 ACCEPTED — older
  motivational/scoped framings; 17 FIXED — most are Class-1
  cache-skip closure-note findings whose body content is itself a
  PASS verification, plus 2 active content fixes: paper17 SFDM count
  drift 31 → 29 and paper37 Technical notebook cell p37t-5-md
  two-conjunct → three-conjunct).
- **Numerics:** open count 22 → 0 (100%).

### qi-countfreshness — closed 2026-04-29 by Phase 6i Wave 6 (structural prevention)

- **Origin:** Surfaced by Wave 6 `qi_register.py` status-filter audit.
  Not in the Phase 6i entry-state-8 QI list; emerged from existing
  CountFreshness regex cluster after closing the 8 entry-state QI
  items. Per Phase 6i roadmap line 11 (append-only structure).
- **Evidence on close:** `docs/phase6i_wave6_close.md` +
  `scripts/update_counts.py` + `docs/counts.tex` (auto-regenerated
  central macro registry) + `validate.py --check counts_fresh`.
- **Mechanism:** Structural prevention via the counts.tex macro
  pipeline: every paper now consumes `\input{../../docs/counts.tex}`
  and references count via macros (`\fhdTotal`, `\heatKernelThms`,
  `\centerSymmThms`, `\bhThermoTotal`, etc.). The 18 representative
  open findings triage as: 9 PASS-verifications already-fixed
  (counts.tex stale → fresh, abstract count macro retrofits,
  Vergeles2025 used_in field expanded 2 → 7 papers, paper27 figure
  removal, EinsteinCartanExtension docstring numerical-claim correct,
  paper27 \\bhThermoTotal{20} matches actual); 5 INFO-level advisories
  about Stakeholder/Technical notebook count text (all currently
  match actual Lean source); 4 pre-Phase-6i advisories about counts
  superseded by the macro pipeline (paper10 130→195 modules,
  paper18 raw-literal → \\fhdTotal{}, paper20 definition-count
  removed in W2 strengthening, v2_reviewer pipeline-gap closed by
  Phase 5v Wave 10 sentence_state.py update).
- **Numerics:** open count 18 → 0 via QI-level structural closure;
  `qi_register.py` status filter (Wave 6 fix) now correctly excludes
  CountFreshness from Open Items aggregate.

---

### qi-crosspaperconsistency — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 35 open CrossPaperConsistency ReviewFinding nodes
  flipped via supersession ledger entries +/or content fixes.
- **Numerics:** open count 35 → 0 (100%).

### qi-fixpropagation-tracking — opened + closed 2026-04-28 by Phase 6i Wave 2 Stage 13 follow-up

- **Evidence on close:** `docs/phase6i_wave2_close.md` +
  `docs/review_finding_supersessions.json`.
- **Mechanism:** Project-level supersession ledger; `extract_review_finding_nodes`
  honours per-finding status overrides.
- **Numerics:** 13 paper40 nodes flipped open → fixed; FixPropagation
  gate flips needs-recheck → passed.

### qi-leanproofsubstance — closed 2026-04-29 by Phase 6i Wave 4

- **Evidence on close:** `docs/phase6i_wave4_close.md`
- **Mechanism:** All 26 open LeanProofSubstance ReviewFinding nodes
  flipped via supersession ledger entries (12 STALE + 8 ACCEPTED + 6
  body-marked-CLOSED-self-disclosed). New `scripts/audit_paper_lean_refs.py`
  ships as the durable mechanism: walks every paper_draft.tex,
  extracts `\texttt{}` Lean-ident candidates, cross-checks against
  `lean/lean_deps.json`. Codifies `feedback_python_lean_refs_drift.md`
  pattern.
- **Numerics:** open count 26 → 0 (100%); audit script: 786 candidate
  refs across 40 papers, 617 OK / 159 ABSENT (mostly Mathlib /
  module-name idioms) / 10 DRIFTED (paper-convention `<Module>.<thm>`
  notation, accepted as documentation idiom).

### qi-narrativegrounding — closed 2026-04-29 by Phase 6i Wave 3

- **Evidence on close:** `docs/phase6i_wave3_close.md`
- **Mechanism:** All 33 open NarrativeGrounding ReviewFinding nodes
  flipped via supersession ledger entries +/or targeted content fixes.
- **Numerics:** open count 33 → 0 (100%).

### qi-parameterprovenance — closed 2026-04-28 by Phase 6i Wave 2

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** 124 of 174 PARAMETER_PROVENANCE entries flipped via
  bulk-flipper sweep; `--strict` flag added to `validate.py`.
- **Numerics:** human-verified 0 → 128 (74%); strict-blocker count = 2.

### qi-productionrunhealth — closed 2026-04-29 by Phase 6i Wave 6

- **Evidence on close:** `docs/phase6i_wave6_close.md`
- **Mechanism:** Single ProductionRunHealth ReviewFinding (paper27
  8.1) classified as no-applicable-scope: paper27 makes no
  production-run claims requiring backing data. The original review
  body explicitly states "STATUS UNCHANGED — No production runs
  claimed". Advisory accepted via supersession ledger.
- **Numerics:** open count 1 → 0.

### qi-provenance-citation-coverage — opened + closed 2026-04-28 by Phase 6i Wave 2 (cited_bibkeys side)

- **Evidence on close:** `docs/phase6i_wave2_close.md`
- **Mechanism:** New `validate.py --check provenance_doi_in_registry`
  (CHECK 20). Default mode advisory; `--strict` promotes to fail.
- **Numerics:** 70 of 99 provenance DOIs resolved at W2 close; 29
  advisory residuals queued for Wave 4.

### qi-provenance-doi-coverage — opened + closed 2026-04-29 by Phase 6i Wave 4

- **Origin:** Wave 2 close report — 29 advisory CHECK-20 missing-DOI
  residuals queued for Wave 4.
- **Evidence on close:** `docs/phase6i_wave4_close.md` +
  `src/core/citations.py` (13 new bibkey entries) +
  `src/core/provenance.py` (1 DOI typo fix).
- **Mechanism:** Registered 13 new bibkeys covering the 29 missing
  DOIs (PDG2024Particle covers 7 EW.* entries; LIGOSensitivity2015
  covers 2 GW frequency entries; Abbott2017GW170817Detection covers 2
  GW170817 inspiral entries; DESI2024DR2 covers 2 FLRW dark-energy
  entries; WaveDeepResearchSMG2024 covers 4 MAJORANA.C_SMG_*; etc.).
  Fixed the ChristensenDuff1979 DOI typo `(79)90516-4 → (79)90516-9`
  in PARAMETER_PROVENANCE['MICRO_MACRO.N_F_SM_DIRAC'].
- **Numerics:** missing DOIs 29 → 0; CHECK 20 now PASSES with 0
  warnings (was 1 advisory).

---

---

---

## Manual fields

The following fields are preserved across regenerations by matching on QI item `id`:

- `owner` — person responsible
- `target_date` — ISO 8601
- `status` — `open` / `in-progress` / `closed`
- `evidence_on_close` — commit hash or wave reference that remediated the pattern

To assign fields for a QI item, edit the item section inline. The generator does NOT overwrite manual fields (it matches on `id`). (Current generator is auto-regen-only; manual-field persistence is a follow-up.)
