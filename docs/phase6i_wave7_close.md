# Phase 6i Wave 7 — Close Report

**Wave:** 6i.7 — Paper Strategy Integration into the Review Process
**Status:** SHIPPED through Stages 1, 7, 12–14 (Track E close — completes Phase 6i)
**Date:** 2026-04-29

## Goal

Wire the Phase 6i Wave 7 paper-bundle architecture (1 flagship + 5 Tier 1 deep + 3 Tier 2 PRL + 2 Tier 3 infrastructure + 2 Tier 4 experimental, per `docs/PAPER_STRATEGY.md`) into the existing review pipeline so every prior-tracks artifact (citation cache, sentence-level provenance, claim clusters, Lean-substance audit, assumption disclosure) operates correctly on bundles. This wave closes Phase 6i Track E and the Phase 6i programme as a whole.

## Method

Six sub-waves, executed in order:

1. **7.1 Bundle-aware schema + migration.** Extended `scripts/sentence_state.py` with three new optional fields on every sentence (`bundle_destination`, `bundle_section_hint`, `lift_action`) plus the corresponding enum constants (`_VALID_BUNDLE_TARGETS`, `_VALID_LIFT_ACTIONS`). Wrote `scripts/bundle_migration.py` which parses `docs/PAPER_DRAFT_MAPPING.md` Table 1 into per-paper bundle assignments and applies them via the canonical sentence-state writer. Wrote `scripts/bundle_clusters.py` which projects per-paper bundle assignments onto claim clusters and emits `papers/cluster_bundle_index.json`.
2. **7.2 Stage 13 reviewer prompt update.** Updated `.claude/plugins/physics-qa/agents/claims-reviewer.md` and `.claude/plugins/physics-qa/agents/figure-reviewer.md` to accept a `bundle_target` argument with per-tier review profile. Wrote `docs/agents/claims-reviewer-bundle-prompts.md` documenting the per-bundle anchor list (load-bearing claims and citations each bundle's Stage-13 review must verify). Wrote `scripts/review_runner.py` orchestrator with `--list-bundles`, `--bundle <target> --prep-brief`, and `--review-doc <path>` modes.
3. **7.3 validate.py --check bundle_consistency.** Added the new check at `scripts/validate.py:check_bundle_consistency` (Phase 6i Wave 7.3). Walks `papers/cluster_bundle_index.json`'s cross-bundle clusters and verifies: exact-match clusters have guaranteed identical content (by `normalized_hash` invariant); normalized-match clusters get flagged for Stage-13 manual numerical-consistency review.
4. **7.4 Per-bundle Stage 13 sweep on existing material.** Wrote `scripts/bundle_readiness.py` which aggregates the existing per-paper `ReviewFinding` nodes (post-supersession-ledger) by bundle and emits per-bundle review documents at `papers/AutomatedReviews/2026-04-29-bundle-stage13/<bundle>.md` plus the N-gate × 13-bundle heatmap at `docs/BUNDLE_READINESS_HEATMAP.md`. Fresh-context Stage-13 LLM sweeps remain user-triggered per memory `feedback_stages_11_13_reflexive.md`.
5. **7.5 Provenance dashboard Bundles tab.** Added a new "Bundles" tab to the Datastar+Flask provenance dashboard at `scripts/provenance_dashboard.py`. Tab partial: `scripts/templates/partials/bundles_tab.html`. Data loader: `scripts/datastar_bundles.py:load_bundles_summary()`. Two new endpoints: `/api/bundles/<bundle>/review` (serve per-bundle review markdown) and `/api/bundles/<bundle>/submission_event` (POST; append-only submission state log at `docs/submission_state.json`).
6. **7.6 CLAUDE.md + WAVE_EXECUTION_PIPELINE.md updates.** Added Tier-2 references section to `CLAUDE.md` (`PAPER_STRATEGY.md`, `PAPER_DRAFT_MAPPING.md`, `claims-reviewer-bundle-prompts.md`); added `BUNDLE_READINESS_HEATMAP.md` to Important Documents. Updated `WAVE_EXECUTION_PIPELINE.md` Stage 1 (bundle-target identification), Stage 13 (bundle-level reviewer profile), and added Pipeline Invariant #14 (bundle-aware paper output).

## Deliverables shipped

| Sub-wave | Artifact | Path | Purpose |
|---|---|---|---|
| 7.1 | Schema additions | `scripts/sentence_state.py` | `bundle_destination` / `bundle_section_hint` / `lift_action` optional fields + `_VALID_BUNDLE_TARGETS` (13 codes) + `_VALID_LIFT_ACTIONS` (6 actions) |
| 7.1 | Migration script | `scripts/bundle_migration.py` | Parses `PAPER_DRAFT_MAPPING.md` Table 1; applies per-paper assignment via canonical sentence-state writer |
| 7.1 | Cluster index builder | `scripts/bundle_clusters.py` | Builds `papers/cluster_bundle_index.json` with per-cluster `cross_bundle: bool` + bundle-distribution metadata |
| 7.1 | Tests | `tests/test_bundle_migration.py` (19) + `tests/test_bundle_clusters.py` (7) | Schema validation + mapping parser correctness + cross-bundle index invariants |
| 7.2 | Per-bundle anchor list | `docs/agents/claims-reviewer-bundle-prompts.md` | Per-bundle Stage-13 anchor enumeration with cross-bundle anchor table |
| 7.2 | Reviewer plugin updates | `.claude/plugins/physics-qa/agents/claims-reviewer.md`, `figure-reviewer.md` | `bundle_target` argument + per-tier review profile |
| 7.2 | Review runner | `scripts/review_runner.py` | Orchestrates per-bundle review via `--list-bundles`, `--bundle X --prep-brief`, `--review-doc PATH` |
| 7.3 | New validate.py check | `scripts/validate.py:check_bundle_consistency` | CHECK 21; walks cross-bundle clusters; exact-match guaranteed-consistent; normalized-match flagged for review |
| 7.3 | Tests | `tests/test_bundle_consistency.py` (6) | Check registration + summary/verdict detail presence + exact-cluster pass invariant |
| 7.4 | Per-bundle readiness aggregator | `scripts/bundle_readiness.py` | Aggregates existing per-paper findings by bundle; emits per-bundle review docs + N-gate × 13-bundle heatmap |
| 7.4 | Per-bundle review docs (13) | `papers/AutomatedReviews/2026-04-29-bundle-stage13/<bundle>.md` | Stage-13 readiness summary per bundle (F, D1–D5, L1–L3, I1–I2, E1–E2) |
| 7.4 | Bundle readiness heatmap | `docs/BUNDLE_READINESS_HEATMAP.md` | Companion to `READINESS_GATES.md` per-paper view |
| 7.5 | Dashboard Bundles tab | `scripts/templates/partials/bundles_tab.html` + `scripts/templates/dashboard.html` (tab nav + dispatch) | Bundles surface in dashboard at `/?tab=bundles` |
| 7.5 | Dashboard data loader | `scripts/datastar_bundles.py` | `load_bundles_summary()` + `append_submission_event()` |
| 7.5 | Dashboard endpoints | `scripts/provenance_dashboard.py` | `/api/bundles/<bundle>/review` + `/api/bundles/<bundle>/submission_event` |
| 7.6 | CLAUDE.md update | `CLAUDE.md` | Tier-2 references + Important Documents added |
| 7.6 | Pipeline doc updates | `docs/WAVE_EXECUTION_PIPELINE.md` | Stage 1 bundle-target identification + Stage 13 bundle-level review profile + Pipeline Invariant #14 |

## Numerics

### Phase 6i Wave 7 deliverable counts

|  | Wave 7 close |
|---|---:|
| New scripts | 5 (`bundle_migration.py`, `bundle_clusters.py`, `review_runner.py`, `bundle_readiness.py`, `datastar_bundles.py`) |
| New validate.py check | 1 (CHECK 21 `bundle_consistency`) |
| New top-level docs | 2 (`agents/claims-reviewer-bundle-prompts.md`, `BUNDLE_READINESS_HEATMAP.md`) |
| Per-bundle review docs | 13 (one per publication target) |
| New dashboard tab | 1 (Bundles) |
| Test files | 3 (`test_bundle_migration.py`, `test_bundle_clusters.py`, `test_bundle_consistency.py`) |
| Tests added | 32 (all PASS) |
| Schema fields added (sentence_state) | 3 (`bundle_destination`, `bundle_section_hint`, `lift_action`) |
| Pipeline invariant added | 1 (#14 — bundle-aware paper output) |

### Bundle assignment coverage

- 39 existing-draft papers fully assigned to bundles via `PAPER_DRAFT_MAPPING.md` (Wave 7.1 fix: corrected `paper27_bh_four_laws` → `paper27_bh_thermodynamics_four_laws` directory mismatch).
- 13 publication targets, each with a non-empty source set (except I2 which is reserved for Phase 5c VerifiedJackknife + Phase 5o lean-tensor-categories — currently 0 source papers in `papers/`).
- 2 cross-bundle clusters identified at Wave 7.1 close (`claim_cluster:exact:d2c6aaa3` and `claim_cluster:exact:ce92f4a9`, both spanning D2/D4/L2 via paper9/paper10/paper11/paper16_wrt_tqft).

### Bundle readiness verdicts (post-supersession aggregation)

| Verdict | Bundles |
|---|---|
| 🟢 GREEN | E2, I1, I2, L1 (4) |
| 🟡 YELLOW | D1, D2, E1, L2 (4) |
| 🔴 RED | D3, D4, D5, F, L3 (5) |

The RED bundles reflect existing per-paper findings retained as `meta.status: open` in graph history (per Phase 6i Wave 6 Pipeline Invariant #13: QI items closed at structural level via Closed Items section may retain individual finding-level open statuses). The Wave 7.4 heatmap surfaces this for user visibility; fresh-context Stage-13 LLM sweeps will incrementally drive these to GREEN as bundles are submission-prepped.

### Pipeline-check states (post-Wave-7)

| Check | State | Notes |
|---|---|---|
| `parameter_provenance` (CHECK 15) | PASS | No regression. |
| `counts_fresh` | PASS | No regression. |
| `citation_primary_sources_present` (CHECK 19) | PASS | No regression. |
| `provenance_doi_in_registry` (CHECK 20) | PASS | No regression. |
| `bundle_consistency` (CHECK 21, NEW) | PASS | 2 cross-bundle clusters; both exact-match; consistency guaranteed by normalized_hash invariant. |

## Decision Gate I.7 (Wave 7)

Per roadmap §"Decision Gate I.7": **at Sub-wave 7.6 close, Phase 6i Wave 7 is CLOSED. The bundle architecture is operational in the review pipeline. Per-bundle Stage-13 readiness is visible in the dashboard. Cross-bundle consistency is enforced by `validate.py`. Future paper-shaped output is bundle-aware by default.**

**Status: PASS.** All six sub-waves shipped:
- 7.1: schema + migration deployed; 26 tests PASS
- 7.2: per-bundle anchor list + reviewer-plugin updates + review runner deployed
- 7.3: `validate.py --check bundle_consistency` registered; 6 tests PASS; check passes against current cluster index
- 7.4: 13 per-bundle review docs + bundle readiness heatmap shipped
- 7.5: dashboard Bundles tab live at `/?tab=bundles`
- 7.6: CLAUDE.md Tier-2 references + WAVE_EXECUTION_PIPELINE.md amendments shipped (Pipeline Invariant #14)

## Phase 6i programme close (final)

**Phase 6i is now FULLY CLOSED across all five tracks (A–E).**

- **Track A (Wave 1):** Primary-Sources Cache Rollout — SHIPPED 2026-04-28
- **Track B (Wave 2):** Parameter Provenance Closure — SHIPPED 2026-04-28
- **Track C (Waves 3+4+5):** Narrative + Cross-Paper + Lean Substance + Assumption Disclosure — SHIPPED 2026-04-29
- **Track D (Wave 6):** Computation Correctness + Production Run Health + Process Wiring Close — SHIPPED 2026-04-29
- **Track E (Wave 7):** Paper Strategy Integration into the Review Process — SHIPPED 2026-04-29 (this report)

All 12 entry-state-or-surfaced QI items closed (8 entry-state + 4 wave-surfaced). All 14 Pipeline Invariants in place. All 5 Phase 6i validate.py checks (parameter_provenance, counts_fresh, citation_primary_sources_present, provenance_doi_in_registry, bundle_consistency) PASS. Bundle architecture operational end-to-end: schema → migration → cluster index → reviewer plugin → consistency check → readiness heatmap → dashboard tab → top-level doc updates.

## Wave 7 residuals queued

None blocking. Future Stage-13 hygiene items (post-Phase-6i):

- **prose_state.json sentence-state population.** Most papers do not yet have populated `prose_state.json` files (only `paper12_polariton` has the lock file present). When the v2 claims-reviewer is run on individual papers, the bundle migration runs idempotently to populate the new schema fields. No Wave 7 work depends on this; the migration is ready for ingestion as sentence-state populates.
- **`scripts/datastar_bundles.py` SSE upgrade (deferred).** The current Bundles-tab data loader is server-rendered (one-shot via `render_template`). A Datastar-style SSE endpoint for live updates (parallel to the existing tabs' SSE pattern) is a natural follow-up but not blocking.
- **Per-bundle fresh-context Stage-13 LLM sweeps.** Per memory `feedback_stages_11_13_reflexive.md`, Stage-13 reviewer re-invocation is user-triggered. The bundle-aware infrastructure is in place; the user can authorize a per-bundle sweep when a bundle is queued for submission.

## Idempotency

Re-running `scripts/bundle_clusters.py` produces identical `papers/cluster_bundle_index.json`. Re-running `scripts/bundle_readiness.py` produces identical per-bundle review docs and heatmap. Re-running `scripts/qi_register.py` produces 0 open QI items (12/12 closed). Re-running `scripts/bundle_migration.py` is idempotent on prose_state.json files (no spurious updates).

## Stage 13 re-invocation policy

Wave 7 introduces 5 new scripts, 3 new docs, 13 new per-bundle review summaries, 1 new dashboard tab, 32 new tests, 1 new validate.py check, and 1 new Pipeline Invariant. Per memory `feedback_stages_11_13_reflexive.md`, Stage 13 reviewer re-invocation on the touched papers is user-triggered. The bundle-aware reviewer profile is now available when the user authorizes a per-bundle sweep.

## Project-wide post-fix state (2026-04-29)

- All 5 Phase 6i validate.py checks PASS
- All 32 new Wave 7 tests PASS
- 12 / 12 QI items closed; 0 open
- 14 Pipeline Invariants in place (Invariant #14 added in Wave 7.6)
- 13 publication bundles operational with per-bundle anchor list, readiness verdict, and dashboard surface
- Bundle architecture wired into Stage 1 (bundle-target identification), Stage 13 (bundle-level reviewer profile), and Stage 14 (QI register flows from per-bundle sweeps the same as per-paper sweeps)

## Phase 6i CLOSED

**Phase 6i (QI Register Closure & Process Hardening) is CLOSED end-to-end as of 2026-04-29.** The hygiene programme that opened on 2026-04-28 with 8 entry-state QI items and a hallucinated-citation incident closes with:

- 12 / 12 QI items closed (8 entry-state + 4 wave-surfaced)
- 4 new validate.py checks (CHECK 19 citation cache, CHECK 20 provenance DOI registry, CHECK 21 bundle consistency, plus `--strict` mode for `parameter_provenance`)
- 4 new Pipeline Invariants (#11 primary-source cache, #12 provenance-DOI registry, #13 QI-register auto-regen + manual-curation, #14 bundle-aware paper output)
- Supersession ledger 13 → 160 entries (147 finding closures across 5 waves)
- 13-bundle paper architecture operational from schema → migration → cluster index → reviewer plugin → validate.py check → readiness heatmap → dashboard tab → top-level docs

**Next: Phase 6c Wave 2 (EWBaryogenesisChiralityWall) is the only remaining outstanding wave in the Phase 6 corpus per memory inspection. Phase 6f.1 (Curvature.lean) remains gated on the upstream Bonn Massot↔Rothgang Levi-Civita branch. All other Phase 6 sub-phases are SHIPPED.**
