# Bundle Readiness Heatmap

**Auto-generated:** 2026-07-31
**Tool:** `scripts/bundle_readiness.py --heatmap`

**Companion to:** `docs/READINESS_GATES.md` (per-paper) — the per-bundle analog. Phase 6i Wave 7.4 deliverable; GREEN semantics tightened 2026-06-10 (S5 closure — see legend).

## Verdict legend

- 🟢 **GREEN** — 0 blockers, ≤5 open advisories, **and** a fresh-context Stage-13 review is RECORDED for the bundle
- 🟡 **YELLOW (unreviewed)** — 0 blockers, but **no recorded fresh-context full-bundle Stage-13 review**. "No findings recorded" ≠ "reviewed and passed" (S5 closure, 2026-06-10, from the 2026-06-05 external review)
- 🟡 **YELLOW** — 0 blockers, reviewed, >5 open advisories
- 🔴 **RED** — ≥1 blocker (critical / major severity)

**Review-recordedness resolution order:** (a) `papers/<X>/bundle_metadata.json` `last_stage13_review` (non-null); (b) else the newest dated genuine fresh-context review document on disk (`papers/AutomatedReviews/<dated>-{bundle-stage13,internal-adversarial}/<X>*.md`, excluding this script's own aggregation summaries and stage-9/10 artifacts, or `docs/audits/stage13_<X>_fullbundle_<date>.md`), backfilled into the metadata with a `last_stage13_review_source` audit note (evidence-based only — never fabricated); (c) else unreviewed.

**Section-level rule:** a section-/phase-scoped Stage-13 audit (e.g. `docs/audits/stage13_phase6AA_*.md`) is NOT a full-bundle fresh review and does not satisfy the recordedness requirement; a bundle with only section-level evidence renders 🟡 YELLOW (unreviewed) with a "§-level only" marker in the Stage-13 review column.

## Bundle summary

| Bundle | Tier | Sources | Open | Blockers | Severity mix | Stage-13 review | Verdict |
|---|---:|---:|---:|---:|---|:---:|:---:|
| **F** | 0 | 63 | 22 | 10 | 5 critical, 5 major, 12 minor | 2026-06-10 | 🔴 RED |
| **D1** | 1 | 12 | 50 | 36 | 1 advisory, 24 critical, 12 major, 13 minor | 2026-06-10 | 🔴 RED |
| **D2** | 1 | 6 | 33 | 16 | 7 critical, 9 major, 17 minor | 2026-06-10 | 🔴 RED |
| **D3** | 1 | 31 | 11 | 3 | 2 advisory, 3 major, 6 minor | 2026-06-10 | 🔴 RED |
| **D4** | 1 | 12 | 0 | 0 | _(none)_ | 2026-06-10 | 🟢 GREEN |
| **D5** | 1 | 9 | 20 | 11 | 3 advisory, 5 critical, 6 major, 6 minor | 2026-06-10 | 🔴 RED |
| **D6** | 1 | 3 | 0 | 0 | _(none)_ | 2026-06-10 † | 🟡 YELLOW (P1 gate blocked: NarrativeGrounding) |
| **D7** | 1 | 1 | 16 | 12 | 8 critical, 4 major, 4 minor | 2026-06-10 | 🔴 RED |
| **D8** | 1 | 13 | 8 | 0 | 2 advisory, 6 minor | 2026-06-10 | 🟡 YELLOW |
| **D9** | 1 | 1 | 0 | 0 | _(none)_ | 2026-06-10 | 🟢 GREEN |
| **D10** | 1 | 1 | 3 | 0 | 1 advisory, 2 minor | 2026-06-30 | 🟡 YELLOW (P1 gate blocked: NarrativeGrounding) |
| **D11** | 1 | 1 | 31 | 14 | 5 advisory, 1 critical, 13 major, 12 minor | 2026-07-31 † | 🔴 RED |
| **D12** | 1 | 1 | 28 | 9 | 2 advisory, 1 critical, 8 major, 17 minor | 2026-07-31 † | 🔴 RED |
| **L1** | 2 | 2 | 1 | 1 | 1 major | 2026-06-10 | 🔴 RED |
| **L2** | 2 | 1 | 20 | 14 | 3 advisory, 8 critical, 6 major, 3 minor | 2026-06-10 | 🔴 RED |
| **L3** | 2 | 4 | 8 | 5 | 1 critical, 4 major, 3 minor | 2026-06-10 | 🔴 RED |
| **I1** | 3 | 8 | 31 | 15 | 5 advisory, 2 critical, 13 major, 11 minor | 2026-06-10 | 🔴 RED |
| **I2** | 3 | 1 | 31 | 19 | 7 advisory, 8 critical, 11 major, 5 minor | 2026-06-10 | 🔴 RED |
| **I3** | 3 | 1 | 23 | 16 | 3 advisory, 9 critical, 7 major, 4 minor | 2026-06-10 | 🔴 RED |
| **E1** | 4 | 5 | 6 | 5 | 1 critical, 4 major, 1 minor | 2026-06-10 | 🔴 RED |
| **E2** | 4 | 4 | 10 | 0 | 4 advisory, 6 minor | 2026-06-10 | 🟡 YELLOW |

† review date backfilled from on-disk review evidence; the evidence path is recorded in the bundle's `bundle_metadata.json` `last_stage13_review_source` field.

## Gate × Bundle distribution (open findings)

| Bundle | AssumptionDisclosu | CitationIntegrity | ComputationCorrect | CountFreshness | CrossPaperConsiste | LeanProofSubstance | NarrativeGrounding | ParameterProvenanc | unclassified |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **F** | 2 | 4 | 0 | 1 | 4 | 3 | 2 | 3 | 3 |
| **D1** | 1 | 21 | 2 | 2 | 8 | 3 | 6 | 3 | 4 |
| **D2** | 3 | 13 | 2 | 2 | 4 | 1 | 3 | 1 | 4 |
| **D3** | 4 | 2 | 0 | 0 | 1 | 0 | 1 | 1 | 2 |
| **D4** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **D5** | 0 | 8 | 0 | 2 | 2 | 1 | 3 | 2 | 2 |
| **D6** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **D7** | 2 | 1 | 0 | 1 | 2 | 1 | 2 | 2 | 5 |
| **D8** | 2 | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 2 |
| **D9** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **D10** | 0 | 2 | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| **D11** | 2 | 6 | 2 | 2 | 3 | 0 | 5 | 3 | 8 |
| **D12** | 3 | 5 | 4 | 0 | 0 | 0 | 5 | 7 | 4 |
| **L1** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 |
| **L2** | 3 | 3 | 1 | 0 | 3 | 2 | 1 | 4 | 3 |
| **L3** | 1 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | 1 |
| **I1** | 3 | 9 | 0 | 2 | 0 | 0 | 11 | 2 | 4 |
| **I2** | 1 | 2 | 1 | 0 | 1 | 4 | 8 | 6 | 8 |
| **I3** | 2 | 2 | 0 | 2 | 2 | 2 | 5 | 4 | 4 |
| **E1** | 1 | 2 | 0 | 1 | 0 | 0 | 1 | 1 | 0 |
| **E2** | 1 | 6 | 0 | 0 | 0 | 0 | 2 | 1 | 0 |

## Notes

- This heatmap aggregates *existing* per-paper Stage-13 review findings via `build_graph.extract_review_finding_nodes()` (post-supersession). It does NOT include findings from a fresh-context Stage-13 sweep on the bundle (those are user-triggered) — but since 2026-06-10 the GREEN verdict additionally REQUIRES that such a sweep is recorded for the bundle (S5 closure).
- 'Open' means `meta.status == 'open'` after applying `docs/review_finding_supersessions.json` overrides.
- 'Blockers' = findings with severity `critical` or `major`. RED bundles must close blockers before promoting to a fresh-context Stage-13 LLM review.
- **Staleness footnote:** the Stage-13 review column surfaces review dates so staleness is visible, but this heatmap does NOT compare edit dates against review dates. Re-review obligations after substantive edits are governed by Stage-13's re-invocation rule (`docs/WAVE_EXECUTION_PIPELINE.md` Stage 13: findings marked fixed must pass a re-invocation — "the re-run is evidence") and, for late absorptions into already-drafted bundles, the Stage-F re-review mandate (`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`). A re-review sweep is separately scheduled.
- Cross-bundle consistency between bundle siblings is verified by `validate.py --check bundle_consistency` (Wave 7.3); see `papers/cluster_bundle_index.json` for the cross-bundle cluster registry.

---

*Generated by `scripts/bundle_readiness.py` (Phase 6i Wave 7.4; S5-closure semantics 2026-06-10).*