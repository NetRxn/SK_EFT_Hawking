# Bundle Readiness Heatmap

**Auto-generated:** 2026-06-10
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
| **F** | 0 | 59 | 6 | 5 | 3 critical, 2 major, 1 minor | 2026-05-11 | 🔴 RED |
| **D1** | 1 | 12 | 0 | 0 | _(none)_ | 2026-05-07 | 🟢 GREEN |
| **D2** | 1 | 6 | 6 | 5 | 3 critical, 2 major, 1 minor | 2026-05-06 | 🔴 RED |
| **D3** | 1 | 31 | 0 | 0 | _(none)_ | 2026-05-06 | 🟢 GREEN |
| **D4** | 1 | 12 | 0 | 0 | _(none)_ | 2026-05-23 | 🟢 GREEN |
| **D5** | 1 | 9 | 0 | 0 | _(none)_ | 2026-05-07 | 🟢 GREEN |
| **D6** | 1 | 3 | 0 | 0 | _(none)_ | 2026-06-01 † | 🟢 GREEN |
| **D7** | 1 | 1 | 0 | 0 | _(none)_ | 2026-05-26 | 🟢 GREEN |
| **D8** | 1 | 9 | 0 | 0 | _(none)_ | 2026-05-31 | 🟢 GREEN |
| **L1** | 2 | 2 | 0 | 0 | _(none)_ | 2026-05-07 | 🟢 GREEN |
| **L2** | 2 | 1 | 6 | 5 | 3 critical, 2 major, 1 minor | 2026-05-06 | 🔴 RED |
| **L3** | 2 | 4 | 0 | 0 | _(none)_ | 2026-05-06 | 🟢 GREEN |
| **I1** | 3 | 8 | 0 | 0 | _(none)_ | 2026-05-06 | 🟢 GREEN |
| **I2** | 3 | 1 | 0 | 0 | _(none)_ | 2026-05-11 | 🟢 GREEN |
| **I3** | 3 | 1 | 0 | 0 | _(none)_ | 2026-05-11 | 🟢 GREEN |
| **E1** | 4 | 5 | 0 | 0 | _(none)_ | 2026-05-07 | 🟢 GREEN |
| **E2** | 4 | 4 | 0 | 0 | _(none)_ | 2026-05-07 | 🟢 GREEN |

† review date backfilled from on-disk review evidence; the evidence path is recorded in the bundle's `bundle_metadata.json` `last_stage13_review_source` field.

### Per-bundle caveats

- **D6** — non-enum `stage13_status` in `papers/D6/bundle_metadata.json` (surfaced verbatim): "green_phase6AA_section (full-bundle Stage-13 still pending Phase-6v close)"

## Gate × Bundle distribution (open findings)

| Bundle | AssumptionDisclosu | ComputationCorrect | CountFreshness | CrossPaperConsiste |
|---|---:|---:|---:|---:|
| **F** | 1 | 2 | 1 | 2 |
| **D1** | 0 | 0 | 0 | 0 |
| **D2** | 1 | 2 | 1 | 2 |
| **D3** | 0 | 0 | 0 | 0 |
| **D4** | 0 | 0 | 0 | 0 |
| **D5** | 0 | 0 | 0 | 0 |
| **D6** | 0 | 0 | 0 | 0 |
| **D7** | 0 | 0 | 0 | 0 |
| **D8** | 0 | 0 | 0 | 0 |
| **L1** | 0 | 0 | 0 | 0 |
| **L2** | 1 | 2 | 1 | 2 |
| **L3** | 0 | 0 | 0 | 0 |
| **I1** | 0 | 0 | 0 | 0 |
| **I2** | 0 | 0 | 0 | 0 |
| **I3** | 0 | 0 | 0 | 0 |
| **E1** | 0 | 0 | 0 | 0 |
| **E2** | 0 | 0 | 0 | 0 |

## Notes

- This heatmap aggregates *existing* per-paper Stage-13 review findings via `build_graph.extract_review_finding_nodes()` (post-supersession). It does NOT include findings from a fresh-context Stage-13 sweep on the bundle (those are user-triggered) — but since 2026-06-10 the GREEN verdict additionally REQUIRES that such a sweep is recorded for the bundle (S5 closure).
- 'Open' means `meta.status == 'open'` after applying `docs/review_finding_supersessions.json` overrides.
- 'Blockers' = findings with severity `critical` or `major`. RED bundles must close blockers before promoting to a fresh-context Stage-13 LLM review.
- **Staleness footnote:** the Stage-13 review column surfaces review dates so staleness is visible, but this heatmap does NOT compare edit dates against review dates. Re-review obligations after substantive edits are governed by Stage-13's re-invocation rule (`docs/WAVE_EXECUTION_PIPELINE.md` Stage 13: findings marked fixed must pass a re-invocation — "the re-run is evidence") and, for late absorptions into already-drafted bundles, the Stage-F re-review mandate (`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`). A re-review sweep is separately scheduled.
- Cross-bundle consistency between bundle siblings is verified by `validate.py --check bundle_consistency` (Wave 7.3); see `papers/cluster_bundle_index.json` for the cross-bundle cluster registry.

---

*Generated by `scripts/bundle_readiness.py` (Phase 6i Wave 7.4; S5-closure semantics 2026-06-10).*