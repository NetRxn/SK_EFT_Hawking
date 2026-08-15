# Bundle Readiness Heatmap

**Auto-generated:** 2026-08-15
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
| **F** | 0 | 63 | 104 | 0 | 72 advisory, 32 minor | 2026-06-10 | 🟡 YELLOW |
| **D1** | 1 | 12 | 23 | 0 | 8 advisory, 15 minor | 2026-06-10 | 🟡 YELLOW |
| **D2** | 1 | 6 | 43 | 0 | 23 advisory, 20 minor | 2026-06-10 | 🟡 YELLOW |
| **D3** | 1 | 31 | 59 | 0 | 43 advisory, 16 minor | 2026-06-10 | 🟡 YELLOW |
| **D4** | 1 | 12 | 34 | 0 | 33 advisory, 1 minor | 2026-06-10 | 🟡 YELLOW |
| **D5** | 1 | 9 | 46 | 0 | 35 advisory, 11 minor | 2026-06-10 | 🟡 YELLOW |
| **D6** | 1 | 3 | 0 | 0 | _(none)_ | 2026-06-10 † | 🟡 YELLOW (P1 gate blocked: NarrativeGrounding) |
| **D7** | 1 | 1 | 5 | 0 | 5 minor | 2026-06-10 | ⚪ UNMEASURED (Stage-13 evidence kind=unrecorded; only full-adversarial earns GREEN) |
| **D8** | 1 | 13 | 14 | 0 | 8 advisory, 6 minor | 2026-06-10 | 🟡 YELLOW |
| **D9** | 1 | 1 | 0 | 0 | _(none)_ | 2026-06-10 | ⚪ UNMEASURED (Stage-13 evidence kind=unrecorded; only full-adversarial earns GREEN) |
| **D10** | 1 | 4 | 3 | 0 | 1 advisory, 2 minor | 2026-06-30 | 🟡 YELLOW (P1 gate blocked: LeanProofSubstance, NarrativeGrounding) |
| **D11** | 1 | 6 | 63 | 0 | 18 advisory, 45 minor | 2026-07-31 † | 🟡 YELLOW |
| **D12** | 1 | 5 | 107 | 5 | 7 advisory, 5 major, 95 minor | 2026-07-31 † | 🔴 RED |
| **L1** | 2 | 2 | 7 | 1 | 1 major, 6 minor | 2026-08-14 | 🔴 RED |
| **L2** | 2 | 1 | 27 | 0 | 24 advisory, 3 minor | 2026-06-10 | 🟡 YELLOW |
| **L3** | 2 | 4 | 18 | 0 | 15 advisory, 3 minor | 2026-06-10 | 🟡 YELLOW |
| **I1** | 3 | 8 | 37 | 0 | 14 advisory, 23 minor | 2026-08-12 | 🟡 YELLOW |
| **I2** | 3 | 1 | 42 | 0 | 37 advisory, 5 minor | 2026-06-10 | 🟡 YELLOW |
| **I3** | 3 | 1 | 20 | 0 | 16 advisory, 4 minor | 2026-06-10 | 🟡 YELLOW |
| **E1** | 4 | 5 | 7 | 0 | 7 minor | 2026-06-10 | 🟡 YELLOW |
| **E2** | 4 | 4 | 22 | 0 | 15 advisory, 7 minor | 2026-06-10 | 🟡 YELLOW |

† review date backfilled from on-disk review evidence; the evidence path is recorded in the bundle's `bundle_metadata.json` `last_stage13_review_source` field.

### Per-bundle caveats

- **D10** — ⚠️ **a NEWER review sits on disk and is not recorded.** The column above shows the recorded date; `papers/AutomatedReviews/2026-07-01-0240-internal-adversarial/D10.md` is dated 2026-07-01 (kind not declared). The recorded value wins here by design, so this review is invisible to every consumer of that column until it is written through `scripts/record_review.py`. Not auto-adopted: a review's verdict is a judgement the writer exists to capture, and silently promoting a date would swap one unverified record for another.
- **D11** — ⚠️ **a NEWER review sits on disk and is not recorded.** The column above shows the recorded date; `papers/AutomatedReviews/2026-08-01-0142-internal-adversarial/D11.md` is dated 2026-08-01 (kind not declared). The recorded value wins here by design, so this review is invisible to every consumer of that column until it is written through `scripts/record_review.py`. Not auto-adopted: a review's verdict is a judgement the writer exists to capture, and silently promoting a date would swap one unverified record for another.
- **D12** — non-enum `stage13_status` in `papers/D12/bundle_metadata.json` (surfaced verbatim): "pending-redo"

## Gate × Bundle distribution (open findings)

| Bundle | AssumptionDisclosu | CitationIntegrity | ComputationCorrect | CountFreshness | CrossPaperConsiste | FixPropagation | LeanProofSubstance | NarrativeGrounding | ParameterProvenanc | ProductionRunHealt | unclassified |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **F** | 7 | 11 | 9 | 7 | 10 | 0 | 5 | 2 | 15 | 1 | 37 |
| **D1** | 0 | 6 | 0 | 0 | 5 | 0 | 2 | 1 | 2 | 0 | 7 |
| **D2** | 10 | 10 | 3 | 3 | 5 | 0 | 1 | 3 | 2 | 0 | 6 |
| **D3** | 4 | 7 | 6 | 5 | 3 | 0 | 2 | 1 | 8 | 1 | 22 |
| **D4** | 3 | 2 | 1 | 0 | 4 | 1 | 2 | 1 | 2 | 0 | 18 |
| **D5** | 3 | 8 | 2 | 2 | 5 | 0 | 2 | 2 | 5 | 0 | 17 |
| **D6** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **D7** | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 0 | 1 |
| **D8** | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | 4 |
| **D9** | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **D10** | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 |
| **D11** | 5 | 14 | 2 | 9 | 4 | 0 | 1 | 0 | 13 | 0 | 15 |
| **D12** | 20 | 12 | 7 | 6 | 0 | 0 | 0 | 18 | 23 | 0 | 21 |
| **L1** | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 | 2 | 0 | 3 |
| **L2** | 3 | 3 | 3 | 2 | 4 | 0 | 2 | 0 | 7 | 0 | 3 |
| **L3** | 1 | 6 | 0 | 2 | 2 | 0 | 0 | 0 | 0 | 1 | 6 |
| **I1** | 3 | 7 | 2 | 0 | 0 | 0 | 0 | 10 | 4 | 0 | 11 |
| **I2** | 1 | 6 | 2 | 3 | 1 | 0 | 4 | 6 | 5 | 0 | 14 |
| **I3** | 1 | 0 | 0 | 0 | 5 | 0 | 2 | 3 | 4 | 0 | 5 |
| **E1** | 0 | 2 | 0 | 1 | 0 | 0 | 0 | 2 | 1 | 0 | 1 |
| **E2** | 1 | 6 | 0 | 0 | 2 | 0 | 1 | 5 | 3 | 0 | 4 |

## Notes

- This heatmap aggregates *existing* per-paper Stage-13 review findings via `build_graph.extract_review_finding_nodes()` (post-supersession). It does NOT include findings from a fresh-context Stage-13 sweep on the bundle — that sweep is a reflexive pipeline stage this script does not run, NOT a user-gated one — and since 2026-06-10 the GREEN verdict additionally REQUIRES that such a sweep is recorded for the bundle (S5 closure).
- 'Open' means `meta.status == 'open'` after applying `docs/review_finding_supersessions.json` overrides.
- 'Blockers' = findings with severity `critical` or `major`. RED bundles must close blockers before promoting to a fresh-context Stage-13 LLM review.
- **Staleness footnote:** the Stage-13 review column surfaces review dates so staleness is visible, but this heatmap does NOT compare edit dates against review dates. Re-review obligations after substantive edits are governed by Stage-13's re-invocation rule (`docs/WAVE_EXECUTION_PIPELINE.md` Stage 13: findings marked fixed must pass a re-invocation — "the re-run is evidence") and, for late absorptions into already-drafted bundles, the Stage-F re-review mandate (`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`). A re-review sweep is separately scheduled.
- Cross-bundle consistency between bundle siblings is verified by `validate.py --check bundle_consistency` (Wave 7.3); see `papers/cluster_bundle_index.json` for the cross-bundle cluster registry.

---

*Generated by `scripts/bundle_readiness.py` (Phase 6i Wave 7.4; S5-closure semantics 2026-06-10).*