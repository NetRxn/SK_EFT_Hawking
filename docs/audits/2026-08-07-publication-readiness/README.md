# Publication-readiness audit — 2026-08-07

**Scope.** The state of the 21 publication bundles, triggered by a spot-check of D9 — the
portfolio's only GREEN bundle — during a strategic review. Read-only; no remediation applied.

**Trigger.** The operator's response to a recommendation that named D9 as the
reference-implementation bundle: *"There's no way D9 is ready for publication, I doubt it even
meets standards for human in the loop review."* That was correct. This audit records why, and
why the readiness machinery said otherwise.

---

## The finding in one line

**Bundle readiness anti-correlates with review depth.** The measurement that certifies a bundle
ready is computed from findings, findings are minted by reviews, and the bundles with the least
review evidence therefore have the fewest findings and the best readiness verdicts.

| | non-RED bundles (5) | RED bundles (16) |
|---|---:|---:|
| mean sentences reviewed | **31** | **71** |
| mean open blockers | **0** | **17** |

The single GREEN bundle, **D9, has zero sentences reviewed.** The most-reviewed bundle,
**I1 at 290 sentences, is RED.**

This is *absence of measurement rendered as success* — the defect class the validation suite was
built to eliminate — reproduced one layer above the suite, in the readiness model itself.

---

## Documents

| file | contents |
|---|---|
| [`READINESS-SIGNAL-FAILURE.md`](READINESS-SIGNAL-FAILURE.md) | why GREEN means unreviewed; the field-ownership and enforcement gaps that permit it |
| [`D9-REFEREE-ASSESSMENT.md`](D9-REFEREE-ASSESSMENT.md) | per-blocker findings for D9, at referee granularity, with the reproduction for each |
| [`PROSE-QUALITY-BASELINE.md`](PROSE-QUALITY-BASELINE.md) | readability measured across all 21 drafts; the recency gradient; the absent control |

## Portfolio state at audit time

| | |
|---|---|
| bundles | 21 — **16 RED · 4 YELLOW · 1 GREEN** |
| open blockers | **265** (63% concentrated in six bundles) |
| open advisories | **629** |
| bundles with no `claims_review.json` | **2** — D6 (YELLOW), D9 (GREEN) |
| bundles with a 0-byte `audit_log.jsonl` | **5** — D6, D8, D9, D10, F |
| bundles with apex theorems declared (ADR-010) | **4 of 21** |
| Tier-1 aggregate vs charter (ADR-010, 2026-08-05) | **186 pp / 480 pp = 39%** |

## Relationship to ADR-010

ADR-010 diagnosed the volume pathology and named three generators: authorization has no content
floor (primary), `BUNDLE_LIFT_PROCEDURE` §3a stub padding, and no continuous gap measurement.
All three reproduce here.

This audit adds two findings ADR-010 does not cover:

1. **The readiness signal is not merely uninformative — it is inverted.** ADR-010 measured page
   counts against charters. It did not test whether the GREEN/YELLOW/RED verdict tracks quality.
   It does not.
2. **Nothing in the pipeline assesses whether prose serves a reader.** Zero validation checks,
   zero reviewer agents, and zero mentions in `WAVE_EXECUTION_PIPELINE.md`. Measured
   consequences are in `PROSE-QUALITY-BASELINE.md`.

Neither changes ADR-010's decisions. Both bear on the roster question it left open (§C3, §D4).
