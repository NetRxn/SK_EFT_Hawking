# Open required findings baseline

On 2026-11-22 the operator authorized freezing the remaining required finding population at its measured level to restore the test baseline while substantive research continues separately. The measurement uses the [canonical graph aggregation](../../../scripts/validation/checks/bundles_readiness.py) at `9fe5a93a1cd948150a3401888206534e7ebab77b`. The [exact snapshot](REQUIRED_FINDINGS_BASELINE_2026-11-22.json) records the previous and measured ceilings and every open finding behind each adjustment. No finding transitions or publication gates were changed. Ordinary no-growth checks and zero headroom apply immediately to this baseline. Lower each ceiling with accepted closures.

| Bundle | Previous ceiling | Measured ceiling |
|---|---:|---:|
| D1 | 2 | 10 |
| D2 | 3 | 7 |
| D3 | 1 | 10 |
| D4 | 4 | 9 |
| D8 | 0 | 5 |
| F | 10 | 9 |
| L2 | 2 | 12 |
| L3 | 0 | 3 |

F tightens after the already accepted closure of `review:2026-04-10:CitationReview-01:8` in [PR #188](https://github.com/NetRxn/SK_EFT_Hawking/pull/188). The prior integration left this bundle with headroom.

## Substantive work to retain

- **D1** still needs source-backed dispersion and noise, physical bounds and calibration, and independent derivations wherever the original claims require them. Source and metadata scope repairs in [PR #91](https://github.com/NetRxn/SK_EFT_Hawking/pull/91) cover a narrower acceptance boundary.
- **D2 and L2** can reuse finite free-Hom finrank, finite exactness, the sided module complex and finite dual cohomology. The full change-of-rings comparison, categorical Ext through degree five including the next differential, and genuine Pin+ anomaly identification remain distinct obligations. See the [Ext substantiation roadmap](../../roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md).
- **D3** needs the manuscript's curvature coefficients and scale conventions reconciled with the actual Lean and computational statements. Broader gravitational identification remains a separate scientific obligation.
- **D4** needs a statement-by-statement reconciliation of the categorical and QEC claims with stronger existing substrate, including the scope of the modular matrices and theorem dependencies.
- **D8** has constructive headline bounds. Remaining findings need adjudication against those actual statements and the primary-source and manuscript evidence. The current inventory supplies the original IDs and review sources.
- **L3** needs integration of already reviewed profile and geometric work where applicable, followed by the physical four-laws and regime-partition derivations. [Profile checkpoint](https://github.com/NetRxn/SK_EFT_Hawking/pull/112) · [Geometry checkpoint](https://github.com/NetRxn/SK_EFT_Hawking/pull/114)

The snapshot covers adjusted ceilings. The canonical graph and closure ledger continue to track the full open population, including findings outside these bundles.
