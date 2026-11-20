# Remaining canonical table migration

Author package for exact PR118 draft `ddc320ec365a1f42fd5d8d81796ae07bc0bb029c`.
Intake and terminal continuity both returned `SAME`. Every write was in scratch.
Both patches pass `git apply --check` against the pinned clean draft. No checker,
renderer, ceiling, paper metadata, PDF, unrelated generated table or infrastructure
change is part of either patch.

## Source and scientific preservation

The full patch changes 23 paths. It replaces the eleven handwritten tabular
bodies with canonical inputs, adds six `tables.py` specs and includes the eleven
outputs. D1's hierarchy input is `tables/platform_hierarchy.tex`.
The differential checks all 36 headings and 108 data rows (340 cells). The
column formats and every byte outside the replaced table bodies are exact.
Comparison normalizes LaTeX-insignificant whitespace and separates rule/spacing
tokens, which are recorded per table in `evidence/cell-differential.json`.

- D1 BEC cells use the pinned `compute_bec_hierarchy` and `fmt_sci_latex`
  functions. Direct evaluation reproduced all three rows, including precision,
  nominal-temperature labels and the dominance classification. Non-BEC orientation
  estimates retain the baseline values and emphasis.
- D2 charge inputs come from `SM_FERMION_DATA`. They are represented as exact
  sixth-integers with a fail-closed reconstruction check. The `ours` coefficient
  constants are read from `SM_Z4_CHARGE_FORMULA`, the GEM column uses the draft's
  rescaled Eq. (gem-standard), and the last column is the exact difference.
  Direct examination of the held García-Etxebarria--Montero PDF, Eq. (4.13)
  and Table 2, matches the six GEM charges. Source SHA-256
  `724adbe18e082ed5eeac2dcd380b850e18f75e2e6855c2515dd22e0cce0bb237`.
- D6 preserves the five source-reported count values and their approximation
  marks. The source function calculates each reciprocal to the existing three
  significant figures. Direct examination of the held AGP PDF confirmed the
  counts in Sec. 8.3 and the depolarizing example. Source SHA-256
  `2df9a42e5094dac7bfc8356ceacd6e1ca9b777d7458efa75cc5120c0031fedea`.
- The remaining tables retain the exact proof-status grades, references,
  labels, qualifiers, deliberate blank cells and emphasis. No scientific
  scope or claim changes are bundled into this migration.

Two whole-corpus canonical renders reproduce byte-identical table output
manifests. All pre-existing table outputs retain their original bytes.
The unchanged canonical freshness check passes with 96 outputs across 20
specs on the all-eleven candidate. The baseline stale-artifact retest
regenerated its scratch artifacts and passed with the same held source index.

## Gate differential

| Check | Exact baseline | All 11 migrated | Ten-table control |
| --- | --- | --- | --- |
| `bundle_tables_use_pipeline` | Fail, 11 handwritten in six bundles | Pass, 0 handwritten | Pass, one handwritten |
| `d1_hierarchy_table` | Pass | Fail, inline tabular not found | Pass |
| `tables_fresh` | Pass | Pass | Pass |
| `bundle_manuscript_length` | Pass | Pass | Pass |
| `bundle_prose_em_dash_free` | Fail | Fail, counts unchanged | Fail, counts unchanged |
| `bundle_reader_facing_voice` | Fail | Fail, identical detail | Fail, identical detail |

The portfolio denominator is 21 and the ceiling remains one. The all-eleven
gate emits the normal below-ceiling advice. The ten-table control keeps only
the numerical D1 hierarchy table inline and preserves all other migration
files. It is an intermediate control for the reader dependency.

The numerical reader reads raw D1 draft text and searches for a tabular after
its hierarchy label. It cannot see the generated file. The author package
does not change the reader or the check's three BEC-row/crossover tolerance.

The theorem-reference reader also scans raw draft text. On the retained
committed index and identical project Lean source, the unchanged
`prose_theorem_reference_coverage` check drops from 1,418 to 1,386 bundle
candidates for both controls. It retains one inherited unresolved D10
reference, two drift advisories, one waiver, and the same legacy outcome
(94 unresolved versus ceiling 90 in this archived project-source context).
The affected-bundle differential uses the same extractor and resolver:

| Bundle | Resolved unique baseline → all 11 | Resolved occurrences baseline → all 11 |
| --- | ---: | ---: |
| D1 | 156 → 133 | 185 → 141 |
| D2 | 110 → 110 | 132 → 132 |
| D4 | 2 → 2 | 4 → 4 |
| D6 | 24 → 22 | 27 → 25 |
| D9 | 151 → 144 | 181 → 170 |
| D10 | 65 → 65 | 74 → 67 |

The reader loses 32 unique resolved names and 64 resolved occurrences,
including 32 repeated occurrences. The exact name/occurrence delta is in
`evidence/prose-reference-differential.json`. A separate bounded control
reads the existing `draft_input_closure`, combines its TeX text with the
draft's preamble, and recovers the exact verbatim-token multiset of every
affected bundle. Scanning snippets in isolation would miss D9's
preamble-defined `\lean` alias. This control supplies evidence for the
reader repair, without changing the production checker.

## Compile and render

The baseline and both variants compile all six bundles through the pinned
compiler. D1, D2, D4, D6, D9 and D10 retain respectively 20, 18, 30, 8, 14
and 9 pages. They have zero TeX errors, zero unresolved PDF references and
zero dropped class options. The pre-existing overfull counts (15, 5, 2, 3,
9 and 4) and individual box dimensions match in all three runs.
Named PDF destinations are preserved across all six comparisons.

Actual candidate raster differences by page were D1 11–20, D2 1–2 and 4,
D4 5, D6 6 and 8, D9 4–5 and 12, and D10 3–4. Each table stays on the same
page and in the same column as its baseline table. I visually inspected the
eleven paired table views. Standard renderer top and bottom rules and the
heading rules change in the output. The two last D9 exact-distance rows keep
their bracket/lower-bound notation and caption exception, while the internal
divider is absent because the current renderer has no per-row rule setting.
D10's four 2 pt inter-group spacings are absent for the same API reason, with
indentation, group order and blank cells intact.

D1's status table overlaps the adjacent bibliography on page 20 in both
renders. D4's trust-grade table clips the two longest descriptions at the
page edge in both renders on page 5. These are inherited layout obligations
visible even though the canonical compile gate passes. The patch preserves
the old column specification and exposes those defects for separate review.

This scratch package is ready for independent review of source and actual
renders. A qualification decision still requires the D1 numerical reader and
the theorem-reference reader to retain full coverage of the generated source,
alongside the existing portfolio and bundle gates. No readiness or stage
promotion is claimed.
