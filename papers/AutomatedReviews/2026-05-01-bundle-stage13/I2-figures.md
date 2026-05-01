# I2 Bundle — Stage 9 Figure Review (Round 3, Non-Stub)

**Bundle:** I2 — Verified statistical estimators + lean-tensor-categories
**Tier:** 3 (Infrastructure — JOSS | CPC)
**Reviewer agent:** `physics-qa:figure-reviewer`
**Run mode:** non-stub (5 figures; round-3 verification of round-2 BLOCKER + 1 advisory remediation)
**Review date (UTC):** 2026-05-01T21:05:00Z
**Phase / Sub-wave:** Phase 7a, sub-wave 7a.3 (I2 lift execution — round-3 figure verification)
**Round 1 reviewed:** 2026-05-01T14:00:56Z (stub-class; recommended I2-FIG-1..5)
**Round 2 reviewed:** 2026-05-01T20:35:00Z (5 figs authored; 4/5 PASS; 1 FAIL on i2_fig5 rendering)

---

## Verdict

`pass` (green). All 5 figures PASS. The round-2 BLOCKER is RESOLVED; one round-2 advisory is RESOLVED via caption edit; the remaining 4 advisories are cosmetic and deferred to pre-press finalization.

| Figure | Round-2 verdict | Round-3 verdict |
|---|---|---|
| `i2_fig1_categorical_hierarchy.png` | PASS | **PASS** (unchanged) |
| `i2_fig2_module_dependencies.png` | PASS w/ adv | **PASS** (ADV-4 deferred) |
| `i2_fig3_mtc_instances.png` | PASS w/ 3 adv | **PASS** (ADV-2, ADV-3 deferred) |
| `i2_fig4_jackknife_dependencies.png` | PASS w/ 1 caption adv | **PASS** (ADV-1 RESOLVED) |
| `i2_fig5_mathlib_upstream_flow.png` | **FAIL** (rendering) | **PASS** (re-authored + render-bug fix) |

The two P0 figures (categorical hierarchy + module dependency) remain publication-ready. The P1 figures (MTC table + VerifiedJackknife graph) are publication-ready; fig 4's caption-vs-figure mismatch is reconciled. The P2 figure (Mathlib upstream flow) is now publication-ready.

## Anchors consulted (per `docs/agents/claims-reviewer-bundle-prompts.md` §I2)

1. VerifiedJackknife test suite cross-references (Phase 5c) — surfaced via fig 4
2. lean-tensor-categories Mathlib upstream cycle (Phase 5o Wave 4 + Wave 5) — surfaced via fig 5 (now PASSING)

Bundle source: fresh-authored from Lean-module substrate per `PAPER_STRATEGY.md` §2.4 I2 outline (sourceless from `PAPER_DRAFT_MAPPING.md`). Stage-13 profile: software paper style — each function must trace to a passing test.

---

## Per-figure detailed review (round 3)

### `i2_fig1_categorical_hierarchy.png` (P0) — PASS

- **Status:** Unchanged from round 2. Hasse-diagram poset; correct two-route encoding (Balanced→Pivotal→Ribbon AND Fusion→ModularTensorData). Two-band coloring (steel-blue Mathlib substrate / amber library-original) matches project conventions.
- **ADV-5** (omitted SphericalCategory node) — deferred to optional pre-press strengthening.

### `i2_fig2_module_dependencies.png` (P0) — PASS

- **Status:** Unchanged from round 2. Plotly Sankey, 28 nodes, 4 architectural tiers (instances → Hopf → number-fields → categorical core). Flow direction (instances → foundations) matches §7 prose.
- **ADV-4** (Sankey label legibility in two-column layouts) — deferred. JOSS primary target is single-column so non-blocking; if CPC two-column variant is later pursued, font-size bump or split into two sub-figures.

### `i2_fig3_mtc_instances.png` (P1) — PASS

- **Status:** Unchanged from round 2. Plotly Table, 8 instance rows × 7 columns; physics entries (rank, q-dimensions, number-field column) verified.
- **ADV-2** (~70% blank canvas below table) — deferred. Cosmetic, pre-press crop.
- **ADV-3** ('Verlinde verified' header vs 'Verlinde-formula' caption) — deferred. One-token copy-edit at pre-press.

### `i2_fig4_jackknife_dependencies.png` (P1) — PASS (caption fix verified)

- **Status:** Figure unchanged; **caption fixed**. Caption now reads (paper around line 269):
  > "...Each project theorem has a corresponding test in `tests/test_verified_statistics.py` that exercises its numerical instantiation; the test names are listed in the prose (Section `sec:jackknife`) rather than overlaid on each node to keep the dependency graph readable."

  This drops the round-2 claim of per-node test-name annotations. The figure now matches the caption exactly.
- **I2-FIGREV2-ADV-1 RESOLVED.**

### `i2_fig5_mathlib_upstream_flow.png` (P2) — **PASS** (round-2 BLOCKER resolved)

- **Section anchor:** §7 line 689.
- **Type:** Process flow diagram — 3 R-gates → 4 PR chain → fallback rail.
- **Round-3 rendering verification:** All node labels are bold white, fully legible inside text-fitted rectangles. Specifically:
  - **Upper rail:** R1, R2, R3 (steel-blue) → PR-1, PR-2, PR-3, PR-4+ (amber), connected by colored arrows.
  - **Lower rail:** F1, F2 (cool-grey) connected by horizontal arrow; R3 → F1 vertical fallback arrow.
  - **Top-right kind legend:** distinguishes R-gate (relationship-building) / atomic Mathlib PR / software-only fallback.
  - **Bottom side-table legend (two columns):**
    - R1 = Mathlib Zulip introduction
    - R2 = AI-tool-assistance disclosure
    - R3 = PR-strategy discussion
    - PR-1 = QSqrt2 + ComputableAdjoinRoot bridge
    - PR-2 = PivotalCategory + RibbonCategory
    - PR-3 = QuasitriangularBialgebra + RibbonHopfAlgebra
    - PR-4+ = MTC instances (SU(2)_k, Ising, Fibonacci)
    - F1 = Software-only release (JOSS, this paper)
    - F2 = JOSS update (retrofit upstream PRs)
    - *Italic footer:* "Fallback if Mathlib AI-content acceptance > 6 mo"
- **Title:** "Mathlib upstream coordination: R1/R2/R3 gates → atomic-PR chain"
- **Subtitle:** "Steel-blue gates → amber PR sequence; cool-grey fallback for software-only release (paper I2 §7)."
- **Physics accuracy:** Correct (preserved from round 2). Three R-gates → four atomic-PR sequence → fallback diamond logic. The §7.4 prose anchor ("Fallback engages if Mathlib AI-content acceptance is delayed > 6 months") is reproduced as the side-table italic footer.
- **Style:** Colorblind-safe palette respected (steel-blue / amber / cool-grey). CMU Serif typography consistent with project conventions. Bold white in-node labels readable against all three fill colors.
- **Caption match:** Yes (paper line 692-702).
- **I2-FIGREV2-BLOCK-1 RESOLVED.**

#### Side note: render-bug fix during round-3 verification

When the round-3 reviewer first inspected `papers/I2/figures/i2_fig5_mathlib_upstream_flow.png`, the saved PNG showed the *old* round-2 long-label clipped layout despite the source function having been correctly rewritten in `src/core/visualizations.py::fig_i2_mathlib_upstream_flow`. Investigation surfaced a `kaleido._kaleido_tab.KaleidoError: Error 525: plotly.js error` triggered by the `&rarr;` HTML entity in the figure title; the figure-author session's `write_image` call had silently failed and left the previous PNG in place. Round-3 substituted the Unicode arrow character `→` for `&rarr;` in the title, re-rendered the PNG cleanly, and verified the fixed image. The fix is committed in `src/core/visualizations.py` lines around 14087-14091.

---

## Style requirements (project-wide compliance check)

Per `CLAUDE.md` Key Conventions:

- **Plotly only** ✓ — all 5 figures Plotly-generated.
- **Colorblind-accessible** ✓ — project palette throughout (steel-blue / amber / berry / sage-green / cool-grey); no red/green pairing.
- **300 DPI minimum** — fig 5 written at scale=2 (1200×800 base ⇒ 2400×1600 pixel raster); other 4 figures unchanged from round 2.

## Blockers (0)

All round-2 blockers resolved.

## Advisories (4 deferred)

| ID | Figure | Status | Defer reason |
|---|---|---|---|
| I2-FIGREV2-ADV-2 | i2_fig3 | deferred (cosmetic) | ~70% canvas blank below table; pre-press crop |
| I2-FIGREV2-ADV-3 | i2_fig3 | deferred (cosmetic) | 'Verlinde verified' vs 'Verlinde-formula' one-token copy-edit |
| I2-FIGREV2-ADV-4 | i2_fig2 | deferred (journal layout dependent) | Sankey label legibility in two-column; JOSS single-column unaffected |
| I2-FIGREV2-ADV-5 | i2_fig1 | deferred (optional) | SphericalCategory not shown as separate node |

## Round-2 → Round-3 Status of Findings

| Round-2 ID | Title | Round-3 status |
|---|---|---|
| I2-FIGREV2-BLOCK-1 | i2_fig5 node labels clipped | **RESOLVED** (re-author + render-bug fix) |
| I2-FIGREV2-ADV-1 | i2_fig4 caption ↔ figure mismatch | **RESOLVED** (caption edited) |
| I2-FIGREV2-ADV-2 | i2_fig3 blank space below table | DEFERRED (cosmetic) |
| I2-FIGREV2-ADV-3 | i2_fig3 'Verlinde verified' copy-edit | DEFERRED (cosmetic) |
| I2-FIGREV2-ADV-4 | i2_fig2 Sankey two-column legibility | DEFERRED (journal layout) |
| I2-FIGREV2-ADV-5 | i2_fig1 SphericalCategory node | DEFERRED (optional) |

## Next actions

1. **Bundle stage9_status upgrades from `yellow` to `green`.** No remaining figure blockers.
2. Stage 10 claims-reviewer round-2 status (currently `red`) is orthogonal to figure review and does not block this stage's promotion.
3. Pre-press finalization should address the four deferred cosmetic advisories (ADV-2, ADV-3, ADV-4, ADV-5) before final journal submission, but none block bundle progression.

---

*JSON sibling artifact:* `papers/I2/figures/figure_review_report.json`
*Round-2 review:* this file at 2026-05-01T20:35:00Z (overwritten)
*Round-1 review (stub-class):* this file at 2026-05-01T14:00:56Z (overwritten)
