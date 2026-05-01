# I2 Bundle — Stage 9 Figure Review (Round 2, Non-Stub)

**Bundle:** I2 — Verified statistical estimators + lean-tensor-categories
**Tier:** 3 (Infrastructure — JOSS | CPC)
**Reviewer agent:** `physics-qa:figure-reviewer`
**Run mode:** non-stub (5 figures authored since round 1)
**Review date (UTC):** 2026-05-01T20:35:00Z
**Phase / Sub-wave:** Phase 7a, sub-wave 7a.3 (I2 lift execution — figure-author follow-up)
**Round 1 reviewed:** 2026-05-01T14:00:56Z (stub-class; recommended I2-FIG-1..5)

---

## Verdict

`issues_found` (yellow). 4 of 5 figures pass with minor advisories; 1 figure (i2_fig5 mathlib upstream flow) FAILS rendering due to clipped node labels.

| Figure | Priority | Verdict |
|---|---|---|
| `i2_fig1_categorical_hierarchy.png` | P0 | **PASS** |
| `i2_fig2_module_dependencies.png` | P0 | **PASS** (1 minor advisory) |
| `i2_fig3_mtc_instances.png` | P1 | **PASS** (3 minor advisories: blank space; column-header copy-edit; missing VerifiedJackknife row — covered separately by fig 4) |
| `i2_fig4_jackknife_dependencies.png` | P1 | **PASS** (1 advisory: caption claims per-theorem test-annotation that figure does not visibly render) |
| `i2_fig5_mathlib_upstream_flow.png` | P2 | **FAIL** (rendering — node labels clipped beyond legibility) |

The two P0 figures (categorical hierarchy + module dependency) are publication-ready. The P1 figures (MTC table + VerifiedJackknife graph) are publication-ready with minor advisories. The P2 figure (Mathlib upstream flow) requires a rendering revision before JOSS submission.

## Anchors consulted (per `docs/agents/claims-reviewer-bundle-prompts.md` §I2)

1. VerifiedJackknife test suite cross-references (Phase 5c) — surfaced via fig 4
2. lean-tensor-categories Mathlib upstream cycle (Phase 5o Wave 4 + Wave 5) — surfaced via fig 5 (currently FAIL)

Bundle source: fresh-authored from Lean-module substrate per `PAPER_STRATEGY.md` §2.4 I2 outline (sourceless from `PAPER_DRAFT_MAPPING.md`). Stage-13 profile: software paper style — each function must trace to a passing test.

---

## Per-figure detailed review

### `i2_fig1_categorical_hierarchy.png` (P0) — PASS

- **Section anchor:** §3 line 308.
- **Type:** Hasse-diagram poset.
- **Rendering:** Clean. Nodes well-spaced, arrows visible, sans-serif typography legible.
- **Physics accuracy:** Correct two-route encoding (Balanced→Pivotal→Ribbon AND Fusion → ModularTensorData).
- **Style:** Two-band coloring (steel-blue Mathlib substrate vs amber library-original) implements round-1 I2-FIG-1 style note. Annotations "Library originals (this work)" and "Mathlib substrate" are clearly placed on the LHS. Colorblind-safe (no red/green pairing).
- **Caption match:** Yes (paper line 311-322).
- **Notes:** Minor — the round-1 I2-FIG-1 description listed `SphericalCategory` as a library-original tier; current figure omits it as a separate node (treated as part of the Pivotal/Ribbon chain in §3 prose). Optional strengthening; not load-bearing.

### `i2_fig2_module_dependencies.png` (P0) — PASS (with one minor advisory)

- **Section anchor:** §7 line 608.
- **Type:** Plotly Sankey (28 nodes; 4 architectural tiers).
- **Rendering:** Sankey labels render at small font; legible at 0.95\linewidth in single-column journal but borderline in two-column. **I2-FIGREV2-ADV-4.**
- **Physics accuracy:** Four-tier layering correct: amber instance modules (LHS) → berry Hopf-algebra modules (mid-left, Uqsl2Hopf, Uqsl2AffineHopf, Uqsl3Hopf, QuantumGroupHopf) → steel-blue number-field modules (mid-right, QCyc16, QSqrt2, QCyc5) → categorical-core modules (RHS, KLinearCategory, RibbonCategory, FusionCategory, SphericalCategory) plus peripheral number-fields (QSqrt5, QCyc5SqrtPhi, QCyc15, QCyc5Ext). Flow direction (instances → foundations) matches §7 prose.
- **Style:** Plotly Sankey; colorblind-safe palette respected.
- **Caption match:** Yes (paper line 611-621). 28-module count consistent with abstract.
- **Notes:** Round-1 I2-FIG-2 recommended VerifiedJackknife appear as a "disconnected island" so the abstract's "two pieces of independent infrastructure" claim is visualized in one figure. Current figure omits VerifiedJackknife — but fig 4 covers it independently, so this is a stylistic choice rather than a blocker.

### `i2_fig3_mtc_instances.png` (P1) — PASS (with cosmetic advisories)

- **Section anchor:** §6 line 510.
- **Type:** Plotly Table (8 instance rows × 7 columns).
- **Rendering:** Clean table render. Color-coded cells: steel-blue ✓ shipped / amber "partial" / grey ✗ not-yet-formalized.
- **Physics accuracy:**
  - SU(2)_k rank counts: 2, 3, 4, 5, 6 for k=1..5 (correct: rank = k+1).
  - SU(3)_2 rank 6 — correct.
  - Ising rank 3 — correct ({1, σ, ψ}).
  - Fibonacci rank 2 — correct ({1, τ}).
  - Quantum dimensions: SU(2)_3 (1, φ, φ, 1) — correct (golden-ratio dimensions emerge at k=3).
  - Number-fields per row consistent with §5 ComputableAdjoinRoot infrastructure: Q, Q(√2), Q(ζ_n), Q(√2, e^{iπ/8}), Q(ζ_5)[√φ].
- **Style:** Steel-blue / amber / grey palette per project conventions. **I2-FIGREV2-ADV-2:** ~70% of canvas height is blank below the table — wastes column inches; crop or tighten Plotly height.
- **Caption match:** Yes (paper line 513-522). **I2-FIGREV2-ADV-3:** column header reads "Verlinde verified" but caption uses phrasing "Verlinde-formula"; minor copy-edit.
- **Notes:** Round-1 I2-FIG-3 recommended adding a parallel VerifiedJackknife row "so both pieces of infrastructure are surveyed in one visual". Not incorporated; fig 4 covers VerifiedJackknife independently. Acceptable.

### `i2_fig4_jackknife_dependencies.png` (P1) — PASS (with one caption-vs-figure advisory)

- **Section anchor:** §2 line 249.
- **Type:** Two-tier dependency micro-graph (theorems above, lemmas below).
- **Rendering:** Clean. Legend in upper-right ("project theorem" amber / "Mathlib lemma" steel-blue / "project def" grey).
- **Physics accuracy:** Theorem→lemma reductions correct:
  - `jackknifeVariance_nonneg` → `mul_nonneg`, `Finset.sum_nonneg`, `sq_nonneg`
  - `autocovariance_zero_nonneg` → `Finset.sum_nonneg`, `sq_nonneg`, `mul_self_nonneg`
  - `intAutocorrTime_ge_half` → `Finset.sum_nonneg`, `mul_self_nonneg`
  - `intAutocorrTime_uncorrelated` → `autocovariance` (def)

  Theorem line ranges (50–58, 82–86, 109–114, 119–124) match §2 prose exactly.
- **Style:** Sage-green / amber / steel-blue palette per project conventions. Two-tier visual lanes match round-1 I2-FIG-4 style note.
- **Caption match:** **NO. I2-FIGREV2-ADV-1.** Caption (paper line 252-264) claims "each project theorem is annotated with the corresponding test function in tests/test_jackknife.py", but the figure does NOT visibly render test-name badges per node. Either:
  - (a) revise caption to drop the per-node-annotation claim and refer prose-readers to §2;
  - (b) re-author the figure with badges per theorem (what round-1 I2-ADV-2 anticipated).

  Option (a) is simpler; option (b) is what the round-1 advisory anticipated. Either is acceptable. Not load-bearing for figure structural content.

### `i2_fig5_mathlib_upstream_flow.png` (P2) — **FAIL** (rendering blocker)

- **Section anchor:** §7 line 689.
- **Type:** Process flow diagram (R-gates → PR chain → fallback diamond).
- **Rendering:** **CRITICAL.** Node labels are heavily clipped. Visible label fragments:
  - `athlib Zulip introd...`
  - `ool acceptance dis...`
  - `R strategy discus...`
  - `12 + Co putable...`
  - `alCateg ry + Ribb...`
  - `ularBial gebra + R...`
  - `tances (SU(2)..`
  - `software-only JOSS` and `update : etrofit upd...` (diamonds)

  The labels render INSIDE the squares/circles where the node shape is too small to contain the full text. The reader cannot determine which node is R1 vs R2 vs R3, nor identify which atomic PR is which (PR-1 QSqrt2 + ComputableAdjoinRoot, PR-2 PivotalCategory + RibbonCategory, PR-3 QuasitriangularBialgebra + RibbonHopfAlgebra, PR-4+ MTC instances).
- **Physics accuracy:** Despite the rendering bug, the structural flow is correct: 3 R-gates (steel-blue squares) → 4 PR nodes (amber circles) → diamond decision → 2 fallback nodes. Annotation "Fallback engages if Mathlib AI-content acceptance is delayed > 6 months" visible at the bottom and matches §7.4 prose.
- **Style:** Legend in upper-left correctly distinguishes R-gate / atomic PR / software-only fallback. Colorblind-safe palette respected. **The label-clipping is a rendering bug, not a style preference.**
- **Caption match:** Caption text (paper line 692-702) is accurate; the figure encodes the right structure but rendering renders the labels unreadable. Caption-figure semantic match is OK; the FAIL is purely rendering.
- **Remediation:** Re-author with one of:
  1. Larger nodes (~2× current size).
  2. Labels placed above/below the node shapes rather than inside.
  3. Abbreviated in-node labels (e.g. "R1", "R2", "R3", "PR-1"..."PR-4") plus a legend table mapping abbreviation → full description.
  4. Text-fitted rectangular shapes (instead of fixed-radius circles/squares).

  Re-invoke `physics-qa:figure-reviewer` with `bundle_target=I2` for verification once fixed.

---

## Style requirements (project-wide compliance check)

Per `CLAUDE.md` Key Conventions:

- **Plotly only** ✓ — All 5 figures appear to be Plotly-generated (Sankey for fig 2, Table for fig 3, scatter+line for figs 1/4/5).
- **Colorblind-accessible** ✓ — All figures use the project palette (steel-blue / amber / berry / sage-green / grey). No red/green pairing observed.
- **300 DPI minimum** — Cannot verify rasterization DPI from the PNGs alone; assumed-OK pending Plotly export-config check.

## Blockers

- **I2-FIGREV2-BLOCK-1:** `i2_fig5_mathlib_upstream_flow.png` — node labels clipped beyond legibility. Fix required before JOSS submission. See remediation list above.

## Advisories (5)

- **I2-FIGREV2-ADV-1.** `i2_fig4` caption claims per-theorem test annotation that figure does not show. Reconcile (caption edit OR figure re-author).
- **I2-FIGREV2-ADV-2.** `i2_fig3` Plotly Table has ~70% blank space below; crop.
- **I2-FIGREV2-ADV-3.** `i2_fig3` column header "Verlinde verified" vs caption phrasing "Verlinde-formula"; copy-edit.
- **I2-FIGREV2-ADV-4.** `i2_fig2` Sankey labels borderline in two-column layout; verify target journal layout.
- **I2-FIGREV2-ADV-5.** `i2_fig1` omits `SphericalCategory` as a separate node; optional strengthening (or update §3 prose to acknowledge).

## Round-1 → Round-2 Status of Recommendations

| Round-1 ID | Title | Round-2 status |
|---|---|---|
| I2-FIG-1 | Categorical hierarchy | **AUTHORED — PASS** |
| I2-FIG-2 | Module-dependency graph | **AUTHORED — PASS** (minor adv) |
| I2-FIG-3 | MTC instances comparison | **AUTHORED — PASS** (3 minor adv) |
| I2-FIG-4 | VerifiedJackknife dependency graph | **AUTHORED — PASS** (1 caption-mismatch adv) |
| I2-FIG-5 | Mathlib upstream R1/R2/R3 + atomic-PR flow | **AUTHORED — FAIL (rendering)** |

| Round-1 advisory | Round-2 status |
|---|---|
| I2-ADV-1 (P0 figures required) | **RESOLVED** — both P0 figs landed |
| I2-ADV-2 (caption ↔ test-name traceability for fig 4) | **PARTIAL** — caption claims annotation but figure has no badges; see I2-FIGREV2-ADV-1 |
| I2-ADV-3 (graphicx loaded but unused) | **RESOLVED** — graphicx now used by 5 `\includegraphics` calls |
| I2-ADV-4 (count-cite verification against `counts.json`) | **DEFERRED** — handle at Stage 13 final formatting |

## Next actions

1. **REQUIRED:** Re-author `papers/I2/figures/i2_fig5_mathlib_upstream_flow.png` to fix label clipping; re-invoke `physics-qa:figure-reviewer` with `bundle_target=I2` for verification.
2. Reconcile `i2_fig4` caption with figure (caption edit drops per-theorem-annotation claim, OR re-author figure with test-name badges).
3. Optional cleanup: crop fig 3 vertical extent; rename fig 3 column header for caption-consistency; add SphericalCategory node to fig 1.
4. Once fig 5 fixed, expect overall_status to upgrade from `issues_found` to `pass` and bundle metadata `stage9_status` from `yellow` to `green`.

---

*JSON sibling artifact:* `papers/I2/figures/figure_review_report.json`
*Round-1 review (stub-class):* this file at 2026-05-01T14:00:56Z (overwritten)
